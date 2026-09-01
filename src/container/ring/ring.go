// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// +gobra

// Package ring implements operations on circular lists.
package ring

// A Ring is an element of a circular list, or ring.
// Rings do not have a beginning or end; a pointer to any ring element
// serves as reference to the entire ring. Empty rings are represented
// as nil Ring pointers. The zero value for a Ring is a one-element
// ring with a nil Value.
//
type Ring struct {
	next, prev *Ring
	Value      any // for use by client; untouched by this library
}

// init links r to itself. It is the lazy initialization of the zero Ring
// value, which the doc comment of Ring declares to be a one-element ring.
// @ requires acc(r)
// @ ensures  acc(r) && ret == r
// @ ensures  r.next == r && r.prev == r
// @ ensures  r.Value === old(r.Value)
// @ decreases
func (r *Ring) init() (ret *Ring) {
	r.next = r
	r.prev = r
	return r
}

// Next returns the next ring element. r must not be empty.
// @ requires  Mem(rs, vs)
// @ requires  0 <= i && i < len(rs) && rs[i] == r
// @ ensures   Mem(rs, vs) && IsInit(rs, vs)
// @ ensures   ret == rs[i+1 < len(rs) ? i+1 : 0]
// @ decreases
func (r *Ring) Next( /*@ ghost rs seq[*Ring], ghost vs seq[any], ghost i int @*/ ) (ret *Ring) {
	//@ unfold Mem(rs, vs)
	// In a ring of more than one element every next pointer is set, so a nil
	// next can only be the lazily initialized zero value.
	//@ assert len(rs) > 1 ==> rs[0].next == rs[1] && rs[1] != nil
	//@ assert len(rs) > 1 && i < len(rs)-1 ==> rs[i].next == rs[i+1] && rs[i+1] != nil
	//@ assert len(rs) > 1 && i == len(rs)-1 ==> rs[i].next == rs[0] && rs[0] != nil
	if r.next == nil {
		//@ assert len(rs) == 1 && i == 0
		res := r.init()
		//@ fold Mem(rs, vs)
		return res
	}
	res := r.next
	//@ assert i == len(rs)-1 ==> res == rs[0]
	//@ fold Mem(rs, vs)
	return res
}

// Prev returns the previous ring element. r must not be empty.
// @ requires  Mem(rs, vs)
// @ requires  0 <= i && i < len(rs) && rs[i] == r
// @ ensures   Mem(rs, vs) && IsInit(rs, vs)
// @ ensures   ret == rs[i > 0 ? i-1 : len(rs)-1]
// @ decreases
func (r *Ring) Prev( /*@ ghost rs seq[*Ring], ghost vs seq[any], ghost i int @*/ ) (ret *Ring) {
	//@ unfold Mem(rs, vs)
	//@ assert len(rs) > 1 ==> rs[0].next == rs[1] && rs[1] != nil
	//@ assert len(rs) > 1 && i < len(rs)-1 ==> rs[i].next == rs[i+1] && rs[i+1] != nil
	//@ assert len(rs) > 1 && i == len(rs)-1 ==> rs[i].next == rs[0] && rs[0] != nil
	if r.next == nil {
		//@ assert len(rs) == 1 && i == 0
		res := r.init()
		//@ fold Mem(rs, vs)
		return res
	}
	//@ assert i > 0 ==> rs[i].prev == rs[i-1]
	res := r.prev
	//@ fold Mem(rs, vs)
	return res
}

// Move moves n % r.Len() elements backward (n < 0) or forward (n >= 0)
// in the ring and returns that ring element. r must not be empty.
//
// @ requires  Mem(rs, vs)
// @ requires  0 <= i && i < len(rs) && rs[i] == r
// @ ensures   Mem(rs, vs) && IsInit(rs, vs)
// @ ensures   ret == rs[Wrap(i+old(n), len(rs))]
// @ decreases
func (r *Ring) Move(n int /*@, ghost rs seq[*Ring], ghost vs seq[any], ghost i int @*/) (ret *Ring) {
	//@ ghost m := len(rs)
	//@ ghost n0 := n
	//@ ghost idx := i
	//@ unfold Mem(rs, vs)
	//@ assert m > 1 ==> rs[0].next == rs[1] && rs[1] != nil
	//@ assert m > 1 && i < m-1 ==> rs[i].next == rs[i+1] && rs[i+1] != nil
	//@ assert m > 1 && i == m-1 ==> rs[i].next == rs[0] && rs[0] != nil
	if r.next == nil {
		//@ assert m == 1 && i == 0
		res := r.init()
		//@ fold Mem(rs, vs)
		//@ assert Wrap(i+n0, m) == 0
		return res
	}
	//@ fold Mem(rs, vs)
	switch {
	case n < 0:
		//@ invariant Mem(rs, vs)
		//@ invariant IsInit(rs, vs)
		//@ invariant 0 <= idx && idx < m && r == rs[idx]
		//@ invariant n <= 0
		//@ invariant Step(idx, n, m) == Step(i, n0, m)
		//@ decreases -n
		for ; n < 0; n++ {
			//@ ghost idx2 := idx == 0 ? m-1 : idx-1
			//@ unfold Mem(rs, vs)
			//@ assert idx > 0 ==> rs[idx].prev == rs[idx-1]
			//@ assert idx == 0 ==> rs[0].prev == rs[m-1]
			r = r.prev
			//@ fold Mem(rs, vs)
			//@ idx = idx2
		}
	case n > 0:
		//@ invariant Mem(rs, vs)
		//@ invariant IsInit(rs, vs)
		//@ invariant 0 <= idx && idx < m && r == rs[idx]
		//@ invariant n >= 0
		//@ invariant Step(idx, n, m) == Step(i, n0, m)
		//@ decreases n
		for ; n > 0; n-- {
			//@ ghost idx2 := idx+1 == m ? 0 : idx+1
			//@ unfold Mem(rs, vs)
			//@ assert idx < m-1 ==> rs[idx].next == rs[idx+1]
			//@ assert idx == m-1 ==> rs[idx].next == rs[0]
			r = r.next
			//@ fold Mem(rs, vs)
			//@ idx = idx2
		}
	}
	//@ assert Step(idx, n, m) == idx
	//@ StepIsWrap(i, n0, m)
	return r
}

// New creates a ring of n elements.
// @ ensures   n <= 0 ==> ret == nil && len(rs) == 0 && len(vs) == 0
// @ ensures   n > 0 ==> ret != nil && Mem(rs, vs) && len(rs) == n && rs[0] == ret
// @ ensures   n > 0 ==> IsInit(rs, vs)
// @ ensures   n > 0 ==> (forall k int :: {vs[k]} 0 <= k && k < len(vs) ==> vs[k] == nil)
// @ decreases
func New(n int) ( /*@ ghost rs seq[*Ring], ghost vs seq[any], @*/ ret *Ring) {
	if n <= 0 {
		return /*@ seq[*Ring]{}, seq[any]{}, @*/ nil
	}
	r := new(Ring)
	p := r
	// Gobra cannot type a bare nil inside a seq[any] literal, so the (nil)
	// value of the freshly allocated element is read out of the element
	// itself.
	//@ rs = seq[*Ring]{r}
	//@ vs = seq[any]{r.Value}

	//@ invariant 1 <= i && i <= n
	//@ invariant len(rs) == i && len(vs) == i
	//@ invariant rs[0] == r && rs[i-1] == p
	//@ invariant forall k int :: {rs[k]} 0 <= k && k < len(rs) ==> acc(rs[k]) && rs[k] != nil && rs[k].Value === vs[k]
	//@ invariant forall k, l int :: {rs[k], rs[l]} 0 <= k && k < len(rs) && 0 <= l && l < len(rs) ==> (rs[k] == rs[l] ==> k == l) && (l == k+1 ==> rs[k].next == rs[l] && rs[l].prev == rs[k])
	//@ invariant rs[0].prev == nil && rs[i-1].next == nil
	//@ invariant forall k int :: {vs[k]} 0 <= k && k < len(vs) ==> vs[k] == nil
	//@ decreases n - i
	for i := 1; i < n; i++ {
		p.next = &Ring{prev: p}
		p = p.next
		//@ rs = rs ++ seq[*Ring]{p}
		//@ vs = vs ++ seq[any]{p.Value}
	}
	//@ assert len(rs) == n && rs[0] == r && rs[len(rs)-1] == p
	p.next = r
	r.prev = p
	// Closing the ring makes every next pointer non-nil, so the ring is
	// initialized rather than a lazily initialized zero value. For n == 1 the
	// single element is linked to itself.
	//@ assert len(rs) > 1 ==> rs[0].next == rs[1] && rs[1] != nil
	//@ assert len(rs) == 1 ==> rs[0] == p && rs[0].next == rs[0] && rs[0] != nil
	//@ assert rs[0].next != nil
	//@ fold Mem(rs, vs)
	return /*@ rs, vs, @*/ r
}

// Link connects ring r with ring s such that r.Next()
// becomes s and returns the original value for r.Next().
// r must not be empty.
//
// If r and s point to the same ring, linking
// them removes the elements between r and s from the ring.
// The removed elements form a subring and the result is a
// reference to that subring (if no elements were removed,
// the result is still the original value for r.Next(),
// and not nil).
//
// If r and s point to different rings, linking
// them creates a single ring with the elements of s inserted
// after r. The result points to the element following the
// last element of s after insertion.
//
// @ trusted
// @ requires false
func (r *Ring) Link(s *Ring) *Ring {
	n := r.Next()
	if s != nil {
		p := s.Prev()
		// Note: Cannot use multiple assignment because
		// evaluation order of LHS is not specified.
		r.next = s
		s.prev = r
		n.prev = p
		p.next = n
	}
	return n
}

// Unlink removes n % r.Len() elements from the ring r, starting
// at r.Next(). If n % r.Len() == 0, r remains unchanged.
// The result is the removed subring. r must not be empty.
//
// @ trusted
// @ requires false
func (r *Ring) Unlink(n int) *Ring {
	if n <= 0 {
		return nil
	}
	return r.Link(r.Move(n + 1))
}

// Len computes the number of elements in ring r.
// It executes in time proportional to the number of elements.
//
// @ requires  r != nil ==> Mem(rs, vs)
// @ requires  r != nil ==> 0 <= i && i < len(rs) && rs[i] == r
// @ requires  r == nil ==> len(rs) == 0
// @ ensures   r != nil ==> Mem(rs, vs) && IsInit(rs, vs)
// @ ensures   res == len(rs)
// @ decreases
func (r *Ring) Len( /*@ ghost rs seq[*Ring], ghost vs seq[any], ghost i int @*/ ) (res int) {
	n := 0
	if r != nil {
		n = 1
		//@ ghost m := len(rs)
		//@ invariant Mem(rs, vs)
		//@ invariant IsInit(rs, vs)
		//@ invariant 1 <= n && n <= m
		//@ invariant p == rs[i+n < m ? i+n : i+n-m]
		//@ decreases m - n
		for p := r.Next( /*@ rs, vs, i @*/ ); p != r; p = /*@ unfolding Mem(rs, vs) in @*/ p.next {
			//@ assert n < m
			n++
			//@ ghost q := i+n-1 < m ? i+n-1 : i+n-1-m
			//@ ghost q2 := i+n < m ? i+n : i+n-m
			//@ unfold Mem(rs, vs)
			//@ assert q < m-1 ==> rs[q].next == rs[q+1]
			//@ assert q == m-1 ==> rs[q].next == rs[0]
			//@ fold Mem(rs, vs)
			//@ assert (unfolding Mem(rs, vs) in p.next) == rs[q2]
		}
		//@ unfold Mem(rs, vs)
		//@ assert rs[i+n < m ? i+n : i+n-m] == rs[i]
		//@ fold Mem(rs, vs)
	}
	return n
}

// Do calls function f on each element of the ring, in forward order.
// The behavior of Do is undefined if f changes *r.
// @ trusted
// @ requires false
func (r *Ring) Do(f func(any)) {
	if r != nil {
		f(r.Value)
		for p := r.Next(); p != r; p = p.next {
			f(p.Value)
		}
	}
}
