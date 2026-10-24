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
// @ preserves acc(r)
// @ ensures   ret == r
// @ ensures   r.next == r && r.prev == r
// @ ensures   r.Value === old(r.Value)
// @ decreases
func (r *Ring) init() (ret *Ring) {
	r.next = r
	r.prev = r
	return r
}

// Next returns the next ring element. r must not be empty.
// @ preserves Mem(rs, vs)
// @ requires  0 <= i && i < len(rs) && rs[i] == r
// @ ensures   IsInit(rs, vs)
// @ ensures   ret == rs[i+1 < len(rs) ? i+1 : 0] && ret != nil
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
// @ preserves Mem(rs, vs)
// @ requires  0 <= i && i < len(rs) && rs[i] == r
// @ ensures   IsInit(rs, vs)
// @ ensures   ret == rs[i > 0 ? i-1 : len(rs)-1] && ret != nil
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
// Note on n: the loops below drive the parameter itself to zero, so the n of
// the postcondition is the argument as passed (Gobra reads a parameter in a
// postcondition in the pre-state), while the n of the loop invariants is the
// steps still to take. n0 holds the entry value for the invariants.
// @ preserves Mem(rs, vs)
// @ requires  0 <= i && i < len(rs) && rs[i] == r
// @ ensures   IsInit(rs, vs)
// @ ensures   ret == rs[Wrap(i+n, len(rs))] && ret != nil
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
		//@ invariant step(idx, n, m) == step(i, n0, m)
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
		//@ invariant step(idx, n, m) == step(i, n0, m)
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
	//@ assert step(idx, n, m) == idx
	//@ stepIsWrap(i, n0, m)
	return r
}

// New creates a ring of n elements.
// @ ensures   n <= 0 ==> ret == nil && len(rs) == 0 && len(vs) == 0
// @ ensures   n > 0 ==> ret != nil && Mem(rs, vs) && len(rs) == n && len(vs) == n && rs[0] == ret
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
	// The elements are pairwise distinct. This conjunct needs no permission, and
	// it has to come before the quantified permission below: Silicon consumes
	// invariant conjuncts left to right, and re-inhaling that permission for the
	// extended sequence is exactly what needs the injectivity of k |-> rs[k].
	//@ invariant forall k, l int :: {rs[k], rs[l]} 0 <= k && k < len(rs) && 0 <= l && l < len(rs) && rs[k] == rs[l] ==> k == l
	//@ invariant forall k int :: {rs[k]} 0 <= k && k < len(rs) ==> acc(rs[k]) && rs[k] != nil && rs[k].Value === vs[k]
	//@ invariant forall k, l int :: {rs[k], rs[l]} 0 <= k && k < len(rs) && 0 <= l && l < len(rs) && l == k+1 ==> rs[k].next == rs[l] && rs[l].prev == rs[k]
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
// The ghost arguments carry the decomposition the result is phrased in: ts is
// rs without its first element r, and ss is the ring s belongs to. Requiring
// Mem(ss, ws) is what restricts this contract to the different-ring case --
// no client can produce a second Mem for elements it already owns through
// Mem(rs, vs) -- so the same-ring case of the doc comment above is excluded
// here rather than proved. See gobra-status.md.
// @ requires  Mem(rs, vs) && 0 < len(rs) && rs[0] == r
// @ requires  rs == seq[*Ring]{r} ++ ts && vs == seq[any]{v0} ++ tvs
// @ requires  s != nil ==> Mem(ss, ws) && 0 < len(ss) && ss[0] == s
// @ ensures   ret == (len(ts) > 0 ? ts[0] : r) && ret != nil
// @ ensures   s == nil ==> Mem(rs, vs) && IsInit(rs, vs)
// @ ensures   s != nil ==> Mem(seq[*Ring]{r} ++ ss ++ ts, seq[any]{v0} ++ ws ++ tvs)
// @ ensures   s != nil ==> IsInit(seq[*Ring]{r} ++ ss ++ ts, seq[any]{v0} ++ ws ++ tvs)
// @ decreases
func (r *Ring) Link(s *Ring /*@, ghost rs seq[*Ring], ghost vs seq[any], ghost v0 any, ghost ts seq[*Ring], ghost tvs seq[any], ghost ss seq[*Ring], ghost ws seq[any] @*/) (ret *Ring) {
	n := r.Next( /*@ rs, vs, 0 @*/ )
	if s != nil {
		p := s.Prev( /*@ ss, ws, 0 @*/ )
		//@ ghost ars := seq[*Ring]{r} ++ ss ++ ts
		//@ ghost avs := seq[any]{v0} ++ ws ++ tvs
		//@ memDisjoint(rs, vs, ss, ws)
		//@ spliceRead(ars, rs, r, ss, ts)
		//@ spliceReadV(avs, vs, v0, ws, tvs)
		//@ unfold Mem(rs, vs)
		//@ unfold Mem(ss, ws)
		// Note: Cannot use multiple assignment because
		// evaluation order of LHS is not specified.
		r.next = s
		s.prev = r
		n.prev = p
		p.next = n
		// The merged ring is one footprint, not two, so it folds straight back.
		//@ assert forall t, u int :: {rs[t], ss[u]} 0 <= t && t < len(rs) && 0 <= u && u < len(ss) ==> rs[t] != ss[u]
		//@ assert ars[0].next != nil
		//@ fold Mem(ars, avs)
	}
	return n
}

// Unlink removes n % r.Len() elements from the ring r, starting
// at r.Next(). If n % r.Len() == 0, r remains unchanged.
// The result is the removed subring. r must not be empty.
//
// NOTE: not verified. Unlink is exactly the same-ring case of Link, which
// Link's contract excludes; see gobra-status.md for how far that proof got and
// what stopped it. The trusted here is not decoration: it suppresses
// type-checking of the body, which calls Move and Link without their ghost
// arguments.
// @ trusted
// @ requires  false
func (r *Ring) Unlink(n int) *Ring {
	if n <= 0 {
		return nil
	}
	return r.Link(r.Move(n + 1))
}

// Len computes the number of elements in ring r.
// It executes in time proportional to the number of elements.
//
// @ preserves r != nil ==> Mem(rs, vs)
// @ requires  r != nil ==> 0 <= i && i < len(rs) && rs[i] == r
// @ requires  r == nil ==> len(rs) == 0
// @ ensures   r != nil ==> IsInit(rs, vs)
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
// The ghost argument vis is the client's side of the closure specification in
// spec.gobra: vis.Seen(calls) is its invariant after f has been applied to
// exactly the values calls, and vis.Accepts says which values its f can be
// applied to at all. Do reports the values in the order it visits them, so
// unlike the other methods it needs the sequence to start at the receiver:
// rs[0] == r.
// @ preserves r != nil ==> Mem(rs, vs)
// @ requires  r != nil ==> 0 < len(rs) && rs[0] == r
// @ requires  r == nil ==> len(rs) == 0 && len(vs) == 0
// @ requires  vis != nil && vis.Seen(seq[any]{})
// @ requires  f implements VisitSpec{vis}
// @ requires  forall t int :: {vs[t]} 0 <= t && t < len(vs) ==> vis.Accepts(vs[t])
// @ ensures   r != nil ==> IsInit(rs, vs)
// @ ensures   vis.Seen(vs)
// @ decreases
func (r *Ring) Do(f func( /*@ ghost seq[any], @*/ any) /*@, ghost rs seq[*Ring], ghost vs seq[any], ghost vis Visitor @*/) {
	if r != nil {
		//@ ghost m := len(rs)
		//@ ghost c := 1
		//@ ghost seen := seq[any]{}
		//@ unfold Mem(rs, vs)
		//@ assert r.Value === vs[0]
		//@ fold Mem(rs, vs)
		f( /*@ seen, @*/ /*@ unfolding Mem(rs, vs) in @*/ r.Value) /*@ as VisitSpec{vis} @*/
		//@ seen = seen ++ seq[any]{vs[0]}
		//@ invariant Mem(rs, vs)
		//@ invariant IsInit(rs, vs)
		//@ invariant 1 <= c && c <= m
		//@ invariant p == rs[c < m ? c : 0]
		//@ invariant len(seen) == c && vis.Seen(seen)
		//@ invariant forall t int :: {seen[t]} 0 <= t && t < c ==> seen[t] === vs[t]
		//@ decreases m - c
		for p := r.Next( /*@ rs, vs, 0 @*/ ); p != r; p = /*@ unfolding Mem(rs, vs) in @*/ p.next {
			//@ assert c < m
			//@ unfold Mem(rs, vs)
			//@ assert p.Value === vs[c]
			//@ assert c < m-1 ==> rs[c].next == rs[c+1]
			//@ assert c == m-1 ==> rs[c].next == rs[0]
			//@ fold Mem(rs, vs)
			//@ assert (unfolding Mem(rs, vs) in p.next) == rs[c+1 < m ? c+1 : 0]
			f( /*@ seen, @*/ /*@ unfolding Mem(rs, vs) in @*/ p.Value) /*@ as VisitSpec{vis} @*/
			//@ seen = seen ++ seq[any]{vs[c]}
			//@ c = c + 1
		}
		//@ unfold Mem(rs, vs)
		//@ assert rs[c < m ? c : 0] == rs[0]
		//@ fold Mem(rs, vs)
		//@ assert c == m
		//@ assert seen == vs
	}

}
