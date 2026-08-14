// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// +gobra

// Package list implements a doubly linked list.
//
// To iterate over a list (where l is a *List):
//	for e := l.Front(); e != nil; e = e.Next() {
//		// do something with e.Value
//	}
//
package list

// Element is an element of a linked list.
type Element struct {
	// Next and previous pointers in the doubly-linked list of elements.
	// To simplify the implementation, internally a list l is implemented
	// as a ring, such that &l.root is both the next element of the last
	// list element (l.Back()) and the previous element of the first list
	// element (l.Front()).
	next, prev *Element

	// The list to which this element belongs.
	list *List

	// The value stored with this element.
	Value any
}

// Next returns the next list element or nil.
//
// The ghost parameters describe where e currently lives: if l is non-nil,
// e is the element at index i of list l; if l is nil, e is detached (it does
// not belong to any list) and the caller owns it.
//@ requires l != nil ==> l.Mem(es, vs, true) && 0 <= i && i < len(es) && es[i] == e
//@ requires l == nil ==> acc(e) && e.list == nil
//@ ensures  l != nil ==> l.Mem(es, vs, true)
//@ ensures  l != nil && i < len(es)-1 ==> ret == es[i+1] && ret != nil
//@ ensures  l != nil && i == len(es)-1 ==> ret == nil
//@ ensures  l == nil ==> acc(e) && e.list == nil && e.next == old(e.next) && e.prev == old(e.prev) && e.Value === old(e.Value) && ret == nil
//@ decreases
func (e *Element) Next( /*@ ghost l *List, ghost es seq[*Element], ghost vs seq[any], ghost i int @*/ ) (ret *Element) {
	//@ ghost if l != nil { unfold l.Mem(es, vs, true) }
	//@ assert l != nil && i < len(es)-1 ==> es[i+1] != nil
	if p := e.next; e.list != nil && p != &e.list.root {
		//@ ghost if l != nil { fold l.Mem(es, vs, true) }
		return p
	}
	//@ ghost if l != nil { fold l.Mem(es, vs, true) }
	return nil
}

// Prev returns the previous list element or nil.
//
// The ghost parameters play the same role as in Next.
//@ requires l != nil ==> l.Mem(es, vs, true) && 0 <= i && i < len(es) && es[i] == e
//@ requires l == nil ==> acc(e) && e.list == nil
//@ ensures  l != nil ==> l.Mem(es, vs, true)
//@ ensures  l != nil && i > 0 ==> ret == es[i-1] && ret != nil
//@ ensures  l != nil && i == 0 ==> ret == nil
//@ ensures  l == nil ==> acc(e) && e.list == nil && e.next == old(e.next) && e.prev == old(e.prev) && e.Value === old(e.Value) && ret == nil
//@ decreases
func (e *Element) Prev( /*@ ghost l *List, ghost es seq[*Element], ghost vs seq[any], ghost i int @*/ ) (ret *Element) {
	//@ ghost if l != nil { unfold l.Mem(es, vs, true) }
	//@ assert l != nil && i > 0 ==> es[i-1] != nil
	if p := e.prev; e.list != nil && p != &e.list.root {
		//@ ghost if l != nil { fold l.Mem(es, vs, true) }
		return p
	}
	//@ ghost if l != nil { fold l.Mem(es, vs, true) }
	return nil
}

// List represents a doubly linked list.
// The zero value for List is an empty list ready to use.
type List struct {
	root   Element // sentinel list element, only &root, root.prev, and root.next are used
	length int     // current list length excluding (this) sentinel element
}

// Init initializes or clears list l.
//@ requires l.Mem(es, vs, ini)
//@ ensures  l.Mem(seq[*Element]{}, seq[any]{}, true)
//@ ensures  ret == l
//@ decreases
func (l *List) Init( /*@ ghost es seq[*Element], ghost vs seq[any], ghost ini bool @*/ ) (ret *List) {
	//@ unfold l.Mem(es, vs, ini)
	l.root.next = &l.root
	l.root.prev = &l.root
	l.length = 0
	//@ fold l.Mem(seq[*Element]{}, seq[any]{}, true)
	return l
}

// New returns an initialized list.
//@ ensures ret != nil
//@ ensures ret.Mem(seq[*Element]{}, seq[any]{}, true)
//@ decreases
func New() (ret *List) {
	l := new(List)
	//@ fold l.Mem(seq[*Element]{}, seq[any]{}, false)
	return l.Init( /*@ seq[*Element]{}, seq[any]{}, false @*/ )
}

// Len returns the number of elements of list l.
// The complexity is O(1).
//@ requires acc(l.Mem(es, vs, ini), _)
//@ ensures  res == len(es)
//@ decreases
//@ pure
func (l *List) Len( /*@ ghost es seq[*Element], ghost vs seq[any], ghost ini bool @*/ ) (res int) {
	return /*@ unfolding acc(l.Mem(es, vs, ini), _) in @*/ l.length
}

// Front returns the first element of list l or nil if the list is empty.
//@ requires l.Mem(es, vs, ini)
//@ ensures  l.Mem(es, vs, ini)
//@ ensures  len(es) > 0 ==> ret == es[0] && ret != nil
//@ ensures  len(es) == 0 ==> ret == nil
//@ decreases
func (l *List) Front( /*@ ghost es seq[*Element], ghost vs seq[any], ghost ini bool @*/ ) (ret *Element) {
	//@ unfold l.Mem(es, vs, ini)
	if l.length == 0 {
		//@ fold l.Mem(es, vs, ini)
		return nil
	}
	res := l.root.next
	//@ fold l.Mem(es, vs, ini)
	return res
}

// Back returns the last element of list l or nil if the list is empty.
//@ requires l.Mem(es, vs, ini)
//@ ensures  l.Mem(es, vs, ini)
//@ ensures  len(es) > 0 ==> ret == es[len(es)-1] && ret != nil
//@ ensures  len(es) == 0 ==> ret == nil
//@ decreases
func (l *List) Back( /*@ ghost es seq[*Element], ghost vs seq[any], ghost ini bool @*/ ) (ret *Element) {
	//@ unfold l.Mem(es, vs, ini)
	if l.length == 0 {
		//@ fold l.Mem(es, vs, ini)
		return nil
	}
	res := l.root.prev
	//@ fold l.Mem(es, vs, ini)
	return res
}

// lazyInit lazily initializes a zero List value.
//@ requires l.Mem(es, vs, ini)
//@ ensures  l.Mem(es, vs, true)
//@ decreases
func (l *List) lazyInit( /*@ ghost es seq[*Element], ghost vs seq[any], ghost ini bool @*/ ) {
	//@ unfold l.Mem(es, vs, ini)
	uninit := l.root.next == nil
	//@ fold l.Mem(es, vs, ini)
	if uninit {
		//@ assert es == seq[*Element]{} && vs == seq[any]{}
		l.Init( /*@ es, vs, ini @*/ )
	}
}

// insert inserts e after at, increments l.length, and returns e.
//
// The ghost index j identifies at: j == -1 stands for the sentinel &l.root,
// and 0 <= j < len(es) stands for es[j].
//@ requires l.Mem(es, vs, true)
//@ requires acc(e) && e.list == nil
//@ requires -1 <= j && j < len(es)
//@ requires at == (j == -1 ? &l.root : es[j])
//@ ensures  l.Mem(es[:j+1] ++ seq[*Element]{e} ++ es[j+1:], vs[:j+1] ++ seq[any]{old(e.Value)} ++ vs[j+1:], true)
//@ ensures  ret == e && ret != nil
//@ decreases
func (l *List) insert(e, at *Element /*@ , ghost es seq[*Element], ghost vs seq[any], ghost j int @*/ ) (ret *Element) {
	//@ unfold l.Mem(es, vs, true)
	// e is detached (e.list == nil) while every element of es has list == l,
	// and the sentinel is owned separately, so e is distinct from all of them.
	//@ assert forall i1 int :: {es[i1]} 0 <= i1 && i1 < len(es) ==> es[i1] != e
	//@ assert e != &l.root
	//@ ghost var es2 seq[*Element] = es[:j+1] ++ seq[*Element]{e} ++ es[j+1:]
	//@ ghost var vs2 seq[any] = vs[:j+1] ++ seq[any]{e.Value} ++ vs[j+1:]
	//@ assert len(es2) == len(es) + 1 && len(vs2) == len(vs) + 1
	//@ assert forall k int :: {es2[k]} 0 <= k && k <= j ==> es2[k] == es[k]
	//@ assert forall k int :: {vs2[k]} 0 <= k && k <= j ==> vs2[k] === vs[k]
	//@ assert es2[j+1] == e && vs2[j+1] === e.Value
	//@ assert forall k int :: {es2[k]} j+1 < k && k < len(es2) ==> es2[k] == es[k-1]
	//@ assert forall k int :: {vs2[k]} j+1 < k && k < len(vs2) ==> vs2[k] === vs[k-1]
	// name at's successor so that the linkage quantifier applies to it
	//@ assert j == -1 && len(es) > 0 ==> l.root.next == es[0]
	//@ assert 0 <= j && j < len(es)-1 ==> es[j].next == es[j+1]
	//@ assert j == len(es)-1 && j >= 0 ==> es[j].next == &l.root
	e.prev = at
	e.next = at.next
	e.prev.next = e
	e.next.prev = e
	e.list = l
	l.length++
	//@ fold l.Mem(es2, vs2, true)
	return e
}

// insertValue is a convenience wrapper for insert(&Element{Value: v}, at).
//@ requires l.Mem(es, vs, true)
//@ requires -1 <= j && j < len(es)
//@ requires at == (j == -1 ? &l.root : es[j])
//@ ensures  l.Mem(es[:j+1] ++ seq[*Element]{ret} ++ es[j+1:], vs[:j+1] ++ seq[any]{v} ++ vs[j+1:], true)
//@ ensures  ret != nil
//@ decreases
func (l *List) insertValue(v any, at *Element /*@ , ghost es seq[*Element], ghost vs seq[any], ghost j int @*/ ) (ret *Element) {
	return l.insert(&Element{Value: v}, at /*@ , es, vs, j @*/ )
}

// remove removes e from its list, decrements l.length
//@ requires l.Mem(es, vs, true)
//@ requires len(es) == len(vs)
//@ requires 0 <= i && i < len(es) && es[i] == e
//@ ensures  l.Mem(es[:i] ++ es[i+1:], vs[:i] ++ vs[i+1:], true)
//@ ensures  acc(e) && e.list == nil && e.next == nil && e.prev == nil && e.Value === vs[i]
//@ decreases
func (l *List) remove(e *Element /*@ , ghost es seq[*Element], ghost vs seq[any], ghost i int @*/ ) {
	//@ unfold l.Mem(es, vs, true)
	//@ ghost var es2 seq[*Element] = es[:i] ++ es[i+1:]
	//@ ghost var vs2 seq[any] = vs[:i] ++ vs[i+1:]
	//@ assert len(es2) == len(es) - 1 && len(vs2) == len(vs) - 1
	//@ assert forall k int :: {es2[k]} 0 <= k && k < i ==> es2[k] == es[k] && vs2[k] === vs[k]
	//@ assert forall k int :: {es2[k]} i <= k && k < len(es2) ==> es2[k] == es[k+1] && vs2[k] === vs[k+1]
	// name e's neighbors so that the linkage quantifier applies to them
	//@ assert i > 0 ==> es[i].prev == es[i-1]
	//@ assert i == 0 ==> es[i].prev == &l.root
	//@ assert i < len(es)-1 ==> es[i].next == es[i+1]
	//@ assert i == len(es)-1 ==> es[i].next == &l.root
	e.prev.next = e.next
	e.next.prev = e.prev
	e.next = nil // avoid memory leaks
	e.prev = nil // avoid memory leaks
	e.list = nil
	l.length--
	//@ fold l.Mem(es2, vs2, true)
}

// move moves e to next to at.
//
// The ghost index i identifies e (e == es[i]) and the ghost index j
// identifies at, as in insert: j == -1 stands for the sentinel &l.root.
//@ requires l.Mem(es, vs, true)
//@ requires len(es) == len(vs)
//@ requires 0 <= i && i < len(es) && es[i] == e
//@ requires -1 <= j && j < len(es)
//@ requires at == (j == -1 ? &l.root : es[j])
//@ ensures  l.Mem(moveSeq(es, i, j), moveSeqV(vs, i, j), true)
//@ decreases
func (l *List) move(e, at *Element /*@ , ghost es seq[*Element], ghost vs seq[any], ghost i int, ghost j int @*/ ) {
	//@ unfold l.Mem(es, vs, true)
	//@ assert forall i1, i2 int :: {es[i1], es[i2]} 0 <= i1 && i1 < i2 && i2 < len(es) ==> es[i1] != es[i2]
	if e == at {
		//@ assert i == j
		//@ fold l.Mem(es, vs, true)
		return
	}
	//@ assert i != j
	// name the neighbors of e and of at so that the linkage quantifier
	// applies to them
	//@ assert i > 0 ==> es[i].prev == es[i-1]
	//@ assert i == 0 ==> es[i].prev == &l.root
	//@ assert i < len(es)-1 ==> es[i].next == es[i+1]
	//@ assert i == len(es)-1 ==> es[i].next == &l.root
	//@ assert j == -1 && len(es) > 0 ==> l.root.next == es[0]
	//@ assert 0 <= j && j < len(es)-1 ==> es[j].next == es[j+1]
	//@ assert j == len(es)-1 && j >= 0 ==> es[j].next == &l.root
	e.prev.next = e.next
	e.next.prev = e.prev

	e.prev = at
	e.next = at.next
	e.prev.next = e
	e.next.prev = e
	//@ ghost var es2 seq[*Element] = moveSeq(es, i, j)
	//@ ghost var vs2 seq[any] = moveSeqV(vs, i, j)
	//@ assert len(es2) == len(es) && len(vs2) == len(vs)
	/*@
	ghost if j < i {
		assert forall k int :: {es2[k]} 0 <= k && k <= j ==> es2[k] == es[k] && vs2[k] === vs[k]
		assert es2[j+1] == e && vs2[j+1] === vs[i]
		assert forall k int :: {es2[k]} j+1 < k && k <= i ==> es2[k] == es[k-1] && vs2[k] === vs[k-1]
		assert forall k int :: {es2[k]} i < k && k < len(es2) ==> es2[k] == es[k] && vs2[k] === vs[k]
	} else {
		assert forall k int :: {es2[k]} 0 <= k && k < i ==> es2[k] == es[k] && vs2[k] === vs[k]
		assert forall k int :: {es2[k]} i <= k && k < j ==> es2[k] == es[k+1] && vs2[k] === vs[k+1]
		assert es2[j] == e && vs2[j] === vs[i]
		assert forall k int :: {es2[k]} j < k && k < len(es2) ==> es2[k] == es[k] && vs2[k] === vs[k]
	}
	@*/
	//@ assert forall i1, i2 int :: {es2[i1], es2[i2]} 0 <= i1 && i1 < i2 && i2 < len(es2) ==> es2[i1] != es2[i2]
	//@ fold l.Mem(es2, vs2, true)
}

// Remove removes e from l if e is an element of list l.
// It returns the element value e.Value.
// The element must not be nil.
//
// The ghost parameters describe where e currently lives: in l itself
// (el == l, at index i), in another list el (with contents ees/evs, at
// index i), or detached (el == nil, owned by the caller).
//@ requires l.Mem(es, vs, ini)
//@ requires len(es) == len(vs)
//@ requires el == l ==> 0 <= i && i < len(es) && es[i] == e
//@ requires el != l && el != nil ==> el.Mem(ees, evs, true) && len(ees) == len(evs) && 0 <= i && i < len(ees) && ees[i] == e
//@ requires el == nil ==> acc(e) && e.list == nil
//@ ensures  el == l ==> l.Mem(es[:i] ++ es[i+1:], vs[:i] ++ vs[i+1:], true)
//@ ensures  el == l ==> acc(e) && e.list == nil && e.next == nil && e.prev == nil && e.Value === vs[i] && ret === vs[i]
//@ ensures  el != l ==> l.Mem(es, vs, ini)
//@ ensures  el != l && el != nil ==> el.Mem(ees, evs, true) && ret === evs[i]
//@ ensures  el == nil ==> acc(e) && e.list == nil && e.next == old(e.next) && e.prev == old(e.prev) && e.Value === old(e.Value) && ret === old(e.Value)
//@ decreases
func (l *List) Remove(e *Element /*@ , ghost el *List, ghost es seq[*Element], ghost vs seq[any], ghost ees seq[*Element], ghost evs seq[any], ghost i int, ghost ini bool @*/ ) (ret any) {
	//@ unfold l.Mem(es, vs, ini)
	//@ ghost if el != nil && el != l { unfold el.Mem(ees, evs, true) }
	inList := e.list == l
	//@ fold l.Mem(es, vs, ini)
	if inList {
		// if e.list == l, l must have been initialized when e was inserted
		// in l or l == nil (e is a zero Element) and l.remove will crash
		l.remove(e /*@ , es, vs, i @*/ )
	}
	v := e.Value
	//@ ghost if el != nil && el != l { fold el.Mem(ees, evs, true) }
	return v
}

// PushFront inserts a new element e with value v at the front of list l and returns e.
//@ requires l.Mem(es, vs, ini)
//@ ensures  l.Mem(seq[*Element]{ret} ++ es, seq[any]{v} ++ vs, true)
//@ ensures  ret != nil
//@ decreases
func (l *List) PushFront(v any /*@ , ghost es seq[*Element], ghost vs seq[any], ghost ini bool @*/ ) (ret *Element) {
	l.lazyInit( /*@ es, vs, ini @*/ )
	return l.insertValue(v, &l.root /*@ , es, vs, -1 @*/ )
}

// PushBack inserts a new element e with value v at the back of list l and returns e.
//@ requires l.Mem(es, vs, ini)
//@ ensures  l.Mem(es ++ seq[*Element]{ret}, vs ++ seq[any]{v}, true)
//@ ensures  ret != nil
//@ decreases
func (l *List) PushBack(v any /*@ , ghost es seq[*Element], ghost vs seq[any], ghost ini bool @*/ ) (ret *Element) {
	l.lazyInit( /*@ es, vs, ini @*/ )
	//@ unfold l.Mem(es, vs, true)
	at := l.root.prev
	//@ fold l.Mem(es, vs, true)
	return l.insertValue(v, at /*@ , es, vs, len(es)-1 @*/ )
}

// InsertBefore inserts a new element e with value v immediately before mark and returns e.
// If mark is not an element of l, the list is not modified.
// The mark must not be nil.
//
// The ghost parameters describe where mark currently lives, as in Remove.
//@ requires l.Mem(es, vs, ini)
//@ requires ml == l ==> 0 <= m && m < len(es) && es[m] == mark
//@ requires ml != l && ml != nil ==> ml.Mem(mes, mvs, true) && 0 <= m && m < len(mes) && mes[m] == mark
//@ requires ml == nil ==> acc(mark) && mark.list == nil
//@ ensures  ml == l ==> l.Mem(es[:m] ++ seq[*Element]{ret} ++ es[m:], vs[:m] ++ seq[any]{v} ++ vs[m:], true) && ret != nil
//@ ensures  ml != l ==> l.Mem(es, vs, ini) && ret == nil
//@ ensures  ml != l && ml != nil ==> ml.Mem(mes, mvs, true)
//@ ensures  ml == nil ==> acc(mark) && mark.list == nil && mark.next == old(mark.next) && mark.prev == old(mark.prev) && mark.Value === old(mark.Value)
//@ decreases
func (l *List) InsertBefore(v any, mark *Element /*@ , ghost ml *List, ghost es seq[*Element], ghost vs seq[any], ghost mes seq[*Element], ghost mvs seq[any], ghost m int, ghost ini bool @*/ ) (ret *Element) {
	//@ unfold l.Mem(es, vs, ini)
	//@ ghost if ml != nil && ml != l { unfold ml.Mem(mes, mvs, true) }
	if mark.list != l {
		//@ fold l.Mem(es, vs, ini)
		//@ ghost if ml != nil && ml != l { fold ml.Mem(mes, mvs, true) }
		return nil
	}
	at := mark.prev
	//@ fold l.Mem(es, vs, ini)
	// see comment in List.Remove about initialization of l
	return l.insertValue(v, at /*@ , es, vs, m-1 @*/ )
}

// InsertAfter inserts a new element e with value v immediately after mark and returns e.
// If mark is not an element of l, the list is not modified.
// The mark must not be nil.
//
// The ghost parameters describe where mark currently lives, as in Remove.
//@ requires l.Mem(es, vs, ini)
//@ requires ml == l ==> 0 <= m && m < len(es) && es[m] == mark
//@ requires ml != l && ml != nil ==> ml.Mem(mes, mvs, true) && 0 <= m && m < len(mes) && mes[m] == mark
//@ requires ml == nil ==> acc(mark) && mark.list == nil
//@ ensures  ml == l ==> l.Mem(es[:m+1] ++ seq[*Element]{ret} ++ es[m+1:], vs[:m+1] ++ seq[any]{v} ++ vs[m+1:], true) && ret != nil
//@ ensures  ml != l ==> l.Mem(es, vs, ini) && ret == nil
//@ ensures  ml != l && ml != nil ==> ml.Mem(mes, mvs, true)
//@ ensures  ml == nil ==> acc(mark) && mark.list == nil && mark.next == old(mark.next) && mark.prev == old(mark.prev) && mark.Value === old(mark.Value)
//@ decreases
func (l *List) InsertAfter(v any, mark *Element /*@ , ghost ml *List, ghost es seq[*Element], ghost vs seq[any], ghost mes seq[*Element], ghost mvs seq[any], ghost m int, ghost ini bool @*/ ) (ret *Element) {
	//@ unfold l.Mem(es, vs, ini)
	//@ ghost if ml != nil && ml != l { unfold ml.Mem(mes, mvs, true) }
	if mark.list != l {
		//@ fold l.Mem(es, vs, ini)
		//@ ghost if ml != nil && ml != l { fold ml.Mem(mes, mvs, true) }
		return nil
	}
	//@ fold l.Mem(es, vs, ini)
	// see comment in List.Remove about initialization of l
	return l.insertValue(v, mark /*@ , es, vs, m @*/ )
}

// MoveToFront moves element e to the front of list l.
// If e is not an element of l, the list is not modified.
// The element must not be nil.
//
// The ghost parameters describe where e currently lives, as in Remove.
//@ requires l.Mem(es, vs, ini)
//@ requires len(es) == len(vs)
//@ requires el == l ==> 0 <= i && i < len(es) && es[i] == e
//@ requires el != l && el != nil ==> el.Mem(ees, evs, true) && 0 <= i && i < len(ees) && ees[i] == e
//@ requires el == nil ==> acc(e) && e.list == nil
//@ ensures  el == l ==> l.Mem(moveSeq(es, i, -1), moveSeqV(vs, i, -1), true)
//@ ensures  el != l ==> l.Mem(es, vs, ini)
//@ ensures  el != l && el != nil ==> el.Mem(ees, evs, true)
//@ ensures  el == nil ==> acc(e) && e.list == nil && e.next == old(e.next) && e.prev == old(e.prev) && e.Value === old(e.Value)
//@ decreases
func (l *List) MoveToFront(e *Element /*@ , ghost el *List, ghost es seq[*Element], ghost vs seq[any], ghost ees seq[*Element], ghost evs seq[any], ghost i int, ghost ini bool @*/ ) {
	//@ unfold l.Mem(es, vs, ini)
	//@ assert forall i1, i2 int :: {es[i1], es[i2]} 0 <= i1 && i1 < i2 && i2 < len(es) ==> es[i1] != es[i2]
	//@ ghost if el != nil && el != l { unfold el.Mem(ees, evs, true) }
	stay := e.list != l || l.root.next == e
	//@ fold l.Mem(es, vs, ini)
	//@ ghost if el != nil && el != l { fold el.Mem(ees, evs, true) }
	if stay {
		return
	}
	// see comment in List.Remove about initialization of l
	l.move(e, &l.root /*@ , es, vs, i, -1 @*/ )
}

// MoveToBack moves element e to the back of list l.
// If e is not an element of l, the list is not modified.
// The element must not be nil.
//
// The ghost parameters describe where e currently lives, as in Remove.
//@ requires l.Mem(es, vs, ini)
//@ requires len(es) == len(vs)
//@ requires el == l ==> 0 <= i && i < len(es) && es[i] == e
//@ requires el != l && el != nil ==> el.Mem(ees, evs, true) && 0 <= i && i < len(ees) && ees[i] == e
//@ requires el == nil ==> acc(e) && e.list == nil
//@ ensures  el == l ==> l.Mem(moveSeq(es, i, len(es)-1), moveSeqV(vs, i, len(vs)-1), true)
//@ ensures  el != l ==> l.Mem(es, vs, ini)
//@ ensures  el != l && el != nil ==> el.Mem(ees, evs, true)
//@ ensures  el == nil ==> acc(e) && e.list == nil && e.next == old(e.next) && e.prev == old(e.prev) && e.Value === old(e.Value)
//@ decreases
func (l *List) MoveToBack(e *Element /*@ , ghost el *List, ghost es seq[*Element], ghost vs seq[any], ghost ees seq[*Element], ghost evs seq[any], ghost i int, ghost ini bool @*/ ) {
	//@ unfold l.Mem(es, vs, ini)
	//@ assert forall i1, i2 int :: {es[i1], es[i2]} 0 <= i1 && i1 < i2 && i2 < len(es) ==> es[i1] != es[i2]
	//@ ghost if el != nil && el != l { unfold el.Mem(ees, evs, true) }
	stay := e.list != l || l.root.prev == e
	at := l.root.prev
	//@ fold l.Mem(es, vs, ini)
	//@ ghost if el != nil && el != l { fold el.Mem(ees, evs, true) }
	if stay {
		return
	}
	// see comment in List.Remove about initialization of l
	l.move(e, at /*@ , es, vs, i, len(es)-1 @*/ )
}

// MoveBefore moves element e to its new position before mark.
// If e or mark is not an element of l, or e == mark, the list is not modified.
// The element and mark must not be nil.
//
// e must be an element of l (at ghost index i); the ghost parameters ml,
// mes, mvs, m describe where mark currently lives, as in Remove.
//@ requires l.Mem(es, vs, ini)
//@ requires len(es) == len(vs)
//@ requires 0 <= i && i < len(es) && es[i] == e
//@ requires ml == l ==> 0 <= m && m < len(es) && es[m] == mark
//@ requires ml != l && ml != nil ==> ml.Mem(mes, mvs, true) && 0 <= m && m < len(mes) && mes[m] == mark
//@ requires ml == nil ==> acc(mark) && mark.list == nil
//@ ensures  ml == l && i != m ==> l.Mem(moveSeq(es, i, m-1), moveSeqV(vs, i, m-1), true)
//@ ensures  ml == l && i == m ==> l.Mem(es, vs, ini)
//@ ensures  ml != l ==> l.Mem(es, vs, ini)
//@ ensures  ml != l && ml != nil ==> ml.Mem(mes, mvs, true)
//@ ensures  ml == nil ==> acc(mark) && mark.list == nil && mark.next == old(mark.next) && mark.prev == old(mark.prev) && mark.Value === old(mark.Value)
//@ decreases
func (l *List) MoveBefore(e, mark *Element /*@ , ghost ml *List, ghost es seq[*Element], ghost vs seq[any], ghost mes seq[*Element], ghost mvs seq[any], ghost i int, ghost m int, ghost ini bool @*/ ) {
	//@ unfold l.Mem(es, vs, ini)
	//@ assert forall i1, i2 int :: {es[i1], es[i2]} 0 <= i1 && i1 < i2 && i2 < len(es) ==> es[i1] != es[i2]
	//@ ghost if ml != nil && ml != l { unfold ml.Mem(mes, mvs, true) }
	stay := e.list != l || e == mark || mark.list != l
	//@ ghost if ml != nil && ml != l { fold ml.Mem(mes, mvs, true) }
	if stay {
		//@ fold l.Mem(es, vs, ini)
		return
	}
	at := mark.prev
	//@ fold l.Mem(es, vs, ini)
	l.move(e, at /*@ , es, vs, i, m-1 @*/ )
}

// MoveAfter moves element e to its new position after mark.
// If e or mark is not an element of l, or e == mark, the list is not modified.
// The element and mark must not be nil.
//
// e must be an element of l (at ghost index i); the ghost parameters ml,
// mes, mvs, m describe where mark currently lives, as in Remove.
//@ requires l.Mem(es, vs, ini)
//@ requires len(es) == len(vs)
//@ requires 0 <= i && i < len(es) && es[i] == e
//@ requires ml == l ==> 0 <= m && m < len(es) && es[m] == mark
//@ requires ml != l && ml != nil ==> ml.Mem(mes, mvs, true) && 0 <= m && m < len(mes) && mes[m] == mark
//@ requires ml == nil ==> acc(mark) && mark.list == nil
//@ ensures  ml == l && i != m ==> l.Mem(moveSeq(es, i, m), moveSeqV(vs, i, m), true)
//@ ensures  ml == l && i == m ==> l.Mem(es, vs, ini)
//@ ensures  ml != l ==> l.Mem(es, vs, ini)
//@ ensures  ml != l && ml != nil ==> ml.Mem(mes, mvs, true)
//@ ensures  ml == nil ==> acc(mark) && mark.list == nil && mark.next == old(mark.next) && mark.prev == old(mark.prev) && mark.Value === old(mark.Value)
//@ decreases
func (l *List) MoveAfter(e, mark *Element /*@ , ghost ml *List, ghost es seq[*Element], ghost vs seq[any], ghost mes seq[*Element], ghost mvs seq[any], ghost i int, ghost m int, ghost ini bool @*/ ) {
	//@ unfold l.Mem(es, vs, ini)
	//@ assert forall i1, i2 int :: {es[i1], es[i2]} 0 <= i1 && i1 < i2 && i2 < len(es) ==> es[i1] != es[i2]
	//@ ghost if ml != nil && ml != l { unfold ml.Mem(mes, mvs, true) }
	stay := e.list != l || e == mark || mark.list != l
	//@ ghost if ml != nil && ml != l { fold ml.Mem(mes, mvs, true) }
	if stay {
		//@ fold l.Mem(es, vs, ini)
		return
	}
	//@ fold l.Mem(es, vs, ini)
	l.move(e, mark /*@ , es, vs, i, m @*/ )
}

// PushBackList inserts a copy of another list at the back of list l.
// The lists l and other may be the same. They must not be nil.
//
// The ghost result nes holds the freshly allocated copies appended to l,
// in order, so that l is abstracted by es ++ nes afterwards.
//@ requires l.Mem(es, vs, ini)
//@ requires len(es) == len(vs)
//@ requires other != l ==> other.Mem(oes, ovs, oini) && len(oes) == len(ovs)
//@ requires other == l ==> oes == es && ovs == vs
//@ ensures  l.Mem(es ++ nes, vs ++ ovs, true)
//@ ensures  len(nes) == len(oes)
//@ ensures  other != l ==> other.Mem(oes, ovs, oini)
//@ decreases
func (l *List) PushBackList(other *List /*@ , ghost es seq[*Element], ghost vs seq[any], ghost oes seq[*Element], ghost ovs seq[any], ghost ini bool, ghost oini bool @*/ ) /*@ (ghost nes seq[*Element]) @*/ {
	l.lazyInit( /*@ es, vs, ini @*/ )
	//@ invariant 0 <= i && i <= len(oes)
	//@ invariant len(nes) == len(oes) - i
	//@ invariant other != l ==> other.Mem(oes, ovs, oini)
	//@ invariant l.Mem(es ++ nes, vs ++ ovs[:len(oes)-i], true)
	//@ invariant i > 0 ==> e == oes[len(oes)-i]
	//@ decreases i
	for i, e := other.Len( /*@ oes, ovs, other == l ? true : oini @*/ ), other.Front( /*@ oes, ovs, other == l ? true : oini @*/ ); i > 0; i, e = i-1, e.Next( /*@ other, other == l ? es ++ nes : oes, other == l ? vs ++ ovs[:len(oes)-i+1] : ovs, len(oes)-i @*/ ) {
		//@ ghost if other != l { unfold other.Mem(oes, ovs, oini) }
		//@ ghost if other == l { unfold l.Mem(es ++ nes, vs ++ ovs[:len(oes)-i], true) }
		v := e.Value
		//@ ghost if other != l { assert oini }
		//@ ghost if other != l { fold other.Mem(oes, ovs, oini) }
		//@ ghost if other == l { fold l.Mem(es ++ nes, vs ++ ovs[:len(oes)-i], true) }
		//@ unfold l.Mem(es ++ nes, vs ++ ovs[:len(oes)-i], true)
		at := l.root.prev
		//@ fold l.Mem(es ++ nes, vs ++ ovs[:len(oes)-i], true)
		ne := l.insertValue(v, at /*@ , es ++ nes, vs ++ ovs[:len(oes)-i], len(es ++ nes)-1 @*/ )
		_ = ne
		//@ nes = nes ++ seq[*Element]{ne}
	}
}

// PushFrontList inserts a copy of another list at the front of list l.
// The lists l and other may be the same. They must not be nil.
//
// The ghost result nes holds the freshly allocated copies prepended to l,
// in list order, so that l is abstracted by nes ++ es afterwards.
//@ requires l.Mem(es, vs, ini)
//@ requires len(es) == len(vs)
//@ requires other != l ==> other.Mem(oes, ovs, oini) && len(oes) == len(ovs)
//@ requires other == l ==> oes == es && ovs == vs
//@ ensures  l.Mem(nes ++ es, ovs ++ vs, true)
//@ ensures  len(nes) == len(oes)
//@ ensures  other != l ==> other.Mem(oes, ovs, oini)
//@ decreases
func (l *List) PushFrontList(other *List /*@ , ghost es seq[*Element], ghost vs seq[any], ghost oes seq[*Element], ghost ovs seq[any], ghost ini bool, ghost oini bool @*/ ) /*@ (ghost nes seq[*Element]) @*/ {
	l.lazyInit( /*@ es, vs, ini @*/ )
	//@ invariant 0 <= i && i <= len(oes)
	//@ invariant len(nes) == len(oes) - i
	//@ invariant other != l ==> other.Mem(oes, ovs, oini)
	//@ invariant l.Mem(nes ++ es, ovs[i:] ++ vs, true)
	//@ invariant i > 0 ==> e == oes[i-1]
	//@ decreases i
	for i, e := other.Len( /*@ oes, ovs, other == l ? true : oini @*/ ), other.Back( /*@ oes, ovs, other == l ? true : oini @*/ ); i > 0; i, e = i-1, e.Prev( /*@ other, other == l ? nes ++ es : oes, other == l ? ovs[i-1:] ++ vs : ovs, other == l ? len(oes) : i-1 @*/ ) {
		//@ ghost if other != l { unfold other.Mem(oes, ovs, oini) }
		//@ ghost if other == l { unfold l.Mem(nes ++ es, ovs[i:] ++ vs, true) }
		// name e's position in the current abstraction of l
		//@ ghost if other == l { assert (nes ++ es)[len(nes)+i-1] == es[i-1] }
		v := e.Value
		//@ ghost if other != l { assert oini }
		//@ ghost if other != l { fold other.Mem(oes, ovs, oini) }
		//@ ghost if other == l { fold l.Mem(nes ++ es, ovs[i:] ++ vs, true) }
		ne := l.insertValue(v, &l.root /*@ , nes ++ es, ovs[i:] ++ vs, -1 @*/ )
		_ = ne
		//@ nes = seq[*Element]{ne} ++ nes
		//@ assert len(nes) > 0 && (nes ++ es)[0] == ne && ne != nil
	}
}
