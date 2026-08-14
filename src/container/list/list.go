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
//@ requires l != nil ==> l.Mem(es, vs) && 0 <= i && i < len(es) && es[i] == e
//@ requires l == nil ==> acc(e) && e.list == nil
//@ ensures  l != nil ==> l.Mem(es, vs)
//@ ensures  l != nil && i < len(es)-1 ==> ret == es[i+1]
//@ ensures  l != nil && i == len(es)-1 ==> ret == nil
//@ ensures  l == nil ==> acc(e) && e.list == nil && e.next == old(e.next) && e.prev == old(e.prev) && e.Value === old(e.Value) && ret == nil
//@ decreases
func (e *Element) Next( /*@ ghost l *List, ghost es seq[*Element], ghost vs seq[any], ghost i int @*/ ) (ret *Element) {
	//@ ghost if l != nil { unfold l.Mem(es, vs) }
	if p := e.next; e.list != nil && p != &e.list.root {
		//@ ghost if l != nil { fold l.Mem(es, vs) }
		return p
	}
	//@ ghost if l != nil { fold l.Mem(es, vs) }
	return nil
}

// Prev returns the previous list element or nil.
//
// The ghost parameters play the same role as in Next.
//@ requires l != nil ==> l.Mem(es, vs) && 0 <= i && i < len(es) && es[i] == e
//@ requires l == nil ==> acc(e) && e.list == nil
//@ ensures  l != nil ==> l.Mem(es, vs)
//@ ensures  l != nil && i > 0 ==> ret == es[i-1]
//@ ensures  l != nil && i == 0 ==> ret == nil
//@ ensures  l == nil ==> acc(e) && e.list == nil && e.next == old(e.next) && e.prev == old(e.prev) && e.Value === old(e.Value) && ret == nil
//@ decreases
func (e *Element) Prev( /*@ ghost l *List, ghost es seq[*Element], ghost vs seq[any], ghost i int @*/ ) (ret *Element) {
	//@ ghost if l != nil { unfold l.Mem(es, vs) }
	if p := e.prev; e.list != nil && p != &e.list.root {
		//@ ghost if l != nil { fold l.Mem(es, vs) }
		return p
	}
	//@ ghost if l != nil { fold l.Mem(es, vs) }
	return nil
}

// List represents a doubly linked list.
// The zero value for List is an empty list ready to use.
type List struct {
	root   Element // sentinel list element, only &root, root.prev, and root.next are used
	length int     // current list length excluding (this) sentinel element
}

// Init initializes or clears list l.
//@ requires l.Mem(es, vs)
//@ ensures  l.Mem(seq[*Element]{}, seq[any]{})
//@ ensures  l.isInit(seq[*Element]{}, seq[any]{})
//@ ensures  ret == l
//@ decreases
func (l *List) Init( /*@ ghost es seq[*Element], ghost vs seq[any] @*/ ) (ret *List) {
	//@ unfold l.Mem(es, vs)
	l.root.next = &l.root
	l.root.prev = &l.root
	l.length = 0
	//@ fold l.Mem(seq[*Element]{}, seq[any]{})
	return l
}

// New returns an initialized list.
//@ ensures ret != nil
//@ ensures ret.Mem(seq[*Element]{}, seq[any]{})
//@ ensures ret.isInit(seq[*Element]{}, seq[any]{})
//@ decreases
func New() (ret *List) {
	l := new(List)
	//@ fold l.Mem(seq[*Element]{}, seq[any]{})
	return l.Init( /*@ seq[*Element]{}, seq[any]{} @*/ )
}

// Len returns the number of elements of list l.
// The complexity is O(1).
//@ requires acc(l.Mem(es, vs), _)
//@ ensures  res == len(es)
//@ decreases
//@ pure
func (l *List) Len( /*@ ghost es seq[*Element], ghost vs seq[any] @*/ ) (res int) {
	return /*@ unfolding acc(l.Mem(es, vs), _) in @*/ l.length
}

// Front returns the first element of list l or nil if the list is empty.
//@ requires l.Mem(es, vs)
//@ ensures  l.Mem(es, vs)
//@ ensures  len(es) > 0 ==> ret == es[0]
//@ ensures  len(es) == 0 ==> ret == nil
//@ decreases
func (l *List) Front( /*@ ghost es seq[*Element], ghost vs seq[any] @*/ ) (ret *Element) {
	//@ unfold l.Mem(es, vs)
	if l.length == 0 {
		//@ fold l.Mem(es, vs)
		return nil
	}
	res := l.root.next
	//@ fold l.Mem(es, vs)
	return res
}

// Back returns the last element of list l or nil if the list is empty.
//@ requires l.Mem(es, vs)
//@ ensures  l.Mem(es, vs)
//@ ensures  len(es) > 0 ==> ret == es[len(es)-1]
//@ ensures  len(es) == 0 ==> ret == nil
//@ decreases
func (l *List) Back( /*@ ghost es seq[*Element], ghost vs seq[any] @*/ ) (ret *Element) {
	//@ unfold l.Mem(es, vs)
	if l.length == 0 {
		//@ fold l.Mem(es, vs)
		return nil
	}
	res := l.root.prev
	//@ fold l.Mem(es, vs)
	return res
}

// lazyInit lazily initializes a zero List value.
//@ requires l.Mem(es, vs)
//@ ensures  l.Mem(es, vs)
//@ ensures  l.isInit(es, vs)
//@ decreases
func (l *List) lazyInit( /*@ ghost es seq[*Element], ghost vs seq[any] @*/ ) {
	//@ unfold l.Mem(es, vs)
	uninit := l.root.next == nil
	//@ fold l.Mem(es, vs)
	if uninit {
		//@ assert es == seq[*Element]{} && vs == seq[any]{}
		l.Init( /*@ es, vs @*/ )
	}
}

// insert inserts e after at, increments l.length, and returns e.
//
// The ghost index j identifies at: j == -1 stands for the sentinel &l.root,
// and 0 <= j < len(es) stands for es[j].
//@ requires l.Mem(es, vs)
//@ requires l.isInit(es, vs)
//@ requires acc(e) && e.list == nil
//@ requires -1 <= j && j < len(es)
//@ requires at == (j == -1 ? &l.root : es[j])
//@ ensures  l.Mem(es[:j+1] ++ seq[*Element]{e} ++ es[j+1:], vs[:j+1] ++ seq[any]{old(e.Value)} ++ vs[j+1:])
//@ ensures  ret == e && ret != nil
//@ decreases
func (l *List) insert(e, at *Element /*@ , ghost es seq[*Element], ghost vs seq[any], ghost j int @*/ ) (ret *Element) {
	//@ unfold l.Mem(es, vs)
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
	//@ fold l.Mem(es2, vs2)
	return e
}

// insertValue is a convenience wrapper for insert(&Element{Value: v}, at).
//@ requires l.Mem(es, vs)
//@ requires l.isInit(es, vs)
//@ requires -1 <= j && j < len(es)
//@ requires at == (j == -1 ? &l.root : es[j])
//@ ensures  l.Mem(es[:j+1] ++ seq[*Element]{ret} ++ es[j+1:], vs[:j+1] ++ seq[any]{v} ++ vs[j+1:])
//@ ensures  ret != nil
//@ decreases
func (l *List) insertValue(v any, at *Element /*@ , ghost es seq[*Element], ghost vs seq[any], ghost j int @*/ ) (ret *Element) {
	return l.insert(&Element{Value: v}, at /*@ , es, vs, j @*/ )
}

// remove removes e from its list, decrements l.length
//@ requires l.Mem(es, vs)
//@ requires len(es) == len(vs)
//@ requires 0 <= i && i < len(es) && es[i] == e
//@ ensures  l.Mem(es[:i] ++ es[i+1:], vs[:i] ++ vs[i+1:])
//@ ensures  acc(e) && e.list == nil && e.next == nil && e.prev == nil && e.Value === vs[i]
//@ decreases
func (l *List) remove(e *Element /*@ , ghost es seq[*Element], ghost vs seq[any], ghost i int @*/ ) {
	//@ unfold l.Mem(es, vs)
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
	//@ fold l.Mem(es2, vs2)
}

// move moves e to next to at.
//@ trusted
//@ requires false
func (l *List) move(e, at *Element) {
	if e == at {
		return
	}
	e.prev.next = e.next
	e.next.prev = e.prev

	e.prev = at
	e.next = at.next
	e.prev.next = e
	e.next.prev = e
}

// Remove removes e from l if e is an element of list l.
// It returns the element value e.Value.
// The element must not be nil.
//@ trusted
//@ requires false
func (l *List) Remove(e *Element) any {
	if e.list == l {
		// if e.list == l, l must have been initialized when e was inserted
		// in l or l == nil (e is a zero Element) and l.remove will crash
		l.remove(e)
	}
	return e.Value
}

// PushFront inserts a new element e with value v at the front of list l and returns e.
//@ trusted
//@ requires false
func (l *List) PushFront(v any) *Element {
	l.lazyInit()
	return l.insertValue(v, &l.root)
}

// PushBack inserts a new element e with value v at the back of list l and returns e.
//@ trusted
//@ requires false
func (l *List) PushBack(v any) *Element {
	l.lazyInit()
	return l.insertValue(v, l.root.prev)
}

// InsertBefore inserts a new element e with value v immediately before mark and returns e.
// If mark is not an element of l, the list is not modified.
// The mark must not be nil.
//@ trusted
//@ requires false
func (l *List) InsertBefore(v any, mark *Element) *Element {
	if mark.list != l {
		return nil
	}
	// see comment in List.Remove about initialization of l
	return l.insertValue(v, mark.prev)
}

// InsertAfter inserts a new element e with value v immediately after mark and returns e.
// If mark is not an element of l, the list is not modified.
// The mark must not be nil.
//@ trusted
//@ requires false
func (l *List) InsertAfter(v any, mark *Element) *Element {
	if mark.list != l {
		return nil
	}
	// see comment in List.Remove about initialization of l
	return l.insertValue(v, mark)
}

// MoveToFront moves element e to the front of list l.
// If e is not an element of l, the list is not modified.
// The element must not be nil.
//@ trusted
//@ requires false
func (l *List) MoveToFront(e *Element) {
	if e.list != l || l.root.next == e {
		return
	}
	// see comment in List.Remove about initialization of l
	l.move(e, &l.root)
}

// MoveToBack moves element e to the back of list l.
// If e is not an element of l, the list is not modified.
// The element must not be nil.
//@ trusted
//@ requires false
func (l *List) MoveToBack(e *Element) {
	if e.list != l || l.root.prev == e {
		return
	}
	// see comment in List.Remove about initialization of l
	l.move(e, l.root.prev)
}

// MoveBefore moves element e to its new position before mark.
// If e or mark is not an element of l, or e == mark, the list is not modified.
// The element and mark must not be nil.
//@ trusted
//@ requires false
func (l *List) MoveBefore(e, mark *Element) {
	if e.list != l || e == mark || mark.list != l {
		return
	}
	l.move(e, mark.prev)
}

// MoveAfter moves element e to its new position after mark.
// If e or mark is not an element of l, or e == mark, the list is not modified.
// The element and mark must not be nil.
//@ trusted
//@ requires false
func (l *List) MoveAfter(e, mark *Element) {
	if e.list != l || e == mark || mark.list != l {
		return
	}
	l.move(e, mark)
}

// PushBackList inserts a copy of another list at the back of list l.
// The lists l and other may be the same. They must not be nil.
//@ trusted
//@ requires false
func (l *List) PushBackList(other *List) {
	l.lazyInit()
	for i, e := other.Len(), other.Front(); i > 0; i, e = i-1, e.Next() {
		l.insertValue(e.Value, l.root.prev)
	}
}

// PushFrontList inserts a copy of another list at the front of list l.
// The lists l and other may be the same. They must not be nil.
//@ trusted
//@ requires false
func (l *List) PushFrontList(other *List) {
	l.lazyInit()
	for i, e := other.Len(), other.Back(); i > 0; i, e = i-1, e.Prev() {
		l.insertValue(e.Value, &l.root)
	}
}
