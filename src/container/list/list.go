// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// +gobra

// Package list implements a doubly linked list.
//
// To iterate over a list (where l is a *List):
//
//	for e := l.Front(); e != nil; e = e.Next() {
//		// do something with e.Value
//	}
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
// @ preserves l != nil ==> l.Mem()
// @ preserves l == nil ==> acc(e) && e.list == nil
// @ requires  l != nil ==> 0 <= i && i < len(l.Es()) && l.Es()[i] == e
// @ ensures   l != nil ==> l.Es() == old(l.Es()) && l.Vs() == old(l.Vs()) && l.Ini() == old(l.Ini())
// @ ensures   l != nil && i < len(l.Es())-1 ==> ret == l.Es()[i+1] && ret != nil
// @ ensures   l != nil && i == len(l.Es())-1 ==> ret == nil
// @ ensures   l == nil ==> e.next == old(e.next) && e.prev == old(e.prev) && e.Value === old(e.Value) && ret == nil
// @ decreases
func (e *Element) Next( /*@ ghost l *List, ghost i int @*/ ) (ret *Element) {
	//@ ghost if l != nil { unfold l.Mem() }
	//@ assert l != nil && i < len(l.es)-1 ==> l.es[i+1] != nil
	if p := e.next; e.list != nil && p != &e.list.root {
		//@ ghost if l != nil { fold l.Mem() }
		return p
	}
	//@ ghost if l != nil { fold l.Mem() }
	return nil
}

// Prev returns the previous list element or nil.
//
// The ghost parameters play the same role as in Next.
// @ preserves l != nil ==> l.Mem()
// @ preserves l == nil ==> acc(e) && e.list == nil
// @ requires  l != nil ==> 0 <= i && i < len(l.Es()) && l.Es()[i] == e
// @ ensures   l != nil ==> l.Es() == old(l.Es()) && l.Vs() == old(l.Vs()) && l.Ini() == old(l.Ini())
// @ ensures   l != nil && i > 0 ==> ret == l.Es()[i-1] && ret != nil
// @ ensures   l != nil && i == 0 ==> ret == nil
// @ ensures   l == nil ==> e.next == old(e.next) && e.prev == old(e.prev) && e.Value === old(e.Value) && ret == nil
// @ decreases
func (e *Element) Prev( /*@ ghost l *List, ghost i int @*/ ) (ret *Element) {
	//@ ghost if l != nil { unfold l.Mem() }
	//@ assert l != nil && i > 0 ==> l.es[i-1] != nil
	if p := e.prev; e.list != nil && p != &e.list.root {
		//@ ghost if l != nil { fold l.Mem() }
		return p
	}
	//@ ghost if l != nil { fold l.Mem() }
	return nil
}

// List represents a doubly linked list.
// The zero value for List is an empty list ready to use.
type List struct {
	root   Element // sentinel list element, only &root, root.prev, and root.next are used
	length int     // current list length excluding (this) sentinel element

	/*@
	// The abstraction of the list, maintained by the methods below and read
	// through the getters Es, Vs and Ini. The zero List value gives empty
	// sequences and ini == false, which is exactly the state lazyInit
	// recognizes.
	ghost es  seq[*Element]
	ghost vs  seq[any]
	ghost ini bool
	@*/
}

// Init initializes or clears list l.
// @ preserves l.Mem()
// @ ensures   l.Es() == seq[*Element]{} && l.Vs() == seq[any]{} && l.Ini()
// @ ensures   ret == l
// @ decreases
func (l *List) Init() (ret *List) {
	//@ unfold l.Mem()
	l.root.next = &l.root
	l.root.prev = &l.root
	l.length = 0
	//@ l.es = seq[*Element]{}
	//@ l.vs = seq[any]{}
	//@ l.ini = true
	//@ fold l.Mem()
	return l
}

// New returns an initialized list.
// @ ensures ret != nil && ret.Mem()
// @ ensures ret.Es() == seq[*Element]{} && ret.Vs() == seq[any]{} && ret.Ini()
// @ decreases
func New() (ret *List) {
	l := new(List)
	//@ fold l.Mem()
	return l.Init()
}

// Len returns the number of elements of list l.
// The complexity is O(1).
// @ requires l.Mem()
// @ ensures  res == len(l.Es())
// @ decreases
// @ pure
func (l *List) Len() (res int) {
	return /*@ unfolding l.Mem() in @*/ l.length
}

// Front returns the first element of list l or nil if the list is empty.
// @ preserves l.Mem()
// @ ensures   l.Es() == old(l.Es()) && l.Vs() == old(l.Vs()) && l.Ini() == old(l.Ini())
// @ ensures   len(l.Es()) > 0 ==> ret == l.Es()[0] && ret != nil
// @ ensures   len(l.Es()) == 0 ==> ret == nil
// @ decreases
func (l *List) Front() (ret *Element) {
	//@ unfold l.Mem()
	if l.length == 0 {
		//@ fold l.Mem()
		return nil
	}
	res := l.root.next
	//@ fold l.Mem()
	return res
}

// Back returns the last element of list l or nil if the list is empty.
// @ preserves l.Mem()
// @ ensures   l.Es() == old(l.Es()) && l.Vs() == old(l.Vs()) && l.Ini() == old(l.Ini())
// @ ensures   len(l.Es()) > 0 ==> ret == l.Es()[len(l.Es())-1] && ret != nil
// @ ensures   len(l.Es()) == 0 ==> ret == nil
// @ decreases
func (l *List) Back() (ret *Element) {
	//@ unfold l.Mem()
	if l.length == 0 {
		//@ fold l.Mem()
		return nil
	}
	res := l.root.prev
	//@ fold l.Mem()
	return res
}

// lazyInit lazily initializes a zero List value.
// @ preserves l.Mem()
// @ ensures   l.Ini()
// @ ensures   l.Es() == old(l.Es()) && l.Vs() == old(l.Vs())
// @ decreases
func (l *List) lazyInit() {
	//@ unfold l.Mem()
	uninit := l.root.next == nil
	// an initialized ring always has a non-nil successor of the sentinel, so
	// a nil one means the list is still the zero value, hence empty
	//@ assert len(l.es) > 0 ==> l.es[0] != nil
	//@ assert uninit ==> !l.ini
	//@ fold l.Mem()
	if uninit {
		//@ assert l.Es() == seq[*Element]{} && l.Vs() == seq[any]{}
		l.Init()
	}
}

// insert inserts e after at, increments l.length, and returns e.
//
// The ghost index j identifies at: j == -1 stands for the sentinel &l.root,
// and 0 <= j < len(l.Es()) stands for l.Es()[j].
// @ preserves l.Mem()
// @ requires  l.Ini()
// @ requires  acc(e) && e.list == nil
// @ requires  -1 <= j && j < len(l.Es())
// @ requires  at == (j == -1 ? &l.root : l.Es()[j])
// @ ensures   l.Ini()
// @ ensures   l.Es() == old(l.Es())[:j+1] ++ seq[*Element]{e} ++ old(l.Es())[j+1:]
// @ ensures   l.Vs() == old(l.Vs())[:j+1] ++ seq[any]{old(e.Value)} ++ old(l.Vs())[j+1:]
// @ ensures   ret == e && ret != nil
// @ decreases
func (l *List) insert(e, at *Element /*@ , ghost j int @*/) (ret *Element) {
	//@ unfold l.Mem()
	//@ ghost var es0 seq[*Element] = l.es
	//@ ghost var vs0 seq[any] = l.vs
	// e is detached (e.list == nil) while every element of es0 has list == l,
	// and the sentinel is owned separately, so e is distinct from all of them.
	//@ assert forall i1 int :: {es0[i1]} 0 <= i1 && i1 < len(es0) ==> es0[i1] != e
	//@ assert e != &l.root
	//@ ghost var es2 seq[*Element] = es0[:j+1] ++ seq[*Element]{e} ++ es0[j+1:]
	//@ ghost var vs2 seq[any] = vs0[:j+1] ++ seq[any]{e.Value} ++ vs0[j+1:]
	//@ assert len(es2) == len(es0) + 1 && len(vs2) == len(vs0) + 1
	//@ assert forall k int :: {es2[k]} 0 <= k && k <= j ==> es2[k] == es0[k]
	//@ assert forall k int :: {vs2[k]} 0 <= k && k <= j ==> vs2[k] === vs0[k]
	//@ assert es2[j+1] == e && vs2[j+1] === e.Value
	//@ assert forall k int :: {es2[k]} j+1 < k && k < len(es2) ==> es2[k] == es0[k-1]
	//@ assert forall k int :: {vs2[k]} j+1 < k && k < len(vs2) ==> vs2[k] === vs0[k-1]
	// name at's successor so that the linkage quantifier applies to it
	//@ assert j == -1 && len(es0) > 0 ==> l.root.next == es0[0]
	//@ assert 0 <= j && j < len(es0)-1 ==> es0[j].next == es0[j+1]
	//@ assert j == len(es0)-1 && j >= 0 ==> es0[j].next == &l.root
	e.prev = at
	e.next = at.next
	e.prev.next = e
	e.next.prev = e
	e.list = l
	l.length++
	//@ l.es = es2
	//@ l.vs = vs2
	//@ l.ini = true
	//@ fold l.Mem()
	return e
}

// insertValue is a convenience wrapper for insert(&Element{Value: v}, at).
// @ preserves l.Mem()
// @ requires  l.Ini()
// @ requires  -1 <= j && j < len(l.Es())
// @ requires  at == (j == -1 ? &l.root : l.Es()[j])
// @ ensures   l.Ini()
// @ ensures   l.Es() == old(l.Es())[:j+1] ++ seq[*Element]{ret} ++ old(l.Es())[j+1:]
// @ ensures   l.Vs() == old(l.Vs())[:j+1] ++ seq[any]{v} ++ old(l.Vs())[j+1:]
// @ ensures   ret != nil
// @ decreases
func (l *List) insertValue(v any, at *Element /*@ , ghost j int @*/) (ret *Element) {
	return l.insert(&Element{Value: v}, at /*@ , j @*/)
}

// remove removes e from its list, decrements l.length
// @ preserves l.Mem()
// @ requires  0 <= i && i < len(l.Es()) && l.Es()[i] == e
// @ ensures   l.Ini()
// @ ensures   l.Es() == old(l.Es())[:i] ++ old(l.Es())[i+1:]
// @ ensures   l.Vs() == old(l.Vs())[:i] ++ old(l.Vs())[i+1:]
// @ ensures   acc(e) && e.list == nil && e.next == nil && e.prev == nil && e.Value === old(l.Vs())[i]
// @ decreases
func (l *List) remove(e *Element /*@ , ghost i int @*/) {
	//@ unfold l.Mem()
	//@ ghost var es0 seq[*Element] = l.es
	//@ ghost var vs0 seq[any] = l.vs
	//@ ghost var es2 seq[*Element] = es0[:i] ++ es0[i+1:]
	//@ ghost var vs2 seq[any] = vs0[:i] ++ vs0[i+1:]
	//@ assert len(es2) == len(es0) - 1 && len(vs2) == len(vs0) - 1
	//@ assert forall k int :: {es2[k]} 0 <= k && k < i ==> es2[k] == es0[k] && vs2[k] === vs0[k]
	//@ assert forall k int :: {es2[k]} i <= k && k < len(es2) ==> es2[k] == es0[k+1] && vs2[k] === vs0[k+1]
	// name e's neighbors so that the linkage quantifier applies to them
	//@ assert i > 0 ==> es0[i].prev == es0[i-1]
	//@ assert i == 0 ==> es0[i].prev == &l.root
	//@ assert i < len(es0)-1 ==> es0[i].next == es0[i+1]
	//@ assert i == len(es0)-1 ==> es0[i].next == &l.root
	e.prev.next = e.next
	e.next.prev = e.prev
	e.next = nil // avoid memory leaks
	e.prev = nil // avoid memory leaks
	e.list = nil
	l.length--
	//@ l.es = es2
	//@ l.vs = vs2
	//@ fold l.Mem()
}

// move moves e to next to at.
//
// The ghost index i identifies e (e == l.Es()[i]) and the ghost index j
// identifies at, as in insert: j == -1 stands for the sentinel &l.root.
// @ preserves l.Mem()
// @ requires  0 <= i && i < len(l.Es()) && l.Es()[i] == e
// @ requires  -1 <= j && j < len(l.Es())
// @ requires  at == (j == -1 ? &l.root : l.Es()[j])
// @ ensures   l.Ini()
// @ ensures   l.Es() == MoveSeq(old(l.Es()), i, j)
// @ ensures   l.Vs() == MoveSeqV(old(l.Vs()), i, j)
// @ decreases
func (l *List) move(e, at *Element /*@ , ghost i int, ghost j int @*/) {
	//@ unfold l.Mem()
	//@ ghost var es0 seq[*Element] = l.es
	//@ ghost var vs0 seq[any] = l.vs
	//@ assert forall i1, i2 int :: {es0[i1], es0[i2]} 0 <= i1 && i1 < i2 && i2 < len(es0) ==> es0[i1] != es0[i2]
	if e == at {
		//@ assert i == j
		//@ fold l.Mem()
		return
	}
	//@ assert i != j
	// name the neighbors of e and of at so that the linkage quantifier
	// applies to them
	//@ assert i > 0 ==> es0[i].prev == es0[i-1]
	//@ assert i == 0 ==> es0[i].prev == &l.root
	//@ assert i < len(es0)-1 ==> es0[i].next == es0[i+1]
	//@ assert i == len(es0)-1 ==> es0[i].next == &l.root
	//@ assert j == -1 && len(es0) > 0 ==> l.root.next == es0[0]
	//@ assert 0 <= j && j < len(es0)-1 ==> es0[j].next == es0[j+1]
	//@ assert j == len(es0)-1 && j >= 0 ==> es0[j].next == &l.root
	e.prev.next = e.next
	e.next.prev = e.prev

	e.prev = at
	e.next = at.next
	e.prev.next = e
	e.next.prev = e
	//@ ghost var es2 seq[*Element] = MoveSeq(es0, i, j)
	//@ ghost var vs2 seq[any] = MoveSeqV(vs0, i, j)
	//@ assert len(es2) == len(es0) && len(vs2) == len(vs0)
	/*@
	ghost if j < i {
		assert forall k int :: {es2[k]} 0 <= k && k <= j ==> es2[k] == es0[k] && vs2[k] === vs0[k]
		assert es2[j+1] == e && vs2[j+1] === vs0[i]
		assert forall k int :: {es2[k]} j+1 < k && k <= i ==> es2[k] == es0[k-1] && vs2[k] === vs0[k-1]
		assert forall k int :: {es2[k]} i < k && k < len(es2) ==> es2[k] == es0[k] && vs2[k] === vs0[k]
	} else {
		assert forall k int :: {es2[k]} 0 <= k && k < i ==> es2[k] == es0[k] && vs2[k] === vs0[k]
		assert forall k int :: {es2[k]} i <= k && k < j ==> es2[k] == es0[k+1] && vs2[k] === vs0[k+1]
		assert es2[j] == e && vs2[j] === vs0[i]
		assert forall k int :: {es2[k]} j < k && k < len(es2) ==> es2[k] == es0[k] && vs2[k] === vs0[k]
	}
	@*/
	//@ assert forall i1, i2 int :: {es2[i1], es2[i2]} 0 <= i1 && i1 < i2 && i2 < len(es2) ==> es2[i1] != es2[i2]
	//@ l.es = es2
	//@ l.vs = vs2
	//@ fold l.Mem()
}

// Remove removes e from l if e is an element of list l.
// It returns the element value e.Value.
// The element must not be nil.
//
// The ghost parameters describe where e currently lives: in l itself
// (el == l, at index i), in another list el (at index i), or detached
// (el == nil, owned by the caller).
// @ preserves l.Mem()
// @ requires  el == l ==> 0 <= i && i < len(l.Es()) && l.Es()[i] == e
// @ requires  el != l && el != nil ==> el.Mem() && 0 <= i && i < len(el.Es()) && el.Es()[i] == e
// @ requires  el == nil ==> acc(e) && e.list == nil
// @ ensures   el == l ==> l.Es() == old(l.Es())[:i] ++ old(l.Es())[i+1:]
// @ ensures   el == l ==> l.Vs() == old(l.Vs())[:i] ++ old(l.Vs())[i+1:]
// @ ensures   el == l ==> acc(e) && e.list == nil && e.next == nil && e.prev == nil && e.Value === old(l.Vs())[i] && ret === old(l.Vs())[i]
// @ ensures   el != l ==> l.Es() == old(l.Es()) && l.Vs() == old(l.Vs()) && l.Ini() == old(l.Ini())
// @ ensures   el != l && el != nil ==> el.Mem() && el.Es() == old(el.Es()) && el.Vs() == old(el.Vs()) && ret === old(el.Vs())[i]
// @ ensures   el == nil ==> acc(e) && e.list == nil && e.next == old(e.next) && e.prev == old(e.prev) && e.Value === old(e.Value) && ret === old(e.Value)
// @ decreases
func (l *List) Remove(e *Element /*@ , ghost el *List, ghost i int @*/) (ret any) {
	//@ unfold l.Mem()
	//@ ghost if el != nil && el != l { unfold el.Mem() }
	//@ assert el == l ==> l.es[i].list == l
	inList := e.list == l
	//@ fold l.Mem()
	if inList {
		// if e.list == l, l must have been initialized when e was inserted
		// in l or l == nil (e is a zero Element) and l.remove will crash
		l.remove(e /*@ , i @*/)
	}
	v := e.Value
	//@ ghost if el != nil && el != l { fold el.Mem() }
	return v
}

// PushFront inserts a new element e with value v at the front of list l and returns e.
// @ preserves l.Mem()
// @ ensures   l.Ini()
// @ ensures   l.Es() == seq[*Element]{ret} ++ old(l.Es())
// @ ensures   l.Vs() == seq[any]{v} ++ old(l.Vs())
// @ ensures   ret != nil
// @ decreases
func (l *List) PushFront(v any) (ret *Element) {
	l.lazyInit()
	return l.insertValue(v, &l.root /*@ , -1 @*/)
}

// PushBack inserts a new element e with value v at the back of list l and returns e.
// @ preserves l.Mem()
// @ ensures   l.Ini()
// @ ensures   l.Es() == old(l.Es()) ++ seq[*Element]{ret}
// @ ensures   l.Vs() == old(l.Vs()) ++ seq[any]{v}
// @ ensures   ret != nil
// @ decreases
func (l *List) PushBack(v any) (ret *Element) {
	l.lazyInit()
	//@ unfold l.Mem()
	at := l.root.prev
	//@ ghost var n int = len(l.es)
	//@ fold l.Mem()
	return l.insertValue(v, at /*@ , n-1 @*/)
}

// InsertBefore inserts a new element e with value v immediately before mark and returns e.
// If mark is not an element of l, the list is not modified.
// The mark must not be nil.
//
// The ghost parameters describe where mark currently lives, as in Remove.
// @ preserves l.Mem()
// @ requires  ml == l ==> 0 <= m && m < len(l.Es()) && l.Es()[m] == mark
// @ requires  ml != l && ml != nil ==> ml.Mem() && 0 <= m && m < len(ml.Es()) && ml.Es()[m] == mark
// @ requires  ml == nil ==> acc(mark) && mark.list == nil
// @ ensures   ml == l ==> l.Es() == old(l.Es())[:m] ++ seq[*Element]{ret} ++ old(l.Es())[m:] && ret != nil
// @ ensures   ml == l ==> l.Vs() == old(l.Vs())[:m] ++ seq[any]{v} ++ old(l.Vs())[m:] && l.Ini()
// @ ensures   ml != l ==> l.Es() == old(l.Es()) && l.Vs() == old(l.Vs()) && l.Ini() == old(l.Ini()) && ret == nil
// @ ensures   ml != l && ml != nil ==> ml.Mem() && ml.Es() == old(ml.Es()) && ml.Vs() == old(ml.Vs())
// @ ensures   ml == nil ==> acc(mark) && mark.list == nil && mark.next == old(mark.next) && mark.prev == old(mark.prev) && mark.Value === old(mark.Value)
// @ decreases
func (l *List) InsertBefore(v any, mark *Element /*@ , ghost ml *List, ghost m int @*/) (ret *Element) {
	//@ unfold l.Mem()
	//@ ghost if ml != nil && ml != l { unfold ml.Mem() }
	//@ assert ml == l ==> l.es[m].list == l
	if mark.list != l {
		//@ fold l.Mem()
		//@ ghost if ml != nil && ml != l { fold ml.Mem() }
		return nil
	}
	at := mark.prev
	//@ assert m > 0 ==> l.es[m].prev == l.es[m-1]
	//@ assert m == 0 ==> l.es[m].prev == &l.root
	//@ fold l.Mem()
	// see comment in List.Remove about initialization of l
	return l.insertValue(v, at /*@ , m-1 @*/)
}

// InsertAfter inserts a new element e with value v immediately after mark and returns e.
// If mark is not an element of l, the list is not modified.
// The mark must not be nil.
//
// The ghost parameters describe where mark currently lives, as in Remove.
// @ preserves l.Mem()
// @ requires  ml == l ==> 0 <= m && m < len(l.Es()) && l.Es()[m] == mark
// @ requires  ml != l && ml != nil ==> ml.Mem() && 0 <= m && m < len(ml.Es()) && ml.Es()[m] == mark
// @ requires  ml == nil ==> acc(mark) && mark.list == nil
// @ ensures   ml == l ==> l.Es() == old(l.Es())[:m+1] ++ seq[*Element]{ret} ++ old(l.Es())[m+1:] && ret != nil
// @ ensures   ml == l ==> l.Vs() == old(l.Vs())[:m+1] ++ seq[any]{v} ++ old(l.Vs())[m+1:] && l.Ini()
// @ ensures   ml != l ==> l.Es() == old(l.Es()) && l.Vs() == old(l.Vs()) && l.Ini() == old(l.Ini()) && ret == nil
// @ ensures   ml != l && ml != nil ==> ml.Mem() && ml.Es() == old(ml.Es()) && ml.Vs() == old(ml.Vs())
// @ ensures   ml == nil ==> acc(mark) && mark.list == nil && mark.next == old(mark.next) && mark.prev == old(mark.prev) && mark.Value === old(mark.Value)
// @ decreases
func (l *List) InsertAfter(v any, mark *Element /*@ , ghost ml *List, ghost m int @*/) (ret *Element) {
	//@ unfold l.Mem()
	//@ ghost if ml != nil && ml != l { unfold ml.Mem() }
	//@ assert ml == l ==> l.es[m].list == l
	if mark.list != l {
		//@ fold l.Mem()
		//@ ghost if ml != nil && ml != l { fold ml.Mem() }
		return nil
	}
	//@ fold l.Mem()
	// see comment in List.Remove about initialization of l
	return l.insertValue(v, mark /*@ , m @*/)
}

// MoveToFront moves element e to the front of list l.
// If e is not an element of l, the list is not modified.
// The element must not be nil.
//
// The ghost parameters describe where e currently lives, as in Remove.
// @ preserves l.Mem()
// @ requires  el == l ==> 0 <= i && i < len(l.Es()) && l.Es()[i] == e
// @ requires  el != l && el != nil ==> el.Mem() && 0 <= i && i < len(el.Es()) && el.Es()[i] == e
// @ requires  el == nil ==> acc(e) && e.list == nil
// @ ensures   el == l ==> l.Es() == MoveSeq(old(l.Es()), i, -1) && l.Vs() == MoveSeqV(old(l.Vs()), i, -1) && l.Ini()
// @ ensures   el != l ==> l.Es() == old(l.Es()) && l.Vs() == old(l.Vs()) && l.Ini() == old(l.Ini())
// @ ensures   el != l && el != nil ==> el.Mem() && el.Es() == old(el.Es()) && el.Vs() == old(el.Vs())
// @ ensures   el == nil ==> acc(e) && e.list == nil && e.next == old(e.next) && e.prev == old(e.prev) && e.Value === old(e.Value)
// @ decreases
func (l *List) MoveToFront(e *Element /*@ , ghost el *List, ghost i int @*/) {
	//@ unfold l.Mem()
	//@ assert forall i1, i2 int :: {l.es[i1], l.es[i2]} 0 <= i1 && i1 < i2 && i2 < len(l.es) ==> l.es[i1] != l.es[i2]
	//@ ghost if el != nil && el != l { unfold el.Mem() }
	//@ assert el == l ==> l.es[i].list == l
	stay := e.list != l || l.root.next == e
	//@ assert el == l && stay ==> i == 0
	//@ fold l.Mem()
	//@ ghost if el != nil && el != l { fold el.Mem() }
	if stay {
		//@ assert el == l ==> MoveSeq(l.Es(), i, -1) == l.Es()
		//@ assert el == l ==> MoveSeqV(l.Vs(), i, -1) == l.Vs()
		return
	}
	// see comment in List.Remove about initialization of l
	l.move(e, &l.root /*@ , i, -1 @*/)
}

// MoveToBack moves element e to the back of list l.
// If e is not an element of l, the list is not modified.
// The element must not be nil.
//
// The ghost parameters describe where e currently lives, as in Remove.
// @ preserves l.Mem()
// @ requires  el == l ==> 0 <= i && i < len(l.Es()) && l.Es()[i] == e
// @ requires  el != l && el != nil ==> el.Mem() && 0 <= i && i < len(el.Es()) && el.Es()[i] == e
// @ requires  el == nil ==> acc(e) && e.list == nil
// @ ensures   el == l ==> l.Es() == MoveSeq(old(l.Es()), i, len(old(l.Es()))-1) && l.Ini()
// @ ensures   el == l ==> l.Vs() == MoveSeqV(old(l.Vs()), i, len(old(l.Vs()))-1)
// @ ensures   el != l ==> l.Es() == old(l.Es()) && l.Vs() == old(l.Vs()) && l.Ini() == old(l.Ini())
// @ ensures   el != l && el != nil ==> el.Mem() && el.Es() == old(el.Es()) && el.Vs() == old(el.Vs())
// @ ensures   el == nil ==> acc(e) && e.list == nil && e.next == old(e.next) && e.prev == old(e.prev) && e.Value === old(e.Value)
// @ decreases
func (l *List) MoveToBack(e *Element /*@ , ghost el *List, ghost i int @*/) {
	//@ unfold l.Mem()
	//@ assert forall i1, i2 int :: {l.es[i1], l.es[i2]} 0 <= i1 && i1 < i2 && i2 < len(l.es) ==> l.es[i1] != l.es[i2]
	//@ ghost if el != nil && el != l { unfold el.Mem() }
	//@ assert el == l ==> l.es[i].list == l
	stay := e.list != l || l.root.prev == e
	at := l.root.prev
	//@ ghost var n int = len(l.es)
	//@ assert el == l && stay ==> i == n-1
	//@ fold l.Mem()
	//@ ghost if el != nil && el != l { fold el.Mem() }
	if stay {
		//@ assert el == l ==> MoveSeq(l.Es(), i, len(l.Es())-1) == l.Es()
		//@ assert el == l ==> MoveSeqV(l.Vs(), i, len(l.Vs())-1) == l.Vs()
		return
	}
	// see comment in List.Remove about initialization of l
	l.move(e, at /*@ , i, n-1 @*/)
}

// MoveBefore moves element e to its new position before mark.
// If e or mark is not an element of l, or e == mark, the list is not modified.
// The element and mark must not be nil.
//
// e must be an element of l (at ghost index i); the ghost parameters ml and
// m describe where mark currently lives, as in Remove.
// @ preserves l.Mem()
// @ requires  0 <= i && i < len(l.Es()) && l.Es()[i] == e
// @ requires  ml == l ==> 0 <= m && m < len(l.Es()) && l.Es()[m] == mark
// @ requires  ml != l && ml != nil ==> ml.Mem() && 0 <= m && m < len(ml.Es()) && ml.Es()[m] == mark
// @ requires  ml == nil ==> acc(mark) && mark.list == nil
// @ ensures   ml == l && i != m ==> l.Es() == MoveSeq(old(l.Es()), i, m-1) && l.Vs() == MoveSeqV(old(l.Vs()), i, m-1) && l.Ini()
// @ ensures   ml == l && i == m ==> l.Es() == old(l.Es()) && l.Vs() == old(l.Vs()) && l.Ini() == old(l.Ini())
// @ ensures   ml != l ==> l.Es() == old(l.Es()) && l.Vs() == old(l.Vs()) && l.Ini() == old(l.Ini())
// @ ensures   ml != l && ml != nil ==> ml.Mem() && ml.Es() == old(ml.Es()) && ml.Vs() == old(ml.Vs())
// @ ensures   ml == nil ==> acc(mark) && mark.list == nil && mark.next == old(mark.next) && mark.prev == old(mark.prev) && mark.Value === old(mark.Value)
// @ decreases
func (l *List) MoveBefore(e, mark *Element /*@ , ghost ml *List, ghost i int, ghost m int @*/) {
	//@ unfold l.Mem()
	//@ assert forall i1, i2 int :: {l.es[i1], l.es[i2]} 0 <= i1 && i1 < i2 && i2 < len(l.es) ==> l.es[i1] != l.es[i2]
	//@ ghost if ml != nil && ml != l { unfold ml.Mem() }
	//@ assert l.es[i].list == l
	stay := e.list != l || e == mark || mark.list != l
	//@ ghost if ml != nil && ml != l { fold ml.Mem() }
	if stay {
		//@ assert ml == l ==> i == m
		//@ fold l.Mem()
		return
	}
	at := mark.prev
	//@ assert m > 0 ==> l.es[m].prev == l.es[m-1]
	//@ assert m == 0 ==> l.es[m].prev == &l.root
	//@ fold l.Mem()
	l.move(e, at /*@ , i, m-1 @*/)
}

// MoveAfter moves element e to its new position after mark.
// If e or mark is not an element of l, or e == mark, the list is not modified.
// The element and mark must not be nil.
//
// e must be an element of l (at ghost index i); the ghost parameters ml and
// m describe where mark currently lives, as in Remove.
// @ preserves l.Mem()
// @ requires  0 <= i && i < len(l.Es()) && l.Es()[i] == e
// @ requires  ml == l ==> 0 <= m && m < len(l.Es()) && l.Es()[m] == mark
// @ requires  ml != l && ml != nil ==> ml.Mem() && 0 <= m && m < len(ml.Es()) && ml.Es()[m] == mark
// @ requires  ml == nil ==> acc(mark) && mark.list == nil
// @ ensures   ml == l && i != m ==> l.Es() == MoveSeq(old(l.Es()), i, m) && l.Vs() == MoveSeqV(old(l.Vs()), i, m) && l.Ini()
// @ ensures   ml == l && i == m ==> l.Es() == old(l.Es()) && l.Vs() == old(l.Vs()) && l.Ini() == old(l.Ini())
// @ ensures   ml != l ==> l.Es() == old(l.Es()) && l.Vs() == old(l.Vs()) && l.Ini() == old(l.Ini())
// @ ensures   ml != l && ml != nil ==> ml.Mem() && ml.Es() == old(ml.Es()) && ml.Vs() == old(ml.Vs())
// @ ensures   ml == nil ==> acc(mark) && mark.list == nil && mark.next == old(mark.next) && mark.prev == old(mark.prev) && mark.Value === old(mark.Value)
// @ decreases
func (l *List) MoveAfter(e, mark *Element /*@ , ghost ml *List, ghost i int, ghost m int @*/) {
	//@ unfold l.Mem()
	//@ assert forall i1, i2 int :: {l.es[i1], l.es[i2]} 0 <= i1 && i1 < i2 && i2 < len(l.es) ==> l.es[i1] != l.es[i2]
	//@ ghost if ml != nil && ml != l { unfold ml.Mem() }
	//@ assert l.es[i].list == l
	stay := e.list != l || e == mark || mark.list != l
	//@ ghost if ml != nil && ml != l { fold ml.Mem() }
	if stay {
		//@ assert ml == l ==> i == m
		//@ fold l.Mem()
		return
	}
	//@ fold l.Mem()
	l.move(e, mark /*@ , i, m @*/)
}

// PushBackList inserts a copy of another list at the back of list l.
// The lists l and other may be the same. They must not be nil.
// @ preserves l.Mem()
// @ requires  other != l ==> other.Mem()
// @ ensures   l.Ini()
// @ ensures   l.Vs() == old(l.Vs()) ++ old(other.Vs())
// @ ensures   l.Es()[:len(old(l.Es()))] == old(l.Es())
// @ ensures   other != l ==> other.Mem() && other.Es() == old(other.Es()) && other.Vs() == old(other.Vs())
// @ decreases
func (l *List) PushBackList(other *List) {
	//@ ghost var es0 seq[*Element] = l.Es()
	//@ ghost var vs0 seq[any] = l.Vs()
	//@ ghost var oes0 seq[*Element] = other.Es()
	//@ ghost var ovs0 seq[any] = other.Vs()
	//@ assert len(es0) == len(vs0) && len(oes0) == len(ovs0)
	//@ assert other == l ==> es0 == oes0 && vs0 == ovs0
	l.lazyInit()
	//@ invariant len(es0) == len(vs0) && len(oes0) == len(ovs0)
	//@ invariant other == l ==> es0 == oes0 && vs0 == ovs0
	//@ invariant 0 <= i && i <= len(oes0)
	//@ invariant l.Mem() && l.Ini()
	//@ invariant other != l ==> other.Mem() && other.Es() == oes0 && other.Vs() == ovs0
	//@ invariant l.Vs() == vs0 ++ ovs0[:len(oes0)-i]
	//@ invariant l.Es()[:len(es0)] == es0
	//@ invariant len(l.Es()) == len(es0) + len(oes0) - i
	//@ invariant i > 0 ==> e == oes0[len(oes0)-i]
	//@ invariant i > 0 && other == l ==> len(oes0)-i < len(l.Es()) && l.Es()[len(oes0)-i] == e
	//@ decreases i
	for i, e := other.Len(), other.Front(); i > 0; i, e = i-1, e.Next( /*@ other, len(oes0)-i @*/ ) {
		//@ ghost if other != l { unfold other.Mem() }
		//@ ghost if other == l { unfold l.Mem() }
		v := e.Value
		//@ ghost if other != l { fold other.Mem() }
		//@ ghost if other == l { fold l.Mem() }
		//@ assert v === ovs0[len(oes0)-i]
		//@ unfold l.Mem()
		at := l.root.prev
		//@ ghost var n int = len(l.es)
		//@ fold l.Mem()
		l.insertValue(v, at /*@ , n-1 @*/)
	}
}

// PushFrontList inserts a copy of another list at the front of list l.
// The lists l and other may be the same. They must not be nil.
// @ preserves l.Mem()
// @ requires  other != l ==> other.Mem()
// @ ensures   l.Ini()
// @ ensures   l.Vs() == old(other.Vs()) ++ old(l.Vs())
// @ ensures   l.Es()[len(l.Es())-len(old(l.Es())):] == old(l.Es())
// @ ensures   other != l ==> other.Mem() && other.Es() == old(other.Es()) && other.Vs() == old(other.Vs())
// @ decreases
func (l *List) PushFrontList(other *List) {
	//@ ghost var es0 seq[*Element] = l.Es()
	//@ ghost var vs0 seq[any] = l.Vs()
	//@ ghost var oes0 seq[*Element] = other.Es()
	//@ ghost var ovs0 seq[any] = other.Vs()
	//@ assert len(es0) == len(vs0) && len(oes0) == len(ovs0)
	//@ assert other == l ==> es0 == oes0 && vs0 == ovs0
	l.lazyInit()
	//@ invariant len(es0) == len(vs0) && len(oes0) == len(ovs0)
	//@ invariant other == l ==> es0 == oes0 && vs0 == ovs0
	//@ invariant 0 <= i && i <= len(oes0)
	//@ invariant l.Mem() && l.Ini()
	//@ invariant other != l ==> other.Mem() && other.Es() == oes0 && other.Vs() == ovs0
	//@ invariant l.Vs() == ovs0[i:] ++ vs0
	//@ invariant len(l.Es()) == len(es0) + len(oes0) - i
	//@ invariant l.Es()[len(oes0)-i:] == es0
	//@ invariant i > 0 ==> e == oes0[i-1]
	//@ invariant i > 0 && other == l ==> len(oes0)-1 < len(l.Es()) && l.Es()[len(oes0)-1] == e
	//@ decreases i
	for i, e := other.Len(), other.Back(); i > 0; i, e = i-1, e.Prev( /*@ other, other == l ? len(oes0) : i-1 @*/ ) {
		//@ ghost if other != l { unfold other.Mem() }
		//@ ghost if other == l { unfold l.Mem() }
		v := e.Value
		//@ ghost if other != l { fold other.Mem() }
		//@ ghost if other == l { fold l.Mem() }
		//@ assert v === ovs0[i-1]
		l.insertValue(v, &l.root /*@ , -1 @*/)
		// the insertion prepended one element, so when other is l the index
		// of e inside l shifted up by one
		//@ assert other == l ==> len(oes0) < len(l.Es()) && l.Es()[len(oes0)] == e
	}
}
