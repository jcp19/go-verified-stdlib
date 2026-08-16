// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Enables Gobra in the current file.
// +gobra

// Package sync provides basic synchronization primitives such as mutual
// exclusion locks. Other than the Once and WaitGroup types, most are intended
// for use by low-level library routines. Higher-level synchronization is
// better done via channels and communication.
//
// Values containing the types defined in this package should not be copied.
package sync

import (
	"internal/race"
	atomics "sync/atomic" // aliased: `atomic` is a reserved word in Gobra
	"unsafe"
)

// throw reports a fatal, unrecoverable runtime error. `requires false` is the
// contract Gobra's builtin package gives to panic: a correct program never
// reaches it. Proving that is part of what is verified below -- the mutex never
// reports an inconsistent state.
//@ requires false
//@ decreases
func throw(string) // provided by runtime

// A Mutex is a mutual exclusion lock.
// The zero value for a Mutex is an unlocked mutex.
//
// A Mutex must not be copied after first use.
type Mutex struct {
	state int32
	sema  uint32

	// Ghost state. See mutex.gobra for what these track.
	//@ ghost inv option[pred()] // the resource the mutex protects
	//@ ghost gl  bool           // mutexLocked is set / UnlockP is out
	//@ ghost gw  bool           // mutexWoken is set / AwokeP is out
	//@ ghost gh  bool           // an ownership handoff is parked in the invariant
	//@ ghost ghc bool           // a handoff has been claimed but not yet installed
	//@ ghost ghn int32          // waiter count when that handoff was claimed
	//@ ghost gws bool           // the awoke token is parked in the invariant
	//@ ghost gt  bool           // permission carrier for semaphore tickets
}

// A Locker represents an object that can be locked and unlocked.
type Locker interface {
	Lock()
	Unlock()
}

const (
	mutexLocked = 1 << iota // mutex is locked
	mutexWoken
	mutexStarving
	mutexWaiterShift = iota

	// Mutex fairness.
	//
	// Mutex can be in 2 modes of operations: normal and starvation.
	// In normal mode waiters are queued in FIFO order, but a woken up waiter
	// does not own the mutex and competes with new arriving goroutines over
	// the ownership. New arriving goroutines have an advantage -- they are
	// already running on CPU and there can be lots of them, so a woken up
	// waiter has good chances of losing. In such case it is queued at front
	// of the wait queue. If a waiter fails to acquire the mutex for more than 1ms,
	// it switches mutex to the starvation mode.
	//
	// In starvation mode ownership of the mutex is directly handed off from
	// the unlocking goroutine to the waiter at the front of the queue.
	// New arriving goroutines don't try to acquire the mutex even if it appears
	// to be unlocked, and don't try to spin. Instead they queue themselves at
	// the tail of the wait queue.
	//
	// If a waiter receives ownership of the mutex and sees that either
	// (1) it is the last waiter in the queue, or (2) it waited for less than 1 ms,
	// it switches mutex back to normal operation mode.
	//
	// Normal mode has considerably better performance as a goroutine can acquire
	// a mutex several times in a row even if there are blocked waiters.
	// Starvation mode is important to prevent pathological cases of tail latency.
	starvationThresholdNs = 1000000 // 1e6; Gobra does not support float literals
)

// Lock locks m.
// If the lock is already in use, the calling goroutine
// blocks until the mutex is available.
// The contract below is the one from Gobra's own model of this package,
// src/main/resources/stubs/sync/mutex.gobra, minus its secure-information-flow
// precondition `lowContext()`, which is out of scope here (see GOBRA-REPORT.md).
//@ requires acc(m.LockP(), _)
//@ ensures  m.LockP() && m.UnlockP() && m.LockInv()()
func (m *Mutex) Lock() {
	//@ m.lockPInv()
	// Fast path: grab unlocked mutex.
	// statep and swapped are hoisted out of the CAS: Gobra only accepts
	// variables and literals as arguments of an atomic call inside a critical
	// region, and only an assignment (not a declaration) as its statement.
	statep := &m.state
	var swapped bool
	//@ critical mutexInv{m} (
	//@ unfold mutexInv{m}()
	//@ bitsLemma(m.state)
	swapped = atomics.CompareAndSwapInt32(statep, 0, mutexLocked)
	//@ ghost if swapped {
	//@ 	// The word was 0, so the mutex was logically free and the invariant
	//@ 	// handed over the protected resource; mint the ownership token.
	//@ 	bitsOf(m.state, 1, 0, 0, 0)
	//@ 	m.gl = true
	//@ 	fold m.UnlockP()
	//@ }
	//@ fold mutexInv{m}()
	//@ )
	if swapped {
		if race.Enabled {
			race.Acquire(unsafe.Pointer(m))
		}
		return
	}
	// Slow path (outlined so that the fast path can be inlined)
	m.lockSlow()
}

// TryLock tries to lock m and reports whether it succeeded.
//
// Note that while correct uses of TryLock do exist, they are rare,
// and use of TryLock is often a sign of a deeper problem
// in a particular use of mutexes.
//@ requires acc(m.LockP(), _)
//@ ensures  m.LockP()
//@ ensures  res ==> m.UnlockP() && m.LockInv()()
//@ decreases
func (m *Mutex) TryLock() (res bool) {
	//@ m.lockPInv()
	statep := &m.state
	var oldv int32
	//@ critical mutexInv{m} (
	//@ unfold mutexInv{m}()
	oldv = atomics.LoadInt32(statep /*@, writePerm @*/)
	//@ fold mutexInv{m}()
	//@ )
	//@ bitsLemma(oldv)
	if oldv&(mutexLocked|mutexStarving) != 0 {
		return false
	}

	// There may be a goroutine waiting for the mutex, but we are
	// running now and can try to grab the mutex before that
	// goroutine wakes up.
	locked := oldv | mutexLocked
	var swapped bool
	//@ critical mutexInv{m} (
	//@ unfold mutexInv{m}()
	//@ bitsLemma(m.state)
	swapped = atomics.CompareAndSwapInt32(statep, oldv, locked)
	//@ ghost if swapped {
	//@ 	bitsOf(locked, 1, bitWoken(oldv), 0, numWaiters(oldv))
	//@ 	m.gl = true
	//@ 	fold m.UnlockP()
	//@ }
	//@ fold mutexInv{m}()
	//@ )
	if !swapped {
		return false
	}

	if race.Enabled {
		race.Acquire(unsafe.Pointer(m))
	}
	return true
}

// WORK IN PROGRESS: lockSlow carries the contract it must satisfy, but is still
// marked `trusted` -- its body is not yet verified. Everything else in this file
// is verified against the contracts shown.
// TODO(claude): discharge this and drop `trusted`.
//@ trusted
//@ requires acc(m.LockP(), _)
//@ ensures  m.LockP() && m.UnlockP() && m.LockInv()()
func (m *Mutex) lockSlow() {
	var waitStartTime int64
	starving := false
	awoke := false
	iter := 0
	oldv := m.state
	for {
		// Don't spin in starvation mode, ownership is handed off to waiters
		// so we won't be able to acquire the mutex anyway.
		if oldv&(mutexLocked|mutexStarving) == mutexLocked && runtime_canSpin(iter) {
			// Active spinning makes sense.
			// Try to set mutexWoken flag to inform Unlock
			// to not wake other blocked goroutines.
			if !awoke && oldv&mutexWoken == 0 && oldv>>mutexWaiterShift != 0 &&
				atomics.CompareAndSwapInt32(&m.state, oldv, oldv|mutexWoken) {
				awoke = true
			}
			runtime_doSpin()
			iter++
			oldv = m.state
			continue
		}
		newv := oldv
		// Don't try to acquire starving mutex, new arriving goroutines must queue.
		if oldv&mutexStarving == 0 {
			newv |= mutexLocked
		}
		if oldv&(mutexLocked|mutexStarving) != 0 {
			newv += 1 << mutexWaiterShift
		}
		// The current goroutine switches mutex to starvation mode.
		// But if the mutex is currently unlocked, don't do the switch.
		// Unlock expects that starving mutex has waiters, which will not
		// be true in this case.
		if starving && oldv&mutexLocked != 0 {
			newv |= mutexStarving
		}
		if awoke {
			// The goroutine has been woken from sleep,
			// so we need to reset the flag in either case.
			if newv&mutexWoken == 0 {
				throw("sync: inconsistent mutex state")
			}
			newv &^= mutexWoken
		}
		if atomics.CompareAndSwapInt32(&m.state, oldv, newv) {
			if oldv&(mutexLocked|mutexStarving) == 0 {
				break // locked the mutex with CAS
			}
			// If we were already waiting before, queue at the front of the queue.
			queueLifo := waitStartTime != 0
			if waitStartTime == 0 {
				waitStartTime = runtime_nanotime()
			}
			runtime_SemacquireMutex(&m.sema, queueLifo, 1)
			starving = starving || runtime_nanotime()-waitStartTime > starvationThresholdNs
			oldv = m.state
			if oldv&mutexStarving != 0 {
				// If this goroutine was woken and mutex is in starvation mode,
				// ownership was handed off to us but mutex is in somewhat
				// inconsistent state: mutexLocked is not set and we are still
				// accounted as waiter. Fix that.
				if oldv&(mutexLocked|mutexWoken) != 0 || oldv>>mutexWaiterShift == 0 {
					throw("sync: inconsistent mutex state")
				}
				delta := int32(mutexLocked - 1<<mutexWaiterShift)
				if !starving || oldv>>mutexWaiterShift == 1 {
					// Exit starvation mode.
					// Critical to do it here and consider wait time.
					// Starvation mode is so inefficient, that two goroutines
					// can go lock-step infinitely once they switch mutex
					// to starvation mode.
					delta -= mutexStarving
				}
				atomics.AddInt32(&m.state, delta)
				break
			}
			awoke = true
			iter = 0
		} else {
			oldv = m.state
		}
	}

	if race.Enabled {
		race.Acquire(unsafe.Pointer(m))
	}
}

// Unlock unlocks m.
// It is a run-time error if m is not locked on entry to Unlock.
//
// A locked Mutex is not associated with a particular goroutine.
// It is allowed for one goroutine to lock a Mutex and then
// arrange for another goroutine to unlock it.
// The contract below is the one from Gobra's own model of this package,
// src/main/resources/stubs/sync/mutex.gobra, minus its secure-information-flow
// precondition `lowContext()`, which is out of scope here (see GOBRA-REPORT.md).
//@ requires acc(m.LockP(), _) && m.UnlockP() && m.LockInv()()
//@ ensures  m.LockP()
//@ decreases
func (m *Mutex) Unlock() {
	if race.Enabled {
		_ = m.state
		race.Release(unsafe.Pointer(m))
	}

	//@ m.lockPInv()
	// Fast path: drop lock bit.
	statep := &m.state
	unlockDelta := int32(-mutexLocked)
	var newv int32
	//@ ghost var w0, s0, n0 int32
	//@ critical mutexInv{m} (
	//@ unfold mutexInv{m}()
	//@ unfold m.UnlockP()
	//@ // Holding UnlockP pins mutexLocked: the token is out, so the bit is set.
	//@ bitsLemma(m.state)
	//@ ghost w0, s0, n0 = bitWoken(m.state), bitStarving(m.state), numWaiters(m.state)
	newv = atomics.AddInt32(statep, unlockDelta)
	//@ bitsOf(m.state, 0, w0, s0, n0)
	//@ ghost m.gl = false
	//@ ghost if s0 == 1 {
	//@ 	// Starvation mode: ownership is not released into the invariant but
	//@ 	// handed to the waiter that redeems the ticket minted here.
	//@ 	m.gh = true
	//@ 	fold semTicket{m}()
	//@ }
	//@ fold mutexInv{m}()
	//@ )
	if newv != 0 {
		// Outlined slow path to allow inlining the fast path.
		// To hide unlockSlow during tracing we skip one extra frame when tracing GoUnblock.
		m.unlockSlow(newv)
	}
}

//@ requires acc(m.LockP(), _)
//@ requires 0 <= newv && bitLocked(newv) == 0
//@ requires bitStarving(newv) == 1 ==> semTicket{m}()
//@ ensures  m.LockP()
//@ decreases _
func (m *Mutex) unlockSlow(newv int32) {
	//@ m.lockPInv()
	//@ bitsLemma(newv)
	//@ bitsOf(newv+mutexLocked, 1, bitWoken(newv), bitStarving(newv), numWaiters(newv))
	if (newv+mutexLocked)&mutexLocked == 0 {
		throw("sync: unlock of unlocked mutex")
	}
	statep := &m.state
	if newv&mutexStarving == 0 {
		oldv := newv
		//@ invariant m.LockP()
		//@ invariant 0 <= oldv
		//@ decreases _
		for {
			// If there are no waiters or a goroutine has already
			// been woken or grabbed the lock, no need to wake anyone.
			// In starvation mode ownership is directly handed off from unlocking
			// goroutine to the next waiter. We are not part of this chain,
			// since we did not observe mutexStarving when we unlocked the mutex above.
			// So get off the way.
			if oldv>>mutexWaiterShift == 0 || oldv&(mutexLocked|mutexWoken|mutexStarving) != 0 {
				return
			}
			// Grab the right to wake someone.
			//@ bitsLemma(oldv)
			newv = (oldv - 1<<mutexWaiterShift) | mutexWoken
			//@ bitsOf(oldv-1<<mutexWaiterShift, 0, 0, 0, numWaiters(oldv)-1)
			//@ bitsLemma(oldv - 1<<mutexWaiterShift)
			//@ bitsOf(newv, 0, 1, 0, numWaiters(oldv)-1)
			var swapped bool
			//@ critical mutexInv{m} (
			//@ unfold mutexInv{m}()
			swapped = atomics.CompareAndSwapInt32(statep, oldv, newv)
			//@ ghost if swapped {
			//@ 	// We took the right to wake someone: set mutexWoken, park the
			//@ 	// AwokeP token and mint the ticket that hands it over.
			//@ 	m.gw = true
			//@ 	m.gws = true
			//@ 	fold semTicket{m}()
			//@ }
			//@ fold mutexInv{m}()
			//@ )
			if swapped {
				//@ m.lockPInv()
				runtime_Semrelease(&m.sema, false, 1)
				return
			}
			//@ critical mutexInv{m} (
			//@ unfold mutexInv{m}()
			oldv = atomics.LoadInt32(statep /*@, writePerm @*/)
			//@ fold mutexInv{m}()
			//@ )
		}
	} else {
		// Starving mode: handoff mutex ownership to the next waiter, and yield
		// our time slice so that the next waiter can start to run immediately.
		// Note: mutexLocked is not set, the waiter will set it after wakeup.
		// But mutex is still considered locked if mutexStarving is set,
		// so new coming goroutines won't acquire it.
		runtime_Semrelease(&m.sema, true, 1)
	}
}
