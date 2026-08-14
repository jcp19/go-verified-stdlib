// Copyright 2018 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Enables Gobra in the current file.
// +gobra

package bytealg

// NOTE(gobra): the "Offsets into internal/cpu records" constant block and the
// imports of internal/cpu and unsafe were moved, unchanged, to offsets.go:
// unsafe.Offsetof is not supported by Gobra. See offsets.go.

// MaxLen is the maximum length of the string to be searched for (argument b) in Index.
// If MaxLen is not 0, make sure MaxLen >= 4.
var MaxLen int

// FIXME: the logic of HashStrBytes, HashStrRevBytes, IndexRabinKarpBytes and HashStr, HashStrRev,
// IndexRabinKarp are exactly the same, except that the types are different. Can we eliminate
// three of them without causing allocation?

// PrimeRK is the prime base used in Rabin-Karp algorithm.
const PrimeRK = 16777619

// HashStrBytes returns the hash and the appropriate multiplicative
// factor for use in Rabin-Karp algorithm.
//@ requires p > 0
//@ preserves acc(sep, p)
func HashStrBytes(sep []byte /*@ , ghost p perm @*/) (uint32, uint32) {
	hash := uint32(0)
	//@ invariant 0 <= i && i <= len(sep)
	//@ invariant acc(sep, p)
	for i := 0; i < len(sep); i++ {
		hash = hash*PrimeRK + uint32(sep[i])
	}
	var pow, sq uint32 = 1, PrimeRK
	for i := len(sep); i > 0; i >>= 1 {
		if i&1 != 0 {
			pow *= sq
		}
		sq *= sq
	}
	return hash, pow
}

// HashStr returns the hash and the appropriate multiplicative
// factor for use in Rabin-Karp algorithm.
func HashStr(sep string) (uint32, uint32) {
	hash := uint32(0)
	//@ invariant 0 <= i && i <= len(sep)
	for i := 0; i < len(sep); i++ {
		hash = hash*PrimeRK + uint32(sep[i])
	}
	var pow, sq uint32 = 1, PrimeRK
	for i := len(sep); i > 0; i >>= 1 {
		if i&1 != 0 {
			pow *= sq
		}
		sq *= sq
	}
	return hash, pow
}

// HashStrRevBytes returns the hash of the reverse of sep and the
// appropriate multiplicative factor for use in Rabin-Karp algorithm.
//@ requires p > 0
//@ preserves acc(sep, p)
func HashStrRevBytes(sep []byte /*@ , ghost p perm @*/) (uint32, uint32) {
	hash := uint32(0)
	//@ invariant -1 <= i && i <= len(sep)-1
	//@ invariant acc(sep, p)
	for i := len(sep) - 1; i >= 0; i-- {
		hash = hash*PrimeRK + uint32(sep[i])
	}
	var pow, sq uint32 = 1, PrimeRK
	for i := len(sep); i > 0; i >>= 1 {
		if i&1 != 0 {
			pow *= sq
		}
		sq *= sq
	}
	return hash, pow
}

// HashStrRev returns the hash of the reverse of sep and the
// appropriate multiplicative factor for use in Rabin-Karp algorithm.
func HashStrRev(sep string) (uint32, uint32) {
	hash := uint32(0)
	//@ invariant -1 <= i && i <= len(sep)-1
	for i := len(sep) - 1; i >= 0; i-- {
		hash = hash*PrimeRK + uint32(sep[i])
	}
	var pow, sq uint32 = 1, PrimeRK
	for i := len(sep); i > 0; i >>= 1 {
		if i&1 != 0 {
			pow *= sq
		}
		sq *= sq
	}
	return hash, pow
}

// IndexRabinKarpBytes uses the Rabin-Karp search algorithm to return the index of the
// first occurrence of substr in s, or -1 if not present.
//@ requires p > 0
//@ requires len(sep) <= len(s)
//@ preserves acc(s, p) && acc(sep, p)
func IndexRabinKarpBytes(s, sep []byte /*@ , ghost p perm @*/) int {
	// Rabin-Karp search
	hashsep, pow := HashStrBytes(sep /*@ , p/2 @*/)
	n := len(sep)
	var h uint32
	//@ invariant 0 <= i && i <= n
	//@ invariant acc(s, p) && acc(sep, p)
	for i := 0; i < n; i++ {
		h = h*PrimeRK + uint32(s[i])
	}
	if h == hashsep && Equal(s[:n], sep) {
		return 0
	}
	//@ invariant n <= i && i <= len(s)
	//@ invariant acc(s, p) && acc(sep, p)
	for i := n; i < len(s); {
		h *= PrimeRK
		h += uint32(s[i])
		h -= pow * uint32(s[i-n])
		i++
		//@ assert forall k int :: {&s[i-n:i][k]} 0 <= k && k < n ==> &s[i-n:i][k] == &s[i-n+k]
		if h == hashsep && Equal(s[i-n:i], sep) {
			return i - n
		}
	}
	return -1
}

// IndexRabinKarp uses the Rabin-Karp search algorithm to return the index of the
// first occurrence of substr in s, or -1 if not present.
//@ requires len(substr) <= len(s)
func IndexRabinKarp(s, substr string) int {
	// Rabin-Karp search
	hashss, pow := HashStr(substr)
	n := len(substr)
	var h uint32
	//@ invariant 0 <= i && i <= n
	for i := 0; i < n; i++ {
		h = h*PrimeRK + uint32(s[i])
	}
	if h == hashss && s[:n] == substr {
		return 0
	}
	//@ invariant n <= i && i <= len(s)
	for i := n; i < len(s); {
		h *= PrimeRK
		h += uint32(s[i])
		h -= pow * uint32(s[i-n])
		i++
		if h == hashss && s[i-n:i] == substr {
			return i - n
		}
	}
	return -1
}
