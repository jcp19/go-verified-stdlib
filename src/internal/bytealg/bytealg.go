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
//@ ensures rhash == RKHash(seq(sep))
//@ ensures rpow == PowRK(PrimeRK, len(sep))
//@ decreases
func HashStrBytes(sep []byte /*@ , ghost p perm @*/) (rhash, rpow uint32) {
	hash := uint32(0)
	//@ invariant 0 <= i && i <= len(sep)
	//@ invariant acc(sep, p)
	//@ invariant seq(sep) == old(seq(sep))
	//@ invariant hash == RKHashRange(seq(sep), 0, i)
	//@ decreases len(sep) - i
	for i := 0; i < len(sep); i++ {
		//@ assert seq(sep)[i] == sep[i]
		hash = hash*PrimeRK + uint32(sep[i])
	}
	var pow, sq uint32 = 1, PrimeRK
	//@ invariant acc(sep, p)
	//@ invariant seq(sep) == old(seq(sep))
	//@ invariant 0 <= i
	//@ invariant pow*PowRK(sq, i) == PowRK(PrimeRK, len(sep))
	//@ decreases i
	for i := len(sep); i > 0; i >>= 1 {
		//@ lemmaBitFacts(i)
		//@ ghost if i&1 != 0 { lemmaPowRKOdd(sq, i/2) } else { lemmaPowRKEven(sq, i/2) }
		if i&1 != 0 {
			pow *= sq
		}
		sq *= sq
	}
	return hash, pow
}

// HashStr returns the hash and the appropriate multiplicative
// factor for use in Rabin-Karp algorithm.
//@ ensures rhash == RKHashStr(sep, 0, len(sep))
//@ ensures rpow == PowRK(PrimeRK, len(sep))
//@ decreases
func HashStr(sep string) (rhash, rpow uint32) {
	hash := uint32(0)
	//@ invariant 0 <= i && i <= len(sep)
	//@ invariant hash == RKHashStr(sep, 0, i)
	//@ decreases len(sep) - i
	for i := 0; i < len(sep); i++ {
		hash = hash*PrimeRK + uint32(sep[i])
	}
	var pow, sq uint32 = 1, PrimeRK
	//@ invariant 0 <= i
	//@ invariant pow*PowRK(sq, i) == PowRK(PrimeRK, len(sep))
	//@ decreases i
	for i := len(sep); i > 0; i >>= 1 {
		//@ lemmaBitFacts(i)
		//@ ghost if i&1 != 0 { lemmaPowRKOdd(sq, i/2) } else { lemmaPowRKEven(sq, i/2) }
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
//@ ensures rhash == RKHashRev(seq(sep))
//@ ensures rpow == PowRK(PrimeRK, len(sep))
//@ decreases
func HashStrRevBytes(sep []byte /*@ , ghost p perm @*/) (rhash, rpow uint32) {
	hash := uint32(0)
	//@ invariant -1 <= i && i <= len(sep)-1
	//@ invariant acc(sep, p)
	//@ invariant seq(sep) == old(seq(sep))
	//@ invariant hash == RKHashRevRange(seq(sep), i+1, len(sep))
	//@ decreases i + 1
	for i := len(sep) - 1; i >= 0; i-- {
		//@ assert seq(sep)[i] == sep[i]
		hash = hash*PrimeRK + uint32(sep[i])
	}
	var pow, sq uint32 = 1, PrimeRK
	//@ invariant acc(sep, p)
	//@ invariant seq(sep) == old(seq(sep))
	//@ invariant 0 <= i
	//@ invariant pow*PowRK(sq, i) == PowRK(PrimeRK, len(sep))
	//@ decreases i
	for i := len(sep); i > 0; i >>= 1 {
		//@ lemmaBitFacts(i)
		//@ ghost if i&1 != 0 { lemmaPowRKOdd(sq, i/2) } else { lemmaPowRKEven(sq, i/2) }
		if i&1 != 0 {
			pow *= sq
		}
		sq *= sq
	}
	return hash, pow
}

// HashStrRev returns the hash of the reverse of sep and the
// appropriate multiplicative factor for use in Rabin-Karp algorithm.
//@ ensures rhash == RKHashStrRev(sep, 0, len(sep))
//@ ensures rpow == PowRK(PrimeRK, len(sep))
//@ decreases
func HashStrRev(sep string) (rhash, rpow uint32) {
	hash := uint32(0)
	//@ invariant -1 <= i && i <= len(sep)-1
	//@ invariant hash == RKHashStrRev(sep, i+1, len(sep))
	//@ decreases i + 1
	for i := len(sep) - 1; i >= 0; i-- {
		hash = hash*PrimeRK + uint32(sep[i])
	}
	var pow, sq uint32 = 1, PrimeRK
	//@ invariant 0 <= i
	//@ invariant pow*PowRK(sq, i) == PowRK(PrimeRK, len(sep))
	//@ decreases i
	for i := len(sep); i > 0; i >>= 1 {
		//@ lemmaBitFacts(i)
		//@ ghost if i&1 != 0 { lemmaPowRKOdd(sq, i/2) } else { lemmaPowRKEven(sq, i/2) }
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
//@ ensures seq(s) == old(seq(s)) && seq(sep) == old(seq(sep))
//@ ensures res == -1 ==> NoMatchBefore(seq(s), seq(sep), len(s)-len(sep)+1)
//@ ensures res != -1 ==> 0 <= res && res <= len(s)-len(sep) && MatchesAt(seq(s), seq(sep), res)
//@ ensures res != -1 ==> NoMatchBefore(old(seq(s)), old(seq(sep)), res)
//@ decreases
func IndexRabinKarpBytes(s, sep []byte /*@ , ghost p perm @*/) (res int) {
	// Rabin-Karp search
	hashsep, pow := HashStrBytes(sep /*@ , p/2 @*/)
	n := len(sep)
	var h uint32
	//@ invariant 0 <= i && i <= n
	//@ invariant acc(s, p) && acc(sep, p)
	//@ invariant seq(s) == old(seq(s)) && seq(sep) == old(seq(sep))
	//@ invariant hashsep == RKHash(seq(sep)) && pow == PowRK(PrimeRK, n)
	//@ invariant h == RKHashRange(seq(s), 0, i)
	//@ decreases n - i
	for i := 0; i < n; i++ {
		//@ assert seq(s)[i] == s[i]
		h = h*PrimeRK + uint32(s[i])
	}
	//@ assert forall k int :: {&s[:n][k]} 0 <= k && k < n ==> &s[:n][k] == &s[k]
	//@ assert forall k int :: {seq(s[:n])[k]} 0 <= k && k < n ==> seq(s[:n])[k] == seq(s)[:n][k]
	//@ assert seq(s[:n]) == seq(s)[:n]
	//@ assert seq(s)[0:n] == seq(s)[:n]
	if h == hashsep && Equal(s[:n], sep) {
		//@ assert seq(s)[0:n] == seq(sep)
		//@ assert MatchesAt(seq(s), seq(sep), 0)
		//@ lemmaNoMatchBeforeZero(old(seq(s)), old(seq(sep)))
		return 0
	}
	//@ ghost if h != hashsep { lemmaMatchesAtFalseHash(seq(s), seq(sep), 0) } else { lemmaMatchesAtFalseNeq(seq(s), seq(sep), 0) }
	//@ assert len(seq(s)) == len(s) && len(seq(sep)) == len(sep)
	//@ assert !MatchesAt(seq(s), seq(sep), 0)
	//@ assert reveal NoMatchBefore(seq(s), seq(sep), 0)
	//@ assert reveal NoMatchBefore(seq(s), seq(sep), 1)
	//@ invariant 0 < n
	//@ invariant n <= i && i <= len(s)
	//@ invariant acc(s, p) && acc(sep, p)
	//@ invariant seq(s) == old(seq(s)) && seq(sep) == old(seq(sep))
	//@ invariant hashsep == RKHash(seq(sep)) && pow == PowRK(PrimeRK, n)
	//@ invariant h == RKHashRange(seq(s), i-n, i)
	//@ invariant NoMatchBefore(seq(s), seq(sep), i-n+1)
	//@ decreases len(s) - i
	for i := n; i < len(s); {
		h *= PrimeRK
		h += uint32(s[i])
		h -= pow * uint32(s[i-n])
		i++
		//@ assert forall k int :: {&s[i-n:i][k]} 0 <= k && k < n ==> &s[i-n:i][k] == &s[i-n+k]
		//@ assert forall k int :: {seq(s[i-n:i])[k]} 0 <= k && k < n ==> seq(s[i-n:i])[k] == seq(s)[i-n:i][k]
		//@ assert seq(s[i-n:i]) == seq(s)[i-n:i]
		if h == hashsep && Equal(s[i-n:i], sep) {
			//@ assert seq(s)[i-n:i] == seq(sep)
			//@ assert MatchesAt(seq(s), seq(sep), i-n)
			//@ assert NoMatchBefore(seq(s), seq(sep), i-n)
			//@ assert seq(s) == old(seq(s)) && seq(sep) == old(seq(sep))
			//@ assert NoMatchBefore(old(seq(s)), old(seq(sep)), i-n)
			return i - n
		}
		//@ assert seq(s)[i-1-n] == s[i-1-n] && seq(s)[i-1] == s[i-1]
		//@ lemmaRKHashRangeRoll(seq(s), n, i-1)
		//@ ghost if h != hashsep { lemmaMatchesAtFalseHash(seq(s), seq(sep), i-n) } else { lemmaMatchesAtFalseNeq(seq(s), seq(sep), i-n) }
		//@ assert reveal NoMatchBefore(seq(s), seq(sep), i-n+1)
	}
	//@ assert NoMatchBefore(seq(s), seq(sep), len(s)-len(sep)+1)
	return -1
}

// IndexRabinKarp uses the Rabin-Karp search algorithm to return the index of the
// first occurrence of substr in s, or -1 if not present.
//
// Note on the specification: Gobra models strings abstractly, so the
// postconditions are stated in terms of StrMatchesAt, which captures exactly
// the test performed by this function (matching window hash and successful
// string comparison); see spec.gobra.
//@ requires len(substr) <= len(s)
//@ ensures res == -1 ==> forall j int :: {StrMatchesAt(s, substr, j)} 0 <= j && j <= len(s)-len(substr) ==> !StrMatchesAt(s, substr, j)
//@ ensures res != -1 ==> 0 <= res && res <= len(s)-len(substr) && StrMatchesAt(s, substr, res)
//@ ensures res != -1 ==> forall j int :: {StrMatchesAt(s, substr, j)} 0 <= j && j < res ==> !StrMatchesAt(s, substr, j)
//@ decreases
func IndexRabinKarp(s, substr string) (res int) {
	// Rabin-Karp search
	hashss, pow := HashStr(substr)
	n := len(substr)
	var h uint32
	//@ invariant 0 <= i && i <= n
	//@ invariant h == RKHashStr(s, 0, i)
	//@ decreases n - i
	for i := 0; i < n; i++ {
		h = h*PrimeRK + uint32(s[i])
	}
	if h == hashss && s[:n] == substr {
		//@ assert StrMatchesAt(s, substr, 0)
		return 0
	}
	//@ assert !StrMatchesAt(s, substr, 0)
	//@ invariant n <= i && i <= len(s)
	//@ invariant h == RKHashStr(s, i-n, i)
	//@ invariant forall j int :: {StrMatchesAt(s, substr, j)} 0 <= j && j <= i-n ==> !StrMatchesAt(s, substr, j)
	//@ decreases len(s) - i
	for i := n; i < len(s); {
		//@ ghost if 0 < n { lemmaRKHashStrDropFirst(s, i-n, i) }
		h *= PrimeRK
		h += uint32(s[i])
		h -= pow * uint32(s[i-n])
		i++
		//@ assert h == RKHashStr(s, i-n, i)
		if h == hashss && s[i-n:i] == substr {
			//@ assert StrMatchesAt(s, substr, i-n)
			return i - n
		}
		//@ assert !StrMatchesAt(s, substr, i-n)
	}
	return -1
}
