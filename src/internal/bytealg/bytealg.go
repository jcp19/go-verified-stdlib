// Copyright 2018 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Enables Gobra in the current file.
// +gobra

package bytealg

// (Gobra) The "Offsets into internal/cpu records" constant block and the
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
// @ requires  p > 0
// @ preserves acc(sep, p)
// @ ensures   rhash == RKHash(seq(sep))
// @ ensures   rpow == PowRK(PrimeRK, len(sep))
// @ decreases
func HashStrBytes(sep []byte /*@ , ghost p perm @*/) (rhash, rpow uint32) {
	hash := uint32(0)
	//@ invariant 0 <= i && i <= len(sep)
	//@ invariant acc(sep, p/2)
	//@ invariant hash == RKHashRange(seq(sep), 0, i)
	//@ decreases len(sep) - i
	for i := 0; i < len(sep); i++ {
		//@ assert seq(sep)[i] == sep[i]
		//@ lemmaRKHashRangeStep(seq(sep), 0, i+1)
		hash = hash*PrimeRK + uint32(sep[i])
	}
	var pow, sq uint32 = 1, PrimeRK
	//@ lemmaPowRKMulStart(PrimeRK, len(sep))
	//@ invariant acc(sep, p/2)
	//@ invariant 0 <= i
	//@ invariant hash == RKHashRange(seq(sep), 0, len(sep))
	//@ invariant PowRKMul(pow, sq, i) == PowRK(PrimeRK, len(sep))
	//@ decreases i
	for i := len(sep); i > 0; i >>= 1 {
		//@ lemmaBitFacts(i)
		// (Gobra) sq0 and pow0 snapshot the pre-step values so that the step
		// lemma below can be applied after the assignments, in the loop's own
		// post-state terms; see lemmaPowRKMulStep.
		//@ ghost sq0 := sq
		//@ ghost pow0 := pow
		if i&1 != 0 {
			pow *= sq
		}
		sq *= sq
		//@ lemmaPowRKMulStep(pow0, pow, sq0, sq, i, i>>1)
	}
	//@ lemmaPowRKMulEnd(pow, sq)
	return hash, pow
}

// HashStr returns the hash and the appropriate multiplicative
// factor for use in Rabin-Karp algorithm.
// @ ensures   rhash == RKHashStr(sep, 0, len(sep))
// @ ensures   rpow == PowRK(PrimeRK, len(sep))
// @ decreases
func HashStr(sep string) (rhash, rpow uint32) {
	hash := uint32(0)
	//@ invariant 0 <= i && i <= len(sep)
	//@ invariant hash == RKHashStr(sep, 0, i)
	//@ decreases len(sep) - i
	for i := 0; i < len(sep); i++ {
		//@ lemmaRKHashStrStep(sep, 0, i+1)
		hash = hash*PrimeRK + uint32(sep[i])
	}
	var pow, sq uint32 = 1, PrimeRK
	//@ lemmaPowRKMulStart(PrimeRK, len(sep))
	//@ invariant 0 <= i
	//@ invariant PowRKMul(pow, sq, i) == PowRK(PrimeRK, len(sep))
	//@ decreases i
	for i := len(sep); i > 0; i >>= 1 {
		//@ lemmaBitFacts(i)
		// (Gobra) sq0 and pow0 snapshot the pre-step values so that the step
		// lemma below can be applied after the assignments, in the loop's own
		// post-state terms; see lemmaPowRKMulStep.
		//@ ghost sq0 := sq
		//@ ghost pow0 := pow
		if i&1 != 0 {
			pow *= sq
		}
		sq *= sq
		//@ lemmaPowRKMulStep(pow0, pow, sq0, sq, i, i>>1)
	}
	//@ lemmaPowRKMulEnd(pow, sq)
	return hash, pow
}

// HashStrRevBytes returns the hash of the reverse of sep and the
// appropriate multiplicative factor for use in Rabin-Karp algorithm.
// @ requires  p > 0
// @ preserves acc(sep, p)
// @ ensures   rhash == RKHashRev(seq(sep))
// @ ensures   rpow == PowRK(PrimeRK, len(sep))
// @ decreases
func HashStrRevBytes(sep []byte /*@ , ghost p perm @*/) (rhash, rpow uint32) {
	hash := uint32(0)
	//@ invariant -1 <= i && i <= len(sep)-1
	//@ invariant acc(sep, p/2)
	//@ invariant hash == RKHashRevRange(seq(sep), i+1, len(sep))
	//@ decreases i + 1
	for i := len(sep) - 1; i >= 0; i-- {
		//@ assert seq(sep)[i] == sep[i]
		//@ lemmaRKHashRevRangeStep(seq(sep), i, len(sep))
		hash = hash*PrimeRK + uint32(sep[i])
	}
	var pow, sq uint32 = 1, PrimeRK
	//@ lemmaPowRKMulStart(PrimeRK, len(sep))
	//@ invariant acc(sep, p/2)
	//@ invariant 0 <= i
	//@ invariant hash == RKHashRevRange(seq(sep), 0, len(sep))
	//@ invariant PowRKMul(pow, sq, i) == PowRK(PrimeRK, len(sep))
	//@ decreases i
	for i := len(sep); i > 0; i >>= 1 {
		//@ lemmaBitFacts(i)
		// (Gobra) sq0 and pow0 snapshot the pre-step values so that the step
		// lemma below can be applied after the assignments, in the loop's own
		// post-state terms; see lemmaPowRKMulStep.
		//@ ghost sq0 := sq
		//@ ghost pow0 := pow
		if i&1 != 0 {
			pow *= sq
		}
		sq *= sq
		//@ lemmaPowRKMulStep(pow0, pow, sq0, sq, i, i>>1)
	}
	//@ lemmaPowRKMulEnd(pow, sq)
	return hash, pow
}

// HashStrRev returns the hash of the reverse of sep and the
// appropriate multiplicative factor for use in Rabin-Karp algorithm.
// @ ensures   rhash == RKHashStrRev(sep, 0, len(sep))
// @ ensures   rpow == PowRK(PrimeRK, len(sep))
// @ decreases
func HashStrRev(sep string) (rhash, rpow uint32) {
	hash := uint32(0)
	//@ invariant -1 <= i && i <= len(sep)-1
	//@ invariant hash == RKHashStrRev(sep, i+1, len(sep))
	//@ decreases i + 1
	for i := len(sep) - 1; i >= 0; i-- {
		//@ lemmaRKHashStrRevStep(sep, i, len(sep))
		hash = hash*PrimeRK + uint32(sep[i])
	}
	var pow, sq uint32 = 1, PrimeRK
	//@ lemmaPowRKMulStart(PrimeRK, len(sep))
	//@ invariant 0 <= i
	//@ invariant PowRKMul(pow, sq, i) == PowRK(PrimeRK, len(sep))
	//@ decreases i
	for i := len(sep); i > 0; i >>= 1 {
		//@ lemmaBitFacts(i)
		// (Gobra) sq0 and pow0 snapshot the pre-step values so that the step
		// lemma below can be applied after the assignments, in the loop's own
		// post-state terms; see lemmaPowRKMulStep.
		//@ ghost sq0 := sq
		//@ ghost pow0 := pow
		if i&1 != 0 {
			pow *= sq
		}
		sq *= sq
		//@ lemmaPowRKMulStep(pow0, pow, sq0, sq, i, i>>1)
	}
	//@ lemmaPowRKMulEnd(pow, sq)
	return hash, pow
}

// IndexRabinKarpBytes uses the Rabin-Karp search algorithm to return the index of the
// first occurrence of substr in s, or -1 if not present.
// @ requires  p > 0
// @ requires  len(sep) <= len(s)
// @ preserves acc(s, p) && acc(sep, p)
// @ ensures   res != -1 ==> 0 <= res && res <= len(s)-len(sep)
// @ ensures   res != -1 ==> MatchesAt(seq(s), seq(sep), res)
// @ ensures   res != -1 ==> NoMatchBefore(seq(s), seq(sep), res)
// @ ensures   res == -1 ==> NoMatchBefore(seq(s), seq(sep), len(s)-len(sep)+1)
// @ decreases
func IndexRabinKarpBytes(s, sep []byte /*@ , ghost p perm @*/) (res int) {
	// Rabin-Karp search
	hashsep, pow := HashStrBytes(sep /*@ , p/2 @*/)
	n := len(sep)
	//@ assert hashsep == RKHashRange(seq(sep), 0, n)
	var h uint32
	//@ invariant 0 <= i && i <= n
	//@ invariant acc(s, p/2) && acc(sep, p/2)
	//@ invariant n == len(sep) && n <= len(s)
	//@ invariant hashsep == RKHashRange(seq(sep), 0, n) && pow == PowRK(PrimeRK, n)
	//@ invariant h == RKHashRange(seq(s), 0, i)
	//@ decreases n - i
	for i := 0; i < n; i++ {
		//@ lemmaRKHashRangeStep(seq(s), 0, i+1)
		h = h*PrimeRK + uint32(s[i])
	}
	// (Gobra) The second trigger is what carries this fact into the window
	// lemmas: the pointwise reasoning they do mentions seq(s)[k], never
	// &s[:n][k], so with the address pattern alone it would never fire.
	//@ assert forall k int :: {&s[:n][k]} {seq(s)[k]} 0 <= k && k < n ==> &s[:n][k] == &s[k]
	//@ lemmaNoMatchBeforeZero(seq(s), seq(sep))
	if h == hashsep && Equal(s[:n], sep) {
		//@ lemmaMatchesAtWindow(s, seq(sep), 0, n, p/4)
		return 0
	}
	// (Gobra) The test just failed, so either the hashes differ or the bytes
	// do; picking the disjunct here rather than passing a disjunction keeps
	// the resliced window out of the hash path. See lemmas.gobra.
	//@ ghost if h != hashsep {
	//@ 	lemmaNoMatchExtendWindowHash(seq(s), seq(sep), 0, n, h)
	//@ } else {
	//@ 	lemmaNoMatchExtendWindowBytes(s, seq(sep), 0, n, p/4)
	//@ }
	// (Gobra) qs and qsep pin the two byte sequences to ordinary ghost values
	// for the duration of the loop. The Equal call in the body exhales and
	// re-inhales a slice of s's quantified permission, and every mention of
	// seq(s) after that point has to be re-derived from a heap carrying pTaken
	// masks -- a fresh snapshot map over the whole slice. Stating the invariant
	// and the lemma calls over qs instead leaves exactly one such obligation
	// per iteration, the seq(s) == qs conjunct below, instead of one at every
	// use.
	//@ ghost qs := seq(s)
	//@ ghost qsep := seq(sep)
	//@ invariant 0 < n && n == len(sep)
	//@ invariant n <= i && i <= len(s)
	//@ invariant acc(s, p/2) && acc(sep, p/2)
	//@ invariant seq(s) == qs && seq(sep) == qsep
	//@ invariant hashsep == RKHashRange(qsep, 0, n) && pow == PowRK(PrimeRK, n)
	//@ invariant h == RKHashRange(qs, i-n, i)
	//@ invariant NoMatchBefore(qs, qsep, i-n+1)
	//@ decreases len(s) - i
	for i := n; i < len(s); {
		h *= PrimeRK
		h += uint32(s[i])
		h -= pow * uint32(s[i-n])
		//@ assert qs[i-n] == s[i-n] && qs[i] == s[i]
		// (Gobra) Under --disableNL the solver will not replace equals by
		// equals under a product, so knowing pow == PowRK(PrimeRK, n) is not
		// enough to read the subtraction above as the roll lemma states it.
		//@ lemmaMulSubstFirst(pow, PowRK(PrimeRK, n), uint32(s[i-n]))
		// (Gobra) The roll step is proved before the test rather than at the end
		// of the body, so that the test already knows h to be the hash of the
		// window it is about to compare -- which is what refutes a match on the
		// hash-mismatch path.
		//@ lemmaRKHashRangeRoll(qs, n, i)
		i++
		// (Gobra) lo names i-n so the trigger below contains no arithmetic:
		// Viper rejects {&s[i-n:i][k]} because ssliceFromSlice(s, i-n, i) has
		// an interpreted subtraction in it, but {&s[lo:i][k]} is a legal
		// pattern.
		//@ ghost lo := i - n
		//@ assert forall k int :: {&s[lo:i][k]} {seq(s)[lo+k]} 0 <= k && k < n ==> &s[lo:i][k] == &s[lo+k]
		if h == hashsep && Equal(s[i-n:i], sep) {
			//@ lemmaMatchesAtWindow(s, seq(sep), lo, i, p/4)
			return i - n
		}
		//@ ghost if h != hashsep {
		//@ 	lemmaNoMatchExtendWindowHash(qs, qsep, lo, i, h)
		//@ } else {
		//@ 	lemmaNoMatchExtendWindowBytes(s, seq(sep), lo, i, p/4)
		//@ }
	}
	return -1
}

// IndexRabinKarp uses the Rabin-Karp search algorithm to return the index of the
// first occurrence of substr in s, or -1 if not present.
//
// (Gobra) Note on the specification: Gobra models strings abstractly, so the
// postconditions are stated in terms of StrMatchesAt, which captures exactly
// the test performed by this function (matching window hash and successful
// string comparison); see spec.gobra.
// @ requires  len(substr) <= len(s)
// @ ensures   res == -1 ==> forall j int :: {StrMatchesAt(s, substr, j)} 0 <= j && j <= len(s)-len(substr) ==> !StrMatchesAt(s, substr, j)
// @ ensures   res != -1 ==> 0 <= res && res <= len(s)-len(substr) && StrMatchesAt(s, substr, res)
// @ ensures   res != -1 ==> forall j int :: {StrMatchesAt(s, substr, j)} 0 <= j && j < res ==> !StrMatchesAt(s, substr, j)
// @ decreases
func IndexRabinKarp(s, substr string) (res int) {
	// Rabin-Karp search
	hashss, pow := HashStr(substr)
	n := len(substr)
	var h uint32
	//@ invariant 0 <= i && i <= n
	//@ invariant h == RKHashStr(s, 0, i)
	//@ decreases n - i
	for i := 0; i < n; i++ {
		//@ lemmaRKHashStrStep(s, 0, i+1)
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
		h *= PrimeRK
		h += uint32(s[i])
		h -= pow * uint32(s[i-n])
		//@ ghost if 0 < n {
		//@ 	lemmaMulSubstFirst(pow, PowRK(PrimeRK, n), uint32(s[i-n]))
		//@ 	lemmaRKHashStrRoll(s, n, i)
		//@ }
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
