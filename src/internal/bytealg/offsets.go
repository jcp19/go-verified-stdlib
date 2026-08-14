// Copyright 2018 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// These declarations were moved, unchanged, from bytealg.go so that the rest
// of that file can be verified with Gobra: unsafe.Offsetof is not supported
// by Gobra and cannot appear in a file under verification. The constants are
// only consumed by the per-architecture assembly files of this package (via
// go_asm.h), so they are irrelevant to the verified Go code. This file
// deliberately carries no Gobra header comment, so Gobra ignores it.

package bytealg

import (
	"internal/cpu"
	"unsafe"
)

// Offsets into internal/cpu records for use in assembly.
const (
	offsetX86HasSSE42  = unsafe.Offsetof(cpu.X86.HasSSE42)
	offsetX86HasAVX2   = unsafe.Offsetof(cpu.X86.HasAVX2)
	offsetX86HasPOPCNT = unsafe.Offsetof(cpu.X86.HasPOPCNT)

	offsetS390xHasVX = unsafe.Offsetof(cpu.S390X.HasVX)

	offsetPPC64HasPOWER9 = unsafe.Offsetof(cpu.PPC64.IsPOWER9)
)
