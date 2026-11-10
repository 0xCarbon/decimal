// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"math/bits"
	"runtime"
)

// pairedMultiplyKernel selects the paired-limb kernel at compile
// time. It is on only where bits.Mul64 is one instruction and the kernel
// is faster (amd64). 386 and wasm emulate Mul64, so they keep the
// base-10^9 scalar kernel, which is also the kernel's differential twin.
const pairedMultiplyKernel = runtime.GOARCH == "amd64"

// The scalar kernel's outer loop runs over a, so a long a with a short b
// is its slow orientation, while the paired kernel is symmetric.
// The thresholds are the amd64 crossovers BenchmarkMultiplyKernels shows:
// the paired kernel runs when a has at least pairedMultiplyOuterLimbs
// limbs, or when both operands have at least pairedMultiplyMinLimbs and one
// has pairedMultiplyMaxLimbs. A short a with a long b, 4×4 and 5×5 stay
// scalar: the kernels are within noise of each other there.
const (
	pairedMultiplyOuterLimbs = 8
	pairedMultiplyMinLimbs   = 4
	pairedMultiplyMaxLimbs   = 6
)

// pairedMultiplyShape reports whether the paired kernel runs for an a of
// outer limbs and a b of inner limbs.
func pairedMultiplyShape(outer, inner int) bool {
	return outer >= pairedMultiplyOuterLimbs ||
		min(outer, inner) >= pairedMultiplyMinLimbs && max(outer, inner) >= pairedMultiplyMaxLimbs
}

const (
	pairBase = decimalLimbBase * decimalLimbBase // 10^18
	// pairShift normalizes 10^18 (60 bits) so its top bit is set, as the
	// reciprocal division step requires.
	pairShift = 4
	pairNorm  = pairBase << pairShift
	// pairReciprocal is ⌊(2^128−1)/pairNorm⌋ − 2^64 (Möller–Granlund).
	pairReciprocal = 0x2725dd1d243aba0e
)

// fillMultiply writes the product of a and b into out, which must be zero
// and hold at least a.count+b.count−1 limbs, as the scalar kernel indexes;
// false reports a product longer than out, which the callers' n+m limbs
// rule out. The paired kernel is a fast path: on false the scalar kernel
// decides from a cleared out. Where the paired kernel is off, fillMultiply
// inlines to the scalar call.
func fillMultiply(out []uint32, a, b *coefficientView) bool {
	if multiplyPaired(a, b) {
		return fillMultiplyPaired(out, a, b) || fillMultiplyScalar(clearLimbs(out), a, b)
	}
	return fillMultiplyScalar(out, a, b)
}

// multiplyPaired reports whether fillMultiply runs the paired kernel for a
// times b; a is the scalar kernel's outer operand.
func multiplyPaired(a, b *coefficientView) bool {
	return pairedMultiplyKernel && pairedMultiplyShape(a.count, b.count)
}

// clearLimbs zeroes and returns s.
func clearLimbs(s []uint32) []uint32 {
	clear(s)
	return s
}

// fillMultiplyScalar is single-buffer base-10^9 schoolbook multiplication.
// Each inner sum stays below 10^18+2*10^9, within uint64.
func fillMultiplyScalar(out []uint32, a, b *coefficientView) bool {
	for i := 0; i < a.count; i++ {
		var carry uint64
		for j := 0; j < b.count; j++ {
			index := i + j
			sum := uint64(a.limb(i))*uint64(b.limb(j)) + uint64(out[index]) + carry
			out[index] = uint32(sum % decimalLimbBase)
			carry = sum / decimalLimbBase
		}
		for index := i + b.count; carry != 0 && index < len(out); index++ {
			sum := uint64(out[index]) + carry
			out[index] = uint32(sum % decimalLimbBase)
			carry = sum / decimalLimbBase
		}
		if carry != 0 {
			return false
		}
	}
	return true
}

// fillMultiplyPaired is column-wise (Comba) schoolbook multiplication in
// base 10^18: limbs 2i and 2i+1 pair into one value below 10^18, the top
// pair of an odd operand having a zero high limb. Carry argument:
//
//   - a pair product is below (10^18−1)^2 < 2^120; a column accumulates
//     at most min(pairs) < 2^62 products plus the previous column's
//     quotient (below the previous accumulator/10^18) in three words
//     (t2:t1:t0), so it stays below 2^62·2^120·(1+10^-18+…) < 2^183 and
//     never overflows 2^192;
//   - each column divides the accumulator by 10^18 exactly (pairDivide):
//     the remainder is the column's output pair and the quotient, which is
//     below the accumulator/10^18, carries into the next column;
//   - the output pair splits into base-10^9 limbs 2k and 2k+1, so out
//     holds the same limbs the scalar kernel writes. A nonzero limb past
//     len(out) returns false.
func fillMultiplyPaired(out []uint32, a, b *coefficientView) bool {
	as, bs := a.limbSlice(), b.limbSlice()
	na, nb := (len(as)+1)/2, (len(bs)+1)/2
	var t0, t1, t2 uint64
	k := 0
	for ; k < na+nb-1; k++ {
		i, end := max(0, k-nb+1), min(k, na-1)
		for ; i <= end; i++ {
			hi, lo := bits.Mul64(limbPair(as, i), limbPair(bs, k-i))
			var c uint64
			t0, c = bits.Add64(t0, lo, 0)
			t1, c = bits.Add64(t1, hi, c)
			t2 += c
		}
		var r uint64
		t2, t1, t0, r = pairDivide(t2, t1, t0)
		if !storePair(out, k, r) {
			return false
		}
	}
	for ; t0|t1|t2 != 0; k++ {
		var r uint64
		t2, t1, t0, r = pairDivide(t2, t1, t0)
		if !storePair(out, k, r) {
			return false
		}
	}
	return true
}

// limbSlice returns the view's limbs, least significant first.
func (v *coefficientView) limbSlice() []uint32 {
	if v.slow != nil {
		return v.slow
	}
	return v.inline[:v.count]
}

// limbPair returns limbs 2i and 2i+1 as one base-10^18 digit.
func limbPair(s []uint32, i int) uint64 {
	lo := uint64(s[2*i])
	if 2*i+1 < len(s) {
		return lo + uint64(s[2*i+1])*decimalLimbBase
	}
	return lo
}

// storePair writes a base-10^18 digit below 10^18 as limbs 2k and 2k+1.
func storePair(out []uint32, k int, r uint64) bool {
	hi, lo := uint32(r/decimalLimbBase), uint32(r%decimalLimbBase)
	p := 2 * k
	if p+1 < len(out) {
		out[p], out[p+1] = lo, hi
		return true
	}
	if p < len(out) {
		out[p] = lo
	} else if lo != 0 {
		return false
	}
	return hi == 0
}

// pairDivide divides t2:t1:t0 by 10^18, returning the quotient and the
// remainder. The dividend is shifted by pairShift so each step divides by
// the normalized pairNorm with a high word below it.
func pairDivide(t2, t1, t0 uint64) (q2, q1, q0, r uint64) {
	u2 := t2<<pairShift | t1>>(64-pairShift)
	u1 := t1<<pairShift | t0>>(64-pairShift)
	u0 := t0 << pairShift
	r = u2 // below 2^pairShift when t2 is zero
	if t2 != 0 {
		q2, r = pairDivStep(t2>>(64-pairShift), u2)
	}
	if r == 0 && u1 < pairNorm {
		r = u1
	} else {
		q1, r = pairDivStep(r, u1)
	}
	q0, r = pairDivStep(r, u0)
	return q2, q1, q0, r >> pairShift
}

// pairDivStep divides x1:x0 by pairNorm for x1 < pairNorm with the
// precomputed reciprocal (the math/big divWW step). For this divisor the
// estimate is the quotient or one below it: the shortfall is below
// 1 + (e/d)·(d/2^64) + (2^64/d − 1) < 1 + 0.400 + 0.153, where
// e = (2^128−1) mod d and e/d = 0.461. So the remainder is below
// 1.553·pairNorm and exactly one of the two corrections below can fire:
// the first when the remainder reaches 2^64, the second when it lies in
// [pairNorm, 2^64).
func pairDivStep(x1, x0 uint64) (q, r uint64) {
	t1, t0 := bits.Mul64(pairReciprocal, x1)
	_, c := bits.Add64(t0, x0, 0)
	q, _ = bits.Add64(t1, x1, c)
	dq1, dq0 := bits.Mul64(pairNorm, q)
	r, borrow := bits.Sub64(x0, dq0, 0)
	r1, _ := bits.Sub64(x1, dq1, borrow)
	if r1 != 0 {
		q++
		r -= pairNorm
	}
	if r >= pairNorm {
		q++
		r -= pairNorm
	}
	return q, r
}
