// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"math"
	"math/bits"
)

// Inline fast paths. A Decimal stores its coefficient inline exactly when the
// magnitude is below 2^128 and in slow base-10^9 limbs otherwise; every
// constructor and publisher preserves that canonical split. The helpers below
// operate on the two inline words directly and report ok=false whenever an
// intermediate would leave 128 bits, so callers fall back to the general limb
// path, which remains the single source of the documented semantics.

// pow10Words holds 10^0 through 10^19, every power of ten below 2^64.
var pow10Words = [...]uint64{
	1, 10, 100, 1_000, 10_000, 100_000, 1_000_000, 10_000_000, 100_000_000,
	1_000_000_000, 10_000_000_000, 100_000_000_000, 1_000_000_000_000,
	10_000_000_000_000, 100_000_000_000_000, 1_000_000_000_000_000,
	10_000_000_000_000_000, 100_000_000_000_000_000,
	1_000_000_000_000_000_000, 10_000_000_000_000_000_000,
}

// inlineScale returns w*10^k when the product stays below 2^128.
func inlineScale(w uint128, k uint64) (uint128, bool) {
	if w.lo|w.hi == 0 || k == 0 {
		return w, true
	}
	if k > 38 {
		return w, false // a nonzero value times 10^39 exceeds 2^128
	}
	if w.hi == 0 && k <= 19 {
		// Both factors fit in one word; their exact product fits in two.
		high, low := bits.Mul64(w.lo, pow10Words[k])
		return uint128{low, high}, true
	}
	for k > 0 {
		step := min(k, 19)
		m := pow10Words[step]
		carry, low := bits.Mul64(w.lo, m)
		overflow, high := bits.Mul64(w.hi, m)
		high, c := bits.Add64(high, carry, 0)
		if overflow != 0 || c != 0 {
			return w, false
		}
		w = uint128{low, high}
		k -= step
	}
	return w, true
}

func inlineCompare(a, b uint128) int {
	switch {
	case a.hi != b.hi:
		if a.hi < b.hi {
			return -1
		}
		return 1
	case a.lo < b.lo:
		return -1
	case a.lo > b.lo:
		return 1
	}
	return 0
}

// inlineCompareMagnitude orders two nonzero inline magnitudes numerically.
func inlineCompareMagnitude(a uint128, ae int32, b uint128, be int32) int {
	switch {
	case ae == be:
		return inlineCompare(a, b)
	case ae > be:
		scaled, ok := inlineScale(a, uint64(int64(ae)-int64(be)))
		if !ok {
			return 1 // a*10^k is at least 2^128 and b is below it
		}
		return inlineCompare(scaled, b)
	default:
		scaled, ok := inlineScale(b, uint64(int64(be)-int64(ae)))
		if !ok {
			return -1
		}
		return inlineCompare(a, scaled)
	}
}

// inlineAddSub computes the exact Add/Sub result at the minimum exponent,
// or reports false for a limb operand or a sum that leaves 128 bits; the
// sum is addSubExact's, the bare Add/Sub fast path.
func inlineAddSub(d, other Decimal, subtract bool) (Decimal, bool) {
	result, ok, _ := d.addSubExact(other, addSubMode(subtract))
	return result, ok
}

// inlineMul computes an exact product whose magnitude stays below 2^128 at
// an int32 exponent sum, or reports false; the product is mulExact's, the
// bare Mul fast path.
func inlineMul(d, other Decimal) (Decimal, bool) {
	result, ok, _ := d.mulExact(other, 0)
	return result, ok
}

// pow10Wide holds 10^0 through 10^38, every power of ten below 2^128.
var pow10Wide = func() (table [39]uint128) {
	table[0] = uint128{1, 0}
	for k := 1; k < len(table); k++ {
		high, low := bits.Mul64(table[k-1].lo, 10)
		table[k] = uint128{low, table[k-1].hi*10 + high}
	}
	return table
}()

// inlineDigits is the decimal digit count of a nonzero inline magnitude.
func inlineDigits(w uint128) uint64 {
	// 1233/4096 approximates log10(2); the estimate is exact or one low.
	bitLength := uint64(bits.Len64(w.hi)) + 64
	if w.hi == 0 {
		bitLength = uint64(bits.Len64(w.lo))
	}
	n := bitLength * 1233 >> 12
	if n < uint64(len(pow10Wide)) && inlineCompare(w, pow10Wide[n]) >= 0 {
		n++
	}
	return max(n, 1)
}

// inlineQuantize serves unguarded, unlimited-precision, unbudgeted target
// rounding. It returns ok=false for shifts it does not cover.
func inlineQuantize(d Decimal, target int32, mode RoundingMode) (result Decimal, events Conditions, exactRefusal, ok bool) {
	switch difference := int64(d.exponent()) - int64(target); {
	case difference == 0:
		return d, 0, false, true
	case difference > 0:
		w, fits := inlineScale(d.words, uint64(difference))
		if !fits {
			return Decimal{}, 0, false, false
		}
		return inlineDecimal(w, target, d.negative()), 0, false, true
	case difference < -19:
		return inlineQuantizeFar(d, target, mode, uint64(-difference))
	default:
		cut := -difference
		divisor := pow10Words[cut]
		var qhi, qlo, remainder uint64
		var guard, retainedLow uint32
		var sticky bool
		if d.words.hi == 0 {
			// Constant small cuts let the compiler replace division with a
			// reciprocal multiply. Every other cut needs one word division.
			switch cut {
			case 1:
				qlo = d.words.lo / 10
			case 2:
				qlo = d.words.lo / 100
			case 3:
				qlo = d.words.lo / 1_000
			case 4:
				qlo = d.words.lo / 10_000
			default:
				qlo = d.words.lo / divisor
			}
			remainder = d.words.lo - qlo*divisor
			retainedLow = uint32(qlo & 1)
			// All divisors are even. Comparing with half avoids the overflow
			// possible in 2*remainder and preserves each rounding decision.
			if remainder != 0 {
				guard = 1
				if half := divisor / 2; remainder >= half {
					guard, sticky = 5, remainder > half
				}
			}
		} else {
			var r uint64
			qhi, r = bits.Div64(0, d.words.hi, divisor)
			qlo, remainder = bits.Div64(r, d.words.lo, divisor)
			guard = uint32(remainder / pow10Words[cut-1])
			sticky = remainder%pow10Words[cut-1] != 0
			retainedLow = uint32(qlo % 10)
		}
		events = Rounded
		if remainder != 0 {
			if mode == Exact {
				return Decimal{}, 0, true, true
			}
			events |= Inexact
		}
		q := uint128{qlo, qhi}
		up := contextRoundUp(mode, d.negative(), guard, sticky, retainedLow)
		if remainder != 0 {
			events |= roundingDirection(up, d.negative())
		}
		if up {
			var carry uint64
			q.lo, carry = bits.Add64(q.lo, 1, 0)
			q.hi += carry // q < 2^128/10, so this cannot overflow
		}
		if q.lo|q.hi == 0 {
			return zeroDecimal(target), events, false, true
		}
		return inlineDecimal(q, target, d.negative()), events, false, true
	}
}

// inlineQuantizeFar is inlineQuantize for a nonzero d and a cut of more
// than 19 digits. Up to 38 digits are dropped in two steps, the low 19
// feeding only the sticky bit; a cut of 39 leaves the leading digit of a
// 39-digit coefficient as the guard; a longer cut discards every digit
// below the guard position. The retained coefficient fits one word.
func inlineQuantizeFar(d Decimal, target int32, mode RoundingMode, cut uint64) (result Decimal, events Conditions, exactRefusal, ok bool) {
	var q uint64
	var guard uint32
	sticky := true
	switch {
	case cut <= 38:
		w := d.words
		var low, r uint64
		w.hi, r = bits.Div64(0, w.hi, pow10Words[19])
		w.lo, low = bits.Div64(r, w.lo, pow10Words[19])
		rest := cut - 19
		// w < 2^128/10^19 < 2^65, so w.hi < 2 ≤ 10^rest.
		q, r = bits.Div64(w.hi, w.lo, pow10Words[rest])
		guard = uint32(r / pow10Words[rest-1])
		sticky = low != 0 || r%pow10Words[rest-1] != 0
	case cut == 39:
		w := d.words
		for inlineCompare(w, pow10Wide[38]) >= 0 { // at most three times
			var borrow uint64
			w.lo, borrow = bits.Sub64(w.lo, pow10Wide[38].lo, 0)
			w.hi, _ = bits.Sub64(w.hi, pow10Wide[38].hi, borrow)
			guard++
		}
		sticky = w.lo|w.hi != 0
	}
	negative := d.negative()
	inexact := guard != 0 || sticky
	events = Rounded
	if inexact {
		if mode == Exact {
			return Decimal{}, 0, true, true
		}
		events |= Inexact
	}
	up := contextRoundUp(mode, negative, guard, sticky, uint32(q&1))
	if inexact {
		events |= roundingDirection(up, negative)
	}
	if up {
		q++ // q < 2^65/10
	}
	if q == 0 {
		return zeroDecimal(target), events, false, true
	}
	return inlineDecimal(uint128{lo: q}, target, negative), events, false, true
}

// inlineReduce strips trailing zeros from a nonzero one-word coefficient
// without raising the exponent above MaxInt32. It removes exactly
// m = min(t, MaxInt32-e) zeros, where t <= 19 counts the trailing zeros:
// fewer than 2k zeros stay removable when the stage for 10^k runs (m < 32
// at 10^16), so each constant-divisor stage strips its power at most once
// and leaves m < k for the next.
func inlineReduce(d Decimal) Decimal {
	w := d.words.lo
	if w%10 != 0 {
		return d
	}
	budget := math.MaxInt32 - int64(d.exponent())
	if q := w / 1e16; budget >= 16 && q*1e16 == w {
		w, budget = q, budget-16
	}
	if q := w / 1e8; budget >= 8 && q*1e8 == w {
		w, budget = q, budget-8
	}
	if q := w / 1e4; budget >= 4 && q*1e4 == w {
		w, budget = q, budget-4
	}
	if q := w / 100; budget >= 2 && q*100 == w {
		w, budget = q, budget-2
	}
	if q := w / 10; budget >= 1 && q*10 == w {
		w, budget = q, budget-1
	}
	return inlineDecimal(uint128{lo: w}, int32(math.MaxInt32-budget), d.negative())
}

// wide256 is an unsigned 256-bit intermediate, least significant word
// first. It holds the exact product of two inline coefficients and their
// exact sum across an exponent gap of up to 38, both below 10^77 < 2^256,
// so context arithmetic on decimal128-sized operands rounds once from the
// exact result without a limb conversion.
type wide256 [4]uint64

// pow10Wide256 holds 10^0 through 10^77, every power of ten below 2^256.
var pow10Wide256 = func() (table [78]wide256) {
	table[0][0] = 1
	for k := 1; k < len(table); k++ {
		table[k] = table[k-1]
		table[k].mulSmall(10)
	}
	return table
}()

// mulWide is the exact product of two inline coefficients.
func mulWide(a, b uint128) (z wide256) {
	h00, l00 := bits.Mul64(a.lo, b.lo)
	h01, l01 := bits.Mul64(a.lo, b.hi)
	h10, l10 := bits.Mul64(a.hi, b.lo)
	h11, l11 := bits.Mul64(a.hi, b.hi)
	z[0] = l00
	t, c1 := bits.Add64(h00, l01, 0)
	z[1], t = bits.Add64(t, l10, 0)
	c1 += t
	t, c2 := bits.Add64(h01, h10, 0)
	t, c3 := bits.Add64(t, l11, 0)
	z[2], t = bits.Add64(t, c1, 0)
	z[3] = h11 + c2 + c3 + t
	return z
}

// mulSmall multiplies in place; the caller keeps the product below 2^256.
func (z *wide256) mulSmall(m uint64) {
	var carry uint64
	for i := range z {
		hi, lo := bits.Mul64(z[i], m)
		var c uint64
		z[i], c = bits.Add64(lo, carry, 0)
		carry = hi + c
	}
}

// mulWords multiplies in place by a two-word factor and reports whether the
// product stays below 2^256; z is unspecified when it does not. The product
// is z·m.lo plus z·m.hi shifted up one word, each formed with its carry
// out.
func (z *wide256) mulWords(m uint128) bool {
	var low, high wide256
	var carryLow, carryHigh uint64
	for i := range z {
		hi, lo := bits.Mul64(z[i], m.lo)
		var c uint64
		low[i], c = bits.Add64(lo, carryLow, 0)
		carryLow = hi + c
		hi, lo = bits.Mul64(z[i], m.hi)
		high[i], c = bits.Add64(lo, carryHigh, 0)
		carryHigh = hi + c
	}
	var carry uint64
	low[1], carry = bits.Add64(low[1], high[0], 0)
	low[2], carry = bits.Add64(low[2], high[1], carry)
	low[3], carry = bits.Add64(low[3], high[2], carry)
	*z = low
	return carryLow|carryHigh|high[3]|carry == 0
}

// divSmall divides in place by a nonzero d and returns the remainder.
func (z *wide256) divSmall(d uint64) (r uint64) {
	for i := len(z) - 1; i >= 0; i-- {
		z[i], r = bits.Div64(r, z[i], d)
	}
	return r
}

func (z wide256) cmp(o wide256) int {
	for i := len(z) - 1; i >= 0; i-- {
		if z[i] != o[i] {
			if z[i] < o[i] {
				return -1
			}
			return 1
		}
	}
	return 0
}

// digits is the decimal digit count of a nonzero value.
func (z wide256) digits() uint64 {
	top := len(z) - 1
	for top > 0 && z[top] == 0 {
		top--
	}
	// 1233/4096 approximates log10(2); the estimate is exact or one low.
	n := (uint64(top)*64 + uint64(bits.Len64(z[top]))) * 1233 >> 12
	if n < uint64(len(pow10Wide256)) && z.cmp(pow10Wide256[n]) >= 0 {
		n++
	}
	return max(n, 1)
}

// addWide and subWide return a + b and a − b for a ≥ b, without overflow
// for the values a wide256 is used for.
func addWide(a, b wide256) (z wide256) {
	var carry uint64
	for i := range z {
		z[i], carry = bits.Add64(a[i], b[i], carry)
	}
	return z
}

func subWide(a, b wide256) (z wide256) {
	var borrow uint64
	for i := range z {
		z[i], borrow = bits.Sub64(a[i], b[i], borrow)
	}
	return z
}
