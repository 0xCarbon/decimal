// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"math/bits"
	"slices"
)

// Decimal is a finite, immutable decimal coefficient and base-ten exponent.
// Its zero value is zero at exponent zero. It is deliberately non-comparable;
// numeric equality is defined by the Equal method.
type Decimal struct {
	_     [0]func()
	words uint128
	meta  signExponent
	slow  *slowCoefficient
}

// uint128 is the comparable unsigned inline coefficient, low word first.
// Struct fields allow the compiler to assign both words to registers.
type uint128 struct{ lo, hi uint64 }

// signExponent stores the full int32 exponent in bits 0–31 and the sign in
// bit 63. Bits 32–62 are reserved zero.
type signExponent uint64

const decimalSignBit signExponent = 1 << 63

// packSignExponent is branchless: the 0/1 select of negative lowers to a
// flag move, shifted to bit 63.
func packSignExponent(exponent int32, negative bool) signExponent {
	var sign signExponent
	if negative {
		sign = 1
	}
	return signExponent(uint32(exponent)) | sign<<63
}

func (m signExponent) exponent() int32 { return int32(uint32(m)) }
func (m signExponent) negative() bool  { return int64(m) < 0 }

func inlineDecimal(words uint128, exponent int32, negative bool) Decimal {
	return Decimal{words: words, meta: packSignExponent(exponent, negative && words.lo|words.hi != 0)}
}

func slowDecimal(slow *slowCoefficient, exponent int32, negative bool) Decimal {
	return Decimal{meta: packSignExponent(exponent, negative), slow: slow}
}

func zeroDecimal(exponent int32) Decimal {
	return Decimal{meta: packSignExponent(exponent, false)}
}

func (d Decimal) exponent() int32 { return d.meta.exponent() }
func (d Decimal) negative() bool  { return d.meta.negative() }

func (d Decimal) withExponent(exponent int32) Decimal {
	d.meta = (d.meta & decimalSignBit) | signExponent(uint32(exponent))
	return d
}

func (d Decimal) withNegative(negative bool) Decimal {
	d.meta &^= decimalSignBit
	if negative && !d.isZero() {
		d.meta |= decimalSignBit
	}
	return d
}

func (d Decimal) negated() Decimal {
	if !d.isZero() {
		d.meta ^= decimalSignBit
	}
	return d
}

// slowCoefficient owns little-endian base-10^9 limbs. Published holders and
// their slices are immutable, so value copies may safely share them. A
// coefficient of at most slowSmallLimbs limbs (81 digits: every product of
// two 38-digit coefficients) lives in the holder's own array, so its
// publication is one allocation; larger coefficients own a separate slice.
type slowCoefficient struct {
	limbs []uint32
	small [slowSmallLimbs]uint32
}

const slowSmallLimbs = 9

// conversionScratchLimbs is the stack scratch of the byte-envelope
// conversions: the envelope of every coefficient of at most 81 digits is
// at most 11 limbs, so each such result publishes into a fused holder.
const conversionScratchLimbs = slowSmallLimbs + 2

// publishScratch publishes limbs the caller keeps as scratch: inline below
// 2^128, otherwise copied into one fused holder (or, above slowSmallLimbs,
// a holder and an exact slice). It never retains limbs.
func publishScratch(limbs []uint32, exponent int32, negative bool) Decimal {
	limbs = trimLimbs(limbs)
	if d, ok := publishInline(limbs, exponent, negative); ok {
		return d
	}
	h := new(slowCoefficient)
	if len(limbs) <= slowSmallLimbs {
		h.limbs = h.small[:copy(h.small[:], limbs)]
	} else {
		h.limbs = append([]uint32(nil), limbs...)
	}
	return slowDecimal(h, exponent, negative)
}

// publishOwned publishes limbs the caller hands over: inline below 2^128,
// otherwise a holder that keeps the slice itself.
func publishOwned(limbs []uint32, exponent int32, negative bool) Decimal {
	limbs = trimLimbs(limbs)
	if d, ok := publishInline(limbs, exponent, negative); ok {
		return d
	}
	return slowDecimal(&slowCoefficient{limbs: limbs}, exponent, negative)
}

// publishInline returns trimmed limbs as zero or as inline words when the
// value is below 2^128.
func publishInline(limbs []uint32, exponent int32, negative bool) (Decimal, bool) {
	if len(limbs) == 0 {
		return zeroDecimal(exponent), true
	}
	if len(limbs) > 5 {
		return Decimal{}, false
	}
	var words uint128
	for _, limb := range slices.Backward(limbs) {
		carry, low := bits.Mul64(words.lo, decimalLimbBase)
		overflow, high := bits.Mul64(words.hi, decimalLimbBase)
		low, lowCarry := bits.Add64(low, uint64(limb), 0)
		high, highCarry := bits.Add64(high, carry, lowCarry)
		if overflow != 0 || highCarry != 0 {
			return Decimal{}, false
		}
		words = uint128{low, high}
	}
	return inlineDecimal(words, exponent, negative), true
}

// New constructs a decimal from a signed 64-bit coefficient and an int32
// exponent, preserving the requested exponent even for zero.
func New(coefficient int64, exponent int32) Decimal {
	magnitude := uint64(coefficient)
	negative := coefficient < 0
	if negative {
		magnitude = -magnitude // unsigned arithmetic handles MinInt64
	}
	return inlineDecimal(uint128{lo: magnitude}, exponent, negative)
}

// Zero returns the zero value at exponent zero.
func Zero() Decimal { return Decimal{} }

// One returns one at exponent zero.
func One() Decimal { return New(1, 0) }

func (d Decimal) isZero() bool {
	return d.slow == nil && d.words.lo|d.words.hi == 0
}

// Exponent returns the stored base-ten exponent as constructed: the value is
// coefficient × 10^Exponent. It is never normalized, so 1.10 reports -2;
// Reduce is the explicit normalization.
func (d Decimal) Exponent() int32 { return d.exponent() }

// CoefficientDigits returns the number of decimal digits in the stored
// coefficient, counting written trailing zeros. Zero reports one digit.
func (d Decimal) CoefficientDigits() uint64 {
	switch {
	case d.isZero():
		return 1
	case d.slow == nil:
		return inlineDigits(d.words)
	default:
		v := coefficientViewOf(d)
		n, _ := arithmeticDigits(&v) // an addressable limb slice always fits
		return n
	}
}
