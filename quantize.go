// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"math/bits"
)

// Quantize rounds to an explicit stored exponent under the selected mode.
func (d Decimal) Quantize(targetExponent int32, mode RoundingMode) (Decimal, Conditions, error) {
	if mode > Exact {
		return quantizeInvalidMode("Quantize")
	}
	if d.slow == nil && d.words.lo|d.words.hi != 0 {
		if result, events, refused, ok := inlineQuantize(d, targetExponent, mode); ok {
			if refused {
				return contextExactRefusal("Quantize")
			}
			return result, events, nil
		}
	}
	return d.quantizeLimbs(targetExponent, Context{rounding: mode}, limits{}, "Quantize")
}

// QuantizeWithContext rounds to an explicit stored exponent under ctx.
func (d Decimal) QuantizeWithContext(targetExponent int32, ctx Context) (Decimal, Conditions, error) {
	return d.quantize(targetExponent, ctx, ctx.arith, "QuantizeWithContext")
}

// RoundToIntegral rounds to stored exponent zero under the selected mode.
func (d Decimal) RoundToIntegral(mode RoundingMode) (Decimal, Conditions, error) {
	if mode > Exact {
		return quantizeInvalidMode("RoundToIntegral")
	}
	if d.slow == nil && d.words.lo|d.words.hi != 0 {
		if result, events, refused, ok := inlineQuantize(d, 0, mode); ok {
			if refused {
				return contextExactRefusal("RoundToIntegral")
			}
			return result, events, nil
		}
	}
	return d.quantizeLimbs(0, Context{rounding: mode}, limits{}, "RoundToIntegral")
}

// RoundToIntegralWithContext rounds to stored exponent zero under ctx.
func (d Decimal) RoundToIntegralWithContext(ctx Context) (Decimal, Conditions, error) {
	return d.quantize(0, ctx, ctx.arith, "RoundToIntegralWithContext")
}

func quantizeInvalidMode(op string) (Decimal, Conditions, error) {
	return Decimal{}, 0, newError(op, ErrInvalidContext)
}

// quantizeTariff is the Quantize charge, shared by quantizeLimbs
// and the estimators, for d digits at difference k = e − t.
// Growing (k > 0) charges and produces d + k digits; an equal exponent
// charges 1 and keeps d. Shrinking by c = −k precharges base d when c ≤ d
// (else 1), then charges base + length, where length is d − c digits plus
// one for an all-nines round-up carry when c < d, one digit when c = d, and
// a flat 2 with one digit when c > d.
func quantizeTariff(digits quantizeCount, difference int64, carry bool) (base, work, length quantizeCount) {
	one := quantizeCount{lo: 1}
	switch {
	case difference > 0:
		length = digits.addUint(uint64(difference))
		return one, length, length
	case difference == 0:
		return one, one, digits
	}
	cut := uint64(-difference)
	switch digits.cmpUint(cut) {
	case 1:
		length = digits.subUint(cut)
		if carry {
			length = length.addUint(1)
		}
		return digits, digits.add(length), length
	case 0:
		return digits, digits.add(one), one
	}
	return one, quantizeCount{lo: 2}, one
}

// quantizeCount is a two-word nonnegative digit/work count. A 64-bit slice
// can have a representable limb count but more than uint64 decimal digits.
type quantizeCount struct{ hi, lo uint64 }

func quantizeCountOf(v *coefficientView) quantizeCount {
	hi, lo := bits.Mul64(uint64(v.count-1), 9)
	lo, carry := bits.Add64(lo, uint64(limbDigits(v.limb(v.count-1))), 0)
	return quantizeCount{hi + carry, lo}
}

func (c quantizeCount) add(other quantizeCount) quantizeCount {
	lo, carry := bits.Add64(c.lo, other.lo, 0)
	return quantizeCount{c.hi + other.hi + carry, lo}
}

func (c quantizeCount) addUint(n uint64) quantizeCount {
	lo, carry := bits.Add64(c.lo, n, 0)
	return quantizeCount{c.hi + carry, lo}
}

func (c quantizeCount) subUint(n uint64) quantizeCount {
	lo, borrow := bits.Sub64(c.lo, n, 0)
	return quantizeCount{c.hi - borrow, lo}
}

func (c quantizeCount) cmpUint(n uint64) int {
	if c.hi != 0 || c.lo > n {
		return 1
	}
	if c.lo < n {
		return -1
	}
	return 0
}

func quantizeAdmitted(limit uint64, n quantizeCount) bool {
	return limit == 0 || n.cmpUint(limit) <= 0
}

func quantizePhysicalCount(n quantizeCount, op string) (int, error) {
	if n.hi >= 9 {
		return 0, newError(op, ErrInsufficientStorage)
	}
	limbs, rem := bits.Div64(n.hi, n.lo, 9)
	if rem != 0 {
		limbs++
	}
	return arithmeticPhysicalLimbCount(limbs, op)
}

func quantizeDigit(v *coefficientView, position uint64) uint32 {
	group := position / 9
	if group >= uint64(v.count) {
		return 0
	}
	return v.limb(int(group)) / decimalPowers[position%9] % 10
}

func quantizeDiscard(v *coefficientView, k uint64) (guard uint32, sticky bool, retainedLow uint32) {
	guard = quantizeDigit(v, k-1)
	group, place := (k-1)/9, (k-1)%9
	for i := range group {
		if v.limb(int(i)) != 0 {
			sticky = true
			break
		}
	}
	if v.limb(int(group))%decimalPowers[place] != 0 {
		sticky = true
	}
	retainedLow = quantizeDigit(v, k)
	return
}

func quantizeAllNines(v *coefficientView, k uint64) bool {
	first, place := k/9, k%9
	for index := first; index < uint64(v.count); index++ {
		limb := v.limb(int(index))
		width := uint32(9)
		if index == uint64(v.count-1) {
			width = limbDigits(limb)
		}
		if index == first {
			limb /= decimalPowers[place]
			width -= uint32(place)
		}
		maximum := uint32(decimalLimbBase - 1)
		if width < 9 {
			maximum = decimalPowers[width] - 1
		}
		if limb != maximum {
			return false
		}
	}
	return true
}

func quantizeQuotientLimb(v *coefficientView, k uint64, index int) uint32 {
	whole, part := k/9, k%9
	group := whole + uint64(index)
	if group >= uint64(v.count) {
		return 0
	}
	low := v.limb(int(group))
	if part == 0 {
		return low
	}
	result := low / decimalPowers[part]
	if group+1 < uint64(v.count) {
		result += (v.limb(int(group+1)) % decimalPowers[part]) * decimalPowers[9-part]
	}
	return result
}

func (d Decimal) quantize(target int32, ctx Context, budget limits, op string) (Decimal, Conditions, error) {
	if d.slow == nil && budget.admits(inlineResultDigits, inlineQuantizeWork) && !d.isZero() && (!ctx.guarded || quantizeTargetStorable(target, &ctx)) {
		if result, events, refused, ok := inlineQuantize(d, target, ctx.rounding); ok {
			if refused {
				return contextExactRefusal(op)
			}
			if ctx.precision == 0 {
				return contextOutcome(result, events, ctx.traps, op)
			}
			if fits, subnormal := quantizeInlineFits(result, target, &ctx); fits {
				return contextOutcome(result, events|subnormal, ctx.traps, op)
			}
		}
	}
	return d.quantizeLimbs(target, ctx, budget, op)
}

// quantizeTargetStorable is quantizeLimbs' first refusal, negated: a guarded
// context stores only targets in [Etiny, Emax].
func quantizeTargetStorable(target int32, ctx *Context) bool {
	if !ctx.guarded {
		return true
	}
	etiny := int64(ctx.guards.Emin) - int64(ctx.precision-1)
	return int64(target) >= etiny && target <= ctx.guards.Emax
}

// quantizeInlineFits applies quantizeLimbs' precision and guard checks to
// an inline rounded result at a storable target, whose digit count is the
// general path's planned length: it reports whether the result is
// publishable, and Subnormal for a nonzero result below Emin. A result
// that does not fit is the general path's ErrInvalidOperation.
func quantizeInlineFits(result Decimal, target int32, ctx *Context) (fits bool, subnormal Conditions) {
	zero := result.isZero()
	length := uint64(1)
	if !zero {
		length = inlineDigits(result.words)
	}
	if ctx.precision != 0 && length > uint64(ctx.precision) {
		return false, 0
	}
	if ctx.guarded && !zero {
		if length > uint64(int64(ctx.guards.Emax)-int64(target)+1) {
			return false, 0
		}
		if threshold := int64(ctx.guards.Emin) - int64(target) + 1; threshold > 0 && length < uint64(threshold) {
			subnormal = Subnormal
		}
	}
	return true, subnormal
}

// quantizeLimbs is the general target-rounding path; it owns every guard,
// precision and budget check.
func (d Decimal) quantizeLimbs(target int32, ctx Context, budget limits, op string) (Decimal, Conditions, error) {
	if ctx.guarded {
		etiny := int64(ctx.guards.Emin) - int64(ctx.precision-1)
		if int64(target) < etiny || target > ctx.guards.Emax {
			return contextFailure(op, ErrInvalidOperation)
		}
	}
	if d.isZero() {
		one := quantizeCount{lo: 1}
		if !quantizeAdmitted(budget.MaxWork, one) || !quantizeAdmitted(budget.MaxDigits, one) {
			return contextFailure(op, ErrInsufficientStorage)
		}
		return zeroDecimal(target), 0, nil
	}
	v := coefficientViewOf(d)
	digits := quantizeCountOf(&v)
	difference := int64(d.exponent()) - int64(target)
	base, work, length := quantizeTariff(digits, difference, false)
	var retained quantizeCount
	var cut uint64
	var grow, shrink, zero, roundUp, carryTop bool
	var events Conditions
	switch {
	case difference > 0:
		grow = true
	case difference < 0:
		shrink = true
		cut = uint64(-difference)
	}
	if !quantizeAdmitted(budget.MaxWork, base) {
		return contextFailure(op, ErrInsufficientStorage)
	}
	if shrink {
		events = Rounded | Inexact
		var guard, low uint32
		sticky := true
		if digits.cmpUint(cut) >= 0 {
			guard, sticky, low = quantizeDiscard(&v, cut)
			if guard == 0 && !sticky {
				events = Rounded
			}
		}
		if ctx.rounding == Exact && events&Inexact != 0 {
			return contextExactRefusal(op)
		}
		roundUp = contextRoundUp(ctx.rounding, d.negative(), guard, sticky, low)
		if events&Inexact != 0 {
			events |= roundingDirection(roundUp, d.negative())
		}
		if digits.cmpUint(cut) > 0 {
			retained = digits.subUint(cut)
			carryTop = roundUp && quantizeAllNines(&v, cut)
			_, work, length = quantizeTariff(digits, difference, carryTop)
		} else {
			zero = !roundUp
		}
	}
	if ctx.precision != 0 && length.cmpUint(uint64(ctx.precision)) > 0 {
		return contextFailure(op, ErrInvalidOperation)
	}
	if ctx.guarded && !zero {
		if length.cmpUint(uint64(int64(ctx.guards.Emax)-int64(target)+1)) > 0 {
			return contextFailure(op, ErrInvalidOperation)
		}
		threshold := int64(ctx.guards.Emin) - int64(target) + 1
		if threshold > 0 && length.cmpUint(uint64(threshold)) < 0 {
			events |= Subnormal
		}
	}
	if !quantizeAdmitted(budget.MaxDigits, length) || !quantizeAdmitted(budget.MaxWork, work) {
		return contextFailure(op, ErrInsufficientStorage)
	}
	count, err := quantizePhysicalCount(length, op)
	if err != nil {
		return Decimal{}, 0, err
	}
	if zero {
		return contextOutcome(zeroDecimal(target), events, ctx.traps, op)
	}
	if !grow && !shrink {
		return contextOutcome(d, events, ctx.traps, op)
	}
	fill := func(out []uint32) {
		switch {
		case grow:
			for i := range out {
				out[i] = alignedLimb(&v, uint64(difference), uint64(i))
			}
		case carryTop:
			place, remainder := bits.Div64(retained.hi, retained.lo, 9)
			out[int(place)] = decimalPowers[remainder]
		case retained.hi == 0 && retained.lo == 0:
			if roundUp {
				out[0] = 1
			}
		default:
			for i := range out {
				out[i] = quantizeQuotientLimb(&v, cut, i)
			}
			if roundUp {
				carry := uint64(1)
				for i := range out {
					sum := uint64(out[i]) + carry
					out[i] = uint32(sum % decimalLimbBase)
					carry = sum / decimalLimbBase
					if carry == 0 {
						break
					}
				}
			}
		}
	}
	if length.cmpUint(38) <= 0 {
		var inline [5]uint32
		out := inline[:count]
		fill(out)
		return contextOutcome(publishInlineArithmetic(out, target, d.negative()), events, ctx.traps, op)
	}
	if count <= slowSmallLimbs {
		var scratch [slowSmallLimbs]uint32
		out := scratch[:count]
		fill(out)
		return contextOutcome(publishScratch(out, target, d.negative()), events, ctx.traps, op)
	}
	out := make([]uint32, count)
	fill(out)
	return contextOutcome(publishOwned(out, target, d.negative()), events, ctx.traps, op)
}
