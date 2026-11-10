// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"math/bits"
	"slices"
)

// Sum returns the exact sum of values: the fold of Add, at the smallest operand
// exponent (the largest scale), with no rounding. The empty sum is zero (0E0).
// It fails only on a checked resource refusal, as Add does.
func Sum(values ...Decimal) (Decimal, error) {
	return sumValues(values, limits{}, "Sum")
}

// SumWithBudget is Sum under an operation budget. The envelope bounds the
// exact sum before any operand is added, so operands that cancel still
// cost the span they cover: 1E+10000000 − 1E+10000000 + 1E−10000000 plans
// twenty million digits for a one-digit result, where a fold of Add would
// not.
//
// A header scan charges one unit per operand; the digit envelope L =
// amax − emin + 1 + ⌈log10 k⌉ (the largest adjusted exponent over the smallest exponent,
// plus carries from k operands) must fit the digit cap before anything is
// allocated; and the full charge is k + Σdᵢ + 2·t(L), t(L) = 1+(L−1)/9.
func SumWithBudget(values []Decimal, budget Budget) (Decimal, error) {
	return sumValues(values, budget.arith(), "SumWithBudget")
}

// SumShape describes a Sum's operands for EstimateSum without the values:
// their count, their total coefficient digits, the smallest exponent, the
// largest adjusted exponent of a nonzero operand, and whether any operand
// is nonzero. ShapeOfSum builds it.
type SumShape struct {
	// Count is the number of operands.
	Count int
	// Digits is the total of their coefficient digits.
	Digits uint64
	// MinExponent is the smallest operand exponent.
	MinExponent int32
	// MaxAdjusted is the largest adjusted exponent of a nonzero operand.
	MaxAdjusted int64
	// Nonzero reports whether any operand is nonzero.
	Nonzero bool
}

// ShapeOfSum reads the SumShape of values in one pass over their headers.
func ShapeOfSum(values ...Decimal) SumShape {
	plan, _ := sumScan(values)
	return plan.shape
}

// sumPlan is the header scan's result: the shape, the digit envelope and
// whether every operand is inline within 19 exponent places of emin.
type sumPlan struct {
	shape    SumShape
	envelope uint64
	inline   bool
}

// sumScan reads each operand's sign, digits and exponent without touching
// its coefficient beyond the digit count. ok is false when a
// count leaves uint64.
func sumScan(values []Decimal) (sumPlan, bool) {
	p := sumPlan{inline: true}
	p.shape.Count = len(values)
	if len(values) == 0 {
		return p, true
	}
	// The running shape stays in locals and a one-word coefficient takes
	// the one-word digit count, which keeps the scan of short operands
	// cheap beside their addition.
	minExponent := values[0].exponent()
	maxExponent := minExponent
	var total uint64
	var maxAdjusted int64
	inline, nonzero, ok := true, false, true
	for i := range values {
		v := &values[i]
		e := v.exponent()
		minExponent, maxExponent = min(minExponent, e), max(maxExponent, e)
		var digits uint64
		switch {
		case v.slow != nil:
			inline = false
			if v.isZero() {
				continue
			}
			view := coefficientViewOf(*v)
			var valid bool
			digits, valid = arithmeticDigits(&view)
			ok = ok && valid
		case v.words.hi != 0:
			digits = inlineDigits(v.words)
		case v.words.lo != 0:
			digits = uint64(wordDigits(v.words.lo))
		default:
			continue
		}
		var valid bool
		total, valid = arithmeticAdd(total, digits)
		ok = ok && valid
		if adjusted := int64(e) + int64(digits) - 1; !nonzero || adjusted > maxAdjusted {
			maxAdjusted = adjusted
		}
		nonzero = true
	}
	p.shape.MinExponent, p.shape.Digits, p.shape.MaxAdjusted, p.shape.Nonzero = minExponent, total, maxAdjusted, nonzero
	p.inline = inline && int64(maxExponent)-int64(minExponent) <= 19
	p.envelope, ok = sumEnvelope(p.shape, ok)
	return p, ok
}

// sumInlineShape is sumScan's inline verdict without the digit counts an
// unbudgeted call never reads: ok when every operand is inline within 19
// exponent places of the smallest exponent emin.
func sumInlineShape(values []Decimal) (emin int32, nonzero, ok bool) {
	emin = values[0].exponent()
	emax := emin
	var any uint64
	for i := range values {
		v := &values[i]
		if v.slow != nil {
			return 0, false, false
		}
		e := v.exponent()
		emin, emax = min(emin, e), max(emax, e)
		any |= v.words.lo | v.words.hi
	}
	return emin, any != 0, int64(emax)-int64(emin) <= 19
}

// sumEnvelope is L = amax − emin + 1 + ⌈log10 k⌉, or 1 when every operand
// is zero.
func sumEnvelope(s SumShape, ok bool) (uint64, bool) {
	if !s.Nonzero {
		return 1, ok
	}
	carries := uint64(0)
	for n := uint64(1); n < uint64(s.Count); n *= 10 {
		carries++
	}
	span := s.MaxAdjusted - int64(s.MinExponent) + 1
	total, valid := arithmeticAdd(uint64(span), carries)
	return total, ok && valid
}

// sumCharges returns the full work W = k + Σdᵢ + 2·t(L), whose header
// precharge is B = k.
func sumCharges(s SumShape, envelope uint64) (work uint64, ok bool) {
	passes, ok1 := arithmeticMul(2, digitLimbs(envelope))
	work, ok2 := checkedSum(uint64(s.Count), s.Digits, passes)
	return work, ok1 && ok2
}

func sumValues(values []Decimal, budget limits, op string) (Decimal, error) {
	if len(values) == 0 {
		return Decimal{}, nil
	}
	if budget.MaxDigits|budget.MaxWork == 0 || sumInlineBoundAdmitted(len(values), budget) {
		// Nothing is charged, or the budget admits every charge of the
		// inline shape, so that shape needs no digit counts: only the
		// exponent window and whether any operand is nonzero.
		if emin, nonzero, ok := sumInlineShape(values); ok {
			if !nonzero {
				return zeroDecimal(emin), nil
			}
			return sumInline(values, emin), nil
		}
	}
	return sumPlanned(values, budget, op)
}

// sumInlineSpan bounds MaxAdjusted − MinExponent + 1 over inline operands
// within 19 exponent places: a coefficient of at most 39 digits, 19 places
// above the smallest exponent.
const sumInlineSpan = 19 + 39

// sumInlineBoundAdmitted reports whether budget certainly admits the
// planned Sum of k operands of the inline shape, whatever their digits: it
// prices the dearest such shape with the planner's own envelope and
// charges, k coefficients of 39 digits spanning sumInlineSpan digits. Both
// grow with the digits and the span, so they bound every such call's.
func sumInlineBoundAdmitted(k int, budget limits) bool {
	worst := SumShape{Count: k, MaxAdjusted: sumInlineSpan - 1, Nonzero: true}
	var ok bool
	if worst.Digits, ok = arithmeticMul(uint64(k), inlineResultDigits); !ok {
		return false
	}
	envelope, ok := sumEnvelope(worst, true)
	work, ok2 := sumCharges(worst, envelope)
	return ok && ok2 && budget.admits(envelope, work)
}

// sumPlanned is the planned Sum of a nonempty list: the header scan, the
// charges and the admissions, then the inline or the limb accumulators. It
// owns every budget refusal.
func sumPlanned(values []Decimal, budget limits, op string) (Decimal, error) {
	if !admitted(budget.MaxWork, uint64(len(values)), true) {
		return arithmeticFailure(op, ErrInsufficientStorage)
	}
	p, ok := sumScan(values)
	if !ok || !admitted(budget.MaxDigits, p.envelope, true) {
		return arithmeticFailure(op, ErrInsufficientStorage)
	}
	work, ok := sumCharges(p.shape, p.envelope)
	if !admitted(budget.MaxWork, work, ok) {
		return arithmeticFailure(op, ErrInsufficientStorage)
	}
	if !p.shape.Nonzero {
		return zeroDecimal(p.shape.MinExponent), nil
	}
	if p.inline {
		return sumInline(values, p.shape.MinExponent), nil
	}
	return sumLimbs(values, p, op)
}

// sumInline adds inline operands within 19 exponent places of emin in two
// 256-bit accumulators: each scaled operand is below 2^128·10^19 < 2^192,
// so fewer than 2^64 of them cannot overflow. It returns exactly what
// sumLimbs returns (TestSumInlineMatchesLimbs).
func sumInline(values []Decimal, emin int32) Decimal {
	var positive, negative [4]uint64
	for i := range values {
		v := values[i]
		if v.isZero() {
			continue
		}
		scale := pow10Words[v.exponent()-emin]
		h0, l0 := bits.Mul64(v.words.lo, scale)
		h1, l1 := bits.Mul64(v.words.hi, scale)
		mid, carry := bits.Add64(h0, l1, 0)
		top := h1 + carry
		acc := &positive
		if v.negative() {
			acc = &negative
		}
		var c uint64
		acc[0], c = bits.Add64(acc[0], l0, 0)
		acc[1], c = bits.Add64(acc[1], mid, c)
		acc[2], c = bits.Add64(acc[2], top, c)
		acc[3] += c
	}
	result, resultNegative := positive, false
	if sumLess(positive, negative) {
		result, resultNegative = negative, true
		sumSubtract(&result, negative, positive)
	} else {
		sumSubtract(&result, positive, negative)
	}
	if result == [4]uint64{} {
		return zeroDecimal(emin)
	}
	if result[2] == 0 && result[3] == 0 {
		return inlineDecimal(uint128{result[0], result[1]}, emin, resultNegative)
	}
	// At most 2^256 < 10^78: nine base-10^9 limbs.
	var limbs [slowSmallLimbs]uint32
	n := 0
	for result != [4]uint64{} {
		var r uint64
		for j := 3; j >= 0; j-- {
			result[j], r = bits.Div64(r, result[j], decimalLimbBase)
		}
		limbs[n] = uint32(r)
		n++
	}
	return publishScratch(limbs[:n], emin, resultNegative)
}

func sumLess(a, b [4]uint64) bool {
	for j := 3; j >= 0; j-- {
		if a[j] != b[j] {
			return a[j] < b[j]
		}
	}
	return false
}

// sumSubtract sets *dst = a − b for a ≥ b.
func sumSubtract(dst *[4]uint64, a, b [4]uint64) {
	var borrow uint64
	for j := range 4 {
		dst[j], borrow = bits.Sub64(a[j], b[j], borrow)
	}
}

// sumLimbs is the general path: two accumulators of 64-bit sums of
// base-10^9 limbs, t(L)+1 limbs each, in one scratch allocation. Each
// operand adds at most two contributions below 10^9 per slot, so carries
// are normalized every 2^31 operands and once at the end.
func sumLimbs(values []Decimal, p sumPlan, op string) (Decimal, error) {
	emin := int64(p.shape.MinExponent)
	width, count, err := sumScratch(p.envelope, op)
	if err != nil {
		return Decimal{}, err
	}
	var stack [2 * sumStackLimbs]uint64
	var scratch []uint64
	if count <= len(stack) {
		scratch = stack[:count]
	} else {
		scratch = make([]uint64, count)
	}
	positive, negative := scratch[:width], scratch[width:]
	for i := range values {
		v := values[i]
		if v.isZero() {
			continue
		}
		acc := positive
		if v.negative() {
			acc = negative
		}
		offset := uint64(int64(v.exponent()) - emin)
		q, r := offset/9, offset%9
		scale := pow10Words[r]
		view := coefficientViewOf(v)
		for j := range view.count {
			x := uint64(view.limb(j)) * scale
			acc[q+uint64(j)] += x % decimalLimbBase
			acc[q+uint64(j)+1] += x / decimalLimbBase
		}
		if uint64(i)%(1<<31) == 1<<31-1 {
			sumNormalize(positive)
			sumNormalize(negative)
		}
	}
	sumNormalize(positive)
	sumNormalize(negative)
	resultNegative := false
	if sumLimbsLess(positive, negative) {
		positive, negative = negative, positive
		resultNegative = true
	}
	if width <= sumStackLimbs {
		var out [sumStackLimbs]uint32
		sumDifference(out[:width], positive, negative)
		return publishScratch(out[:width], int32(emin), resultNegative), nil
	}
	out := make([]uint32, width)
	sumDifference(out, positive, negative)
	return publishOwned(out, int32(emin), resultNegative), nil
}

// sumDifference writes positive − negative (normalized base-10^9, positive
// not smaller) into out.
func sumDifference(out []uint32, positive, negative []uint64) {
	var borrow uint64
	for j := range positive {
		d := positive[j] + decimalLimbBase - negative[j] - borrow
		out[j] = uint32(d % decimalLimbBase)
		borrow = 1 - d/decimalLimbBase
	}
}

// sumScratch plans the general path's buffers for a digit envelope: two
// accumulators of width = t(L) + 1 limbs, admitted physically as one
// allocation of 2·width limbs. sumLimbs and EstimateSum share it, so the
// estimate refuses exactly when the call would.
func sumScratch(envelope uint64, op string) (width uint64, count int, err error) {
	width = 1 + (envelope-1)/9 + 1
	count, err = arithmeticPhysicalLimbCount(2*width, op)
	return width, count, err
}

// sumStackLimbs bounds the accumulators and result kept on the stack, so
// a sum of up to about 280 digits allocates only its published holder.
const sumStackLimbs = 32

func sumNormalize(acc []uint64) {
	var carry uint64
	for j := range acc {
		v := acc[j] + carry
		acc[j] = v % decimalLimbBase
		carry = v / decimalLimbBase
	}
}

func sumLimbsLess(a, b []uint64) bool {
	for j, v := range slices.Backward(a) {
		if v != b[j] {
			return v < b[j]
		}
	}
	return false
}
