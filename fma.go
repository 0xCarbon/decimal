// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"math"
	"math/bits"
)

// FMAWithContext returns d·y + z rounded once under ctx: the exact
// product is added to z and only the sum is rounded, so the result can
// differ from MulWithContext then AddWithContext, which round twice. The
// product's exponent ex+ey is internal and carried in int64; only the
// published exponent must fit int32. The operands are reduced as
// AddWithContext reduces them, before the product is built: a
// nonzero z far below the product, or a product far below z, contributes
// one sticky digit, and a zero product or zero z far below the other is
// clamped to just below the rounding position, so the work does not grow
// with the exponent gap. Context{} returns the exact d·y + z at the
// preferred exponent min(ex+ey, ez) with zero Conditions: Mul then Add's
// value, cohort and ErrExponentRange when ex+ey leaves int32. There is no
// bare FMA: with unlimited precision, Mul then Add already computes
// d·y + z exactly.
func (d Decimal) FMAWithContext(y, z Decimal, ctx Context) (Decimal, Conditions, error) {
	return d.contextFMA(y, z, ctx, ctx.arith, "FMAWithContext")
}

// fmaStackLimbs is the product scratch kept on the stack (432 digits);
// a longer product takes one heap buffer.
const fmaStackLimbs = 48

// fmaProductTerm returns the product's term before its coefficient exists
// (the plan-digit envelope dx+dy at exponent ex+ey) and the Mul work charge
// that precedes the sum, through fmaProductPlan.
func fmaProductTerm(x, y *coefficientView, exponent int64, negative bool) (addTerm, uint64, bool) {
	if x.count == 0 || y.count == 0 {
		digits, charge, _ := fmaProductPlan(0, 0)
		return addTerm{exponent: exponent, digits: digits, zero: true}, charge, true
	}
	dx, validX := arithmeticDigits(x)
	dy, validY := arithmeticDigits(y)
	digits, charge, valid := fmaProductPlan(dx, dy)
	return addTerm{exponent: exponent, digits: digits, negative: negative}, charge, validX && validY && valid
}

// fmaProductPlan is the FMA planner shared with the estimators: for nonzero dx- and dy-digit factors, the product's plan digits
// dx+dy and Mul's charge t(dx)·t(dy)+dx+dy; for a zero factor (dx or dy
// 0), one digit and Mul's zero charge 1.
func fmaProductPlan(dx, dy uint64) (digits, charge uint64, valid bool) {
	if dx == 0 || dy == 0 {
		return 1, 1, true
	}
	digits, validD := arithmeticAdd(dx, dy)
	charge, validC := mulWorkCharge(dx, dy, digits)
	return digits, charge, validD && validC
}

// fmaProduct writes x·y with the Mul kernel into stack when it fits, and
// otherwise into one heap buffer, and returns the trimmed product's view
// and that heap buffer (nil on the stack), which the bare kernel hands
// over when the sum is the product itself.
func fmaProduct(x, y *coefficientView, stack []uint32, op string) (coefficientView, []uint32, error) {
	count, err := arithmeticPhysicalLimbCount(uint64(x.count)+uint64(y.count), op)
	if err != nil {
		return coefficientView{}, nil, err
	}
	if count <= len(stack) {
		out := stack[:count]
		if !fillMultiply(out, x, y) {
			return coefficientView{}, nil, newError(op, ErrInsufficientStorage)
		}
		out = trimLimbs(out)
		return coefficientView{slow: out, count: len(out)}, nil, nil
	}
	heap := make([]uint32, count)
	if !fillMultiply(heap, x, y) {
		return coefficientView{}, nil, newError(op, ErrInsufficientStorage)
	}
	heap = trimLimbs(heap)
	return coefficientView{slow: heap, count: len(heap)}, heap, nil
}

// fma is the exact kernel behind Context{} (precision 0): Mul's exponent check, then the Add/Sub plan over
// the product's shape, the product, and the sum.
func (d Decimal) fma(y, z Decimal, budget limits, op string) (Decimal, error) {
	e := int64(d.exponent()) + int64(y.exponent())
	if e < math.MinInt32 || e > math.MaxInt32 {
		return arithmeticFailure(op, ErrExponentRange)
	}
	if budget.admits(fmaInlineDigits, fmaInlineWork) && d.slow == nil && y.slow == nil {
		if product, ok := inlineMul(d, y); ok {
			if sum, ok := inlineAddSub(product, z, false); ok {
				return sum, nil
			}
			if budget.MaxDigits|budget.MaxWork == 0 {
				return product.addSubLimbs(z, budget, op, false)
			}
		}
	}
	return d.fmaTerms(y, z, e, budget, op)
}

// The inline FMA paths serve a budgeted call when the budget admits these
// bounds of the product-term path's charges, over every shape they return
// for: factors of dx and dy digits whose product stays below 2^128, so the
// product plans dx+dy ≤ 40 digits and Mul charges t(dx)·t(dy)+dx+dy ≤ 49
// (at most nine tile pairs, at 20 and 20 digits); an addend of at most 39
// digits, so the inputs total at most 79 digits; and an aligned span L of
// at most 40 digits when the exact sum stays inline, or at most 40+38 = 78
// when the 256-bit sum serves an exponent gap of at most 38.
//
// The bare form returns only an inline exact sum. Opposite signs charge
// 49 + 2·79 + L ≤ 247 and need L ≤ 40 result digits; equal signs charge
// 49 + 79 + L + 1 ≤ 169 and are admitted without a carry scan when the
// digit cap exceeds L, so a cap of 41 admits every case; a zero operand
// charges less on both axes.
//
// The context form returns only an inline result, of N ≤ 39 digits, and the
// finisher adds 2N+1 to the base charge, which is largest for opposite
// signs. An inline exact sum charges at most 49 + 2·79 + 40 + 2·39 + 1 =
// 326. The 256-bit sum serves only a precision that keeps the rounded
// coefficient inline, so N ≤ 38 there: at most 49 + 2·79 + 78 + 2·38 + 1 =
// 362. The context planner's reduction never raises a span or a digit
// count, so the bounds hold for the reduced operands too.
const (
	fmaInlineDigits        = 40 + 1
	fmaInlineWork          = 49 + 2*79 + 40
	contextFMAInlineDigits = inlineResultDigits
	contextFMAInlineWork   = 49 + 2*79 + 78 + 2*38 + 1
)

// fmaTerms is the bare general path, kept out of fma so the inline path
// does not set up the product scratch's frame.
func (d Decimal) fmaTerms(y, z Decimal, e int64, budget limits, op string) (Decimal, error) {
	xv, yv := coefficientViewOf(d), coefficientViewOf(y)
	a, pre, validA := fmaProductTerm(&xv, &yv, e, d.negative() != y.negative())
	var b addTerm
	if !b.load(z, false) || !validA {
		return arithmeticFailure(op, ErrInsufficientStorage)
	}
	p, err := addSubAdmit(&a, &b, budget, pre, op)
	if err != nil {
		return Decimal{}, err
	}
	var stack [fmaStackLimbs]uint32
	var heap []uint32
	if !a.zero {
		if a.v, heap, err = fmaProduct(&xv, &yv, stack[:], op); err != nil {
			return Decimal{}, err
		}
	}
	switch p.unchanged(&a, &b) {
	case addSelfA:
		// The sum is the product itself: a heap product is handed over
		// without a copy, as Mul publishes it; stack scratch is copied.
		if heap != nil {
			return publishOwned(heap, int32(e), a.negative), nil
		}
		return publishScratch(a.v.slow, int32(e), a.negative), nil
	case addSelfB:
		return z, nil
	}
	return addSubFinish(&p, &a, &b, budget, op)
}

// contextFMA is the context kernel: the context Add/Sub plan and finisher
// over the product term, with the product's exponent in int64.
func (d Decimal) contextFMA(y, z Decimal, ctx Context, budget limits, op string) (Decimal, Conditions, error) {
	if ctx.precision == 0 {
		result, err := d.fma(y, z, budget, op)
		return result, 0, err
	}
	e := int64(d.exponent()) + int64(y.exponent())
	if budget.admits(contextFMAInlineDigits, contextFMAInlineWork) && d.slow == nil && y.slow == nil && e >= math.MinInt32 && e <= math.MaxInt32 {
		if product, ok := inlineMul(d, y); ok {
			if result, events, served, err := product.contextAddSubInline(z, ctx, op, false); served {
				return result, events, err
			}
			if budget.MaxDigits|budget.MaxWork == 0 {
				// The product is exact, so its sum with z under the context
				// is the FMA; the Add kernel charges nothing unbudgeted.
				return product.contextAddSubGeneral(z, ctx, op, false, true, nil)
			}
		} else if budget.MaxDigits|budget.MaxWork == 0 {
			// The product leaves two words: its exact sum with z in 256
			// bits, rounded once as the 256-bit Add/Sub sum is.
			if sum, exponent, negative, ok := wideFMASum(d, y, z, e); ok {
				if rounded, events, ok := contextRoundWide(sum, exponent, negative, ctx); ok {
					return contextOutcome(rounded, events, ctx.traps, op)
				}
			}
		}
	}
	return d.contextFMATerms(y, z, e, ctx, budget, op)
}

// wideFMASum is the exact d·y + z of nonzero inline operands, at the
// smaller of the product's exponent e and z's, when the 256-bit product
// and the addend align within 38 places and their sum stays below 2^256.
// ok is false for a limb or zero addend, a wider gap, a scaled product or
// sum of 2^256 or more, and an exact zero; the product-term path owns
// those.
//
//go:noinline
func wideFMASum(d, y, z Decimal, e int64) (sum wide256, exponent int64, negative, ok bool) {
	if z.slow != nil || z.isZero() {
		return sum, 0, false, false
	}
	product := mulWide(d.words, y.words)
	addend := wide256{z.words.lo, z.words.hi}
	ze := int64(z.exponent())
	exponent = min(e, ze)
	switch gap := e - ze; {
	case gap > 38 || gap < -38:
		return sum, 0, false, false
	case gap > 0:
		if !product.mulWords(pow10Wide[gap]) {
			return sum, 0, false, false
		}
	case gap < 0:
		addend = mulWide(z.words, pow10Wide[-gap])
	}
	negative = d.negative() != y.negative()
	if negative == z.negative() {
		var carry uint64
		for i := range sum {
			sum[i], carry = bits.Add64(product[i], addend[i], carry)
		}
		return sum, exponent, negative, carry == 0
	}
	switch product.cmp(addend) {
	case 0:
		return sum, 0, false, false
	case 1:
		return subWide(product, addend), exponent, negative, true
	}
	return subWide(addend, product), exponent, !negative, true
}

// contextFMATerms is the context general path over the product term. The
// product and addend are reduced by the context planner before anything is
// charged or built (fmaReduce), budgeted or not, so a remote or zero
// operand costs O(p) and the charges follow the reduced spans. A product
// that survives is built between admission and the finisher.
func (d Decimal) contextFMATerms(y, z Decimal, e int64, ctx Context, budget limits, op string) (Decimal, Conditions, error) {
	xv, yv := coefficientViewOf(d), coefficientViewOf(y)
	a, pre, validA := fmaProductTerm(&xv, &yv, e, d.negative() != y.negative())
	var b addTerm
	if !b.load(z, false) || !validA {
		return contextFailure(op, ErrInsufficientStorage)
	}
	fmaReduce(&a, &b, ctx)
	var p contextAddSubPlan
	if err := p.admit(&a, &b, budget, pre, op); err != nil {
		return Decimal{}, 0, err
	}
	var stack [fmaStackLimbs]uint32
	if !a.zero && a.v.count == 0 {
		var err error
		if a.v, _, err = fmaProduct(&xv, &yv, stack[:], op); err != nil {
			return Decimal{}, 0, err
		}
	}
	return p.finish(&a, &b, ctx, budget, op)
}

// fmaReduce applies the context planner to the unbuilt product term a and
// the addend term b with int64 exponents (contextReduceSpans, which never
// gives up below int32). The product plans dx+dy digits but has dx+dy−1 or
// dx+dy, and the planner reads that bracket on its safe side.
func fmaReduce(a, b *addTerm, ctx Context) {
	sa := reduceSpan{exponent: a.exponent, negative: a.negative}
	if !a.zero {
		sa.lo, sa.hi = a.digits-1, a.digits
	}
	sb := reduceSpan{exponent: b.exponent, negative: b.negative}
	if !b.zero {
		sb.lo, sb.hi = b.digits, b.digits
	}
	ra, rb := contextReduceSpans(sa, sb, ctx)
	a.reduce(sa, ra)
	b.reduce(sb, rb)
}
