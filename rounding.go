// SPDX-License-Identifier: Apache-2.0

package decimal

// RoundToPrecision rounds to at most precision significant digits under the
// selected mode. A value that already fits returns unchanged, cohort included,
// with no Conditions (GDA plus); precision 0 is the identity. Otherwise the
// value is rounded once, with Inexact|Rounded and the direction, or Rounded
// alone for a zero-only discard, which Exact permits. RoundToPrecision(3,
// TiesToEven) of 12345 is 1.23E+4; of 1.20 it is 1.20.
func (d Decimal) RoundToPrecision(precision uint32, mode RoundingMode) (Decimal, Conditions, error) {
	if mode > Exact {
		return quantizeInvalidMode("RoundToPrecision")
	}
	return d.roundToPrecision(Context{precision: precision, rounding: mode}, "RoundToPrecision")
}

// RoundToPrecisionWithContext rounds to ctx's precision under its mode,
// guards and traps. A value that fits within the precision and guards
// returns unchanged; Context{} is the identity.
func (d Decimal) RoundToPrecisionWithContext(ctx Context) (Decimal, Conditions, error) {
	return d.roundToPrecision(ctx, "RoundToPrecisionWithContext")
}

// roundToPrecision is GDA plus: context addition of a zero at the value's
// own exponent, so the exact sum is the value in its cohort and the context
// finisher rounds it once. An inline value is that exact sum as it stands,
// so it takes the context addition's inline steps directly, under the same
// budget gate: returned as it is when it fits, or rounded once in words.
func (d Decimal) roundToPrecision(ctx Context, op string) (Decimal, Conditions, error) {
	if d.slow == nil && ctx.precision != 0 && ctx.arith.admits(inlineResultDigits, inlineContextAddSubWork) {
		if contextExactFits(d, ctx) {
			return d, 0, nil
		}
		if rounded, events, ok := contextRoundInline(d, ctx); ok {
			return contextOutcome(rounded, events, ctx.traps, op)
		}
	}
	return d.contextAddSub(zeroDecimal(d.exponent()), ctx, op, false, true, nil)
}

// The inline RoundToMultiple path serves a budgeted call when the budget
// admits these bounds of the general path's charges over every shape it
// returns for. The quotient r of N_r digits comes from the inline
// DivToExponent kernel, whose whole tariff B + 2N_r + 1 is at most
// inlineDivWork (the bound of DivToExponent's own gate, for the same
// kernel). The product r·Cm
// stays below 2^128, so N_r + digits(m) ≤ 40: that is the largest result
// digit count the general path checks, the quotient's own cap is then at
// least N_r, and Mul charges at most nine tile pairs plus those 40 digits,
// 49. A zero quotient charges less on both axes.
const (
	roundToMultipleInlineDigits = 40
	roundToMultipleInlineWork   = inlineDivWork + 9 + 40
)

// RoundToMultiple rounds to the multiple of m nearest the value under the
// mode: r·m where the integer r is decided once on the
// exact rational d/m, never on a truncated quotient, so there is no double
// rounding. The result has m's exponent. It is exact with no Conditions
// when d/m is integral, and otherwise reports Inexact|Rounded and the
// direction. m must be positive; zero or negative m is ErrInvalidOperation.
// Cash rounding of 2.525 to 0.05 is 2.50 under TiesToEven and 2.55 under
// TiesAwayFromZero.
func (d Decimal) RoundToMultiple(m Decimal, mode RoundingMode) (Decimal, Conditions, error) {
	return d.roundToMultiple(m, mode, limits{}, "RoundToMultiple")
}

// RoundToMultipleWithBudget adds an operation-local budget: the
// DivToExponent charge of d/m at exponent 0 with W = B + 2N_r + 1 for the
// quotient's N_r digits, plus the Mul charge of r·m. The digit cap bounds
// the result, which has at most N_r + digits(m) digits.
func (d Decimal) RoundToMultipleWithBudget(m Decimal, mode RoundingMode, budget Budget) (Decimal, Conditions, error) {
	return d.roundToMultiple(m, mode, budget.arith(), "RoundToMultipleWithBudget")
}

func (d Decimal) roundToMultiple(m Decimal, mode RoundingMode, budget limits, op string) (Decimal, Conditions, error) {
	if mode <= Exact && !m.negative() && inlineDivShape(d, m) {
		// r = round(d/Cm) at m's exponent by the inline DivToExponent
		// kernel, then r·Cm by the inline product: the general path's two
		// steps on words. An Exact refusal and every overflow defer, and so
		// does a budget that admits neither the bounds above nor the
		// general path's own charges for this quotient.
		unit := m.withExponent(0)
		if r, events, refused, ok := inlineDivToExponent(d, unit, m.exponent(), mode); ok && !refused &&
			(budget.admits(roundToMultipleInlineDigits, roundToMultipleInlineWork) || roundToMultipleInlineAdmitted(d, m, r, budget)) {
			if events&Inexact == 0 {
				events = 0
			}
			if r.isZero() {
				return zeroDecimal(m.exponent()), events, nil
			}
			if product, ok := inlineMul(r.withExponent(0), unit); ok {
				return product.withExponent(m.exponent()), events, nil
			}
		}
	}
	return d.roundToMultipleLimbs(m, mode, budget, op)
}

// roundToMultipleInlineAdmitted reports whether budget admits
// roundToMultipleLimbs's charges for nonzero inline d and m whose rounded
// quotient is r: the division plan's precharge B at m's exponent, and
// either W = B + 3 and one digit for a zero quotient, or the N_r + dm
// result digits and W = B + 2N_r + 1 plus the Mul charge of r·Cm. Those
// final caps imply the earlier ones: the precharge alone, and the
// quotient's digit cap, since a quotient planned above it has more than
// cap − dm digits.
//
//go:noinline
func roundToMultipleInlineAdmitted(d, m, r Decimal, budget limits) bool {
	dm := inlineDigits(m.words)
	s := divSource{dx: inlineDigits(d.words), dy: dm, ideal: int64(d.exponent())}
	p := s.plan(int64(m.exponent()))
	if !p.ok {
		return false
	}
	if r.isZero() {
		work, ok := contextFinalCharge(p.charge, 1)
		return ok && budget.admits(1, work)
	}
	nr := inlineDigits(r.words)
	quotientWork, ok1 := contextFinalCharge(p.charge, nr)
	mulWork, ok2 := mulWorkCharge(nr, dm, nr+dm)
	total, ok3 := arithmeticAdd(quotientWork, mulWork)
	return ok1 && ok2 && ok3 && budget.admits(nr+dm, total)
}

// roundToMultipleLimbs is the general RoundToMultiple path. It owns every
// error, budget charge and refusal.
func (d Decimal) roundToMultipleLimbs(m Decimal, mode RoundingMode, budget limits, op string) (Decimal, Conditions, error) {
	if mode > Exact {
		return quantizeInvalidMode(op)
	}
	if m.isZero() || m.negative() {
		return contextFailure(op, ErrInvalidOperation)
	}
	mv := coefficientViewOf(m)
	dm, ok := arithmeticDigits(&mv)
	if !ok {
		return contextFailure(op, ErrInsufficientStorage)
	}
	// The digit envelope is N_r + dm, so a quotient may have
	// at most cap − dm digits. At or below dm digits only a zero quotient
	// fits, which needs |d| < m; otherwise refuse before any scratch.
	quotientBudget := limits{MaxWork: budget.MaxWork}
	if limit := budget.MaxDigits; limit != 0 {
		quotientBudget.MaxDigits = limit - min(limit-1, dm)
		if limit <= dm && !d.isZero() {
			dv := coefficientViewOf(d)
			if compareMagnitude(&dv, int64(d.exponent()), &mv, int64(m.exponent())) >= 0 {
				return contextFailure(op, ErrInsufficientStorage)
			}
		}
	}
	unit := m.withExponent(0).withNegative(false)
	var stack [divStackLimbs]uint32
	o, events, charge, err := d.divToExponentRound(&stack, unit, m.exponent(), mode, quotientBudget, op)
	if err != nil {
		return Decimal{}, 0, err
	}
	// Only a value change is reported: an integral quotient whose ideal
	// exponent lies below the target is not a rounding.
	if events&Inexact == 0 {
		events = 0
	}
	r := trimLimbs(o.r)
	if len(r) == 0 {
		if !admitted(budget.MaxDigits, 1, true) || !contextFinalWork(charge, 1, budget.MaxWork) {
			return contextFailure(op, ErrInsufficientStorage)
		}
		return zeroDecimal(m.exponent()), events, nil
	}
	nr := limbsDigits(r)
	digits, ok := arithmeticAdd(nr, dm)
	if !admitted(budget.MaxDigits, digits, ok) {
		return contextFailure(op, ErrInsufficientStorage)
	}
	if budget.MaxWork != 0 {
		quotientWork, ok1 := contextFinalCharge(charge, nr)
		mulWork, ok2 := mulWorkCharge(nr, dm, digits)
		total, ok3 := arithmeticAdd(quotientWork, mulWork)
		if !admitted(budget.MaxWork, total, ok1 && ok2 && ok3) {
			return contextFailure(op, ErrInsufficientStorage)
		}
	}
	quotient := coefficientView{slow: r, count: len(r)}
	count, err := arithmeticPhysicalLimbCount(uint64(len(r)+mv.count), op)
	if err != nil {
		return Decimal{}, 0, err
	}
	negative := d.negative()
	if digits <= 38 {
		var inline [6]uint32
		out := inline[:count]
		if !fillMultiply(out, &quotient, &mv) {
			return contextFailure(op, ErrInsufficientStorage)
		}
		return publishInlineArithmetic(out, m.exponent(), negative), events, nil
	}
	if count <= slowSmallLimbs+1 {
		var scratch [slowSmallLimbs + 1]uint32
		out := scratch[:count]
		if !fillMultiply(out, &quotient, &mv) {
			return contextFailure(op, ErrInsufficientStorage)
		}
		return publishScratch(out, m.exponent(), negative), events, nil
	}
	out := make([]uint32, count)
	if !fillMultiply(out, &quotient, &mv) {
		return contextFailure(op, ErrInsufficientStorage)
	}
	return publishOwned(out, m.exponent(), negative), events, nil
}
