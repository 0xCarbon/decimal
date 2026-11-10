// SPDX-License-Identifier: Apache-2.0

package decimal

const (
	lnRemedy    = "non-terminating logarithm: supply a finite-precision context (LnWithContext)"
	log10Remedy = "non-terminating logarithm: supply a finite-precision context (Log10WithContext)"
)

// Ln returns the natural logarithm of d exactly: Ln(1) is 0. Every other
// positive d has an irrational logarithm and returns a *Error with
// Condition Inexact and a remedy naming LnWithContext. A negative d returns
// ErrInvalidOperation and zero returns ErrDivisionByZero, since the finite
// value space has no infinite pole.
func (d Decimal) Ln() (Decimal, error) {
	result, _, err := d.ln(Context{}, Budget{}, false, "Ln")
	return result, err
}

// LnWithContext rounds ln d once to the context precision in the context's
// mode, with guards and traps. Ln(1) is exactly 0E0; every other result is
// inexact, so the Exact mode refuses it. Context{} behaves as Ln.
func (d Decimal) LnWithContext(ctx Context) (Decimal, Conditions, error) {
	return d.ln(ctx, ctx.Budget(), false, "LnWithContext")
}

// Log10 returns the base-ten logarithm of d exactly. For a power of ten
// 10^k it is the integer k at exponent 0; every other positive d has an
// irrational logarithm and returns a *Error with Condition Inexact
// and a remedy naming Log10WithContext. A negative d returns
// ErrInvalidOperation and zero returns ErrDivisionByZero.
func (d Decimal) Log10() (Decimal, error) {
	result, _, err := d.ln(Context{}, Budget{}, true, "Log10")
	return result, err
}

// Log10WithContext rounds log10 d once to the context precision in the
// context's mode, with guards and traps. The exact integer of a power of
// ten keeps exponent 0 when it fits the precision and otherwise loses only
// zeros (Rounded) or rounds as any other value.
func (d Decimal) Log10WithContext(ctx Context) (Decimal, Conditions, error) {
	return d.ln(ctx, ctx.Budget(), true, "Log10WithContext")
}

func (d Decimal) ln(ctx Context, budget Budget, ten bool, op string) (Decimal, Conditions, error) {
	ev := newEvaluator(budget)
	return ev.ln(d, ctx, ten, op)
}

func (ev *evaluator) ln(x Decimal, ctx Context, ten bool, op string) (Decimal, Conditions, error) {
	switch {
	case x.isZero():
		return contextFailure(op, ErrDivisionByZero)
	case x.negative():
		return contextFailure(op, ErrInvalidOperation)
	}
	pr := evalProblem{kind: evalLn}
	if ten {
		pr.kind = evalLog10
	}
	v := coefficientViewOf(x)
	digits, _ := arithmeticDigits(&v)
	pr.ln = ev.newLnInput(v, digits, int64(x.exponent()))
	if !ev.ok() {
		return ev.failure(op)
	}
	if pr.ln.unit {
		// x = 10^k: ln 1 = 0 and log10 x = k, exact at exponent 0.
		k := pr.ln.k
		if k == 0 {
			return ev.finishZero(op)
		}
		if ten {
			var buf [4]uint32
			n := evalSmall(buf[:], uint64(max(k, -k)), false)
			return ev.finishExact(buf[:len(n.m):len(buf)], 0, 0, k < 0, &ctx, op)
		}
	}
	if ctx.precision == 0 {
		remedy := lnRemedy
		if ten {
			remedy = log10Remedy
		}
		return Decimal{}, 0, conditionError(op, Inexact, remedy)
	}
	if ctx.rounding == Exact {
		return contextExactRefusal(op)
	}
	return ev.certify(&pr, &ctx, op)
}
