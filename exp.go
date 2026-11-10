// SPDX-License-Identifier: Apache-2.0

package decimal

import "math"

// Exp, Ln, Log10 and PowDecimal use adaptive certified evaluation. A
// finite context result is correctly rounded in every mode: the value is
// enclosed by certified directed bounds (enclosure.go, elementary.go) at a
// working precision that doubles until the enclosure proves the rounding
// input, which the shared round-once finisher then rounds once. An exact
// result that is not a finite decimal refuses; no fixed guard-digit count
// or iteration cap replaces the proof. Every phase is admitted against one
// Budget before it runs.

const expRemedy = "non-terminating exponential: supply a finite-precision context (ExpWithContext)"

// Exp returns e^d exactly: Exp(0) is 1. Every other finite d has an
// irrational power and returns a *Error with Condition Inexact and
// a remedy naming ExpWithContext.
func (d Decimal) Exp() (Decimal, error) {
	result, _, err := d.exp(Context{}, Budget{}, "Exp")
	return result, err
}

// ExpWithContext rounds e^d once to the context precision in the context's
// mode, with guards and traps. Exp(0) is exactly 1E0; every other result is
// inexact, so the Exact mode refuses it. A result beyond the stored exponent
// range without guards returns ErrExponentRange; guards overflow or
// underflow as the context arithmetic does. Context{} behaves as Exp.
func (d Decimal) ExpWithContext(ctx Context) (Decimal, Conditions, error) {
	return d.exp(ctx, ctx.Budget(), "ExpWithContext")
}

func (d Decimal) exp(ctx Context, budget Budget, op string) (Decimal, Conditions, error) {
	ev := newEvaluator(budget)
	return ev.exp(d, ctx, op)
}

func (ev *evaluator) exp(x Decimal, ctx Context, op string) (Decimal, Conditions, error) {
	if x.isZero() {
		one := [2]uint32{1}
		return ev.finishExact(one[:1], 0, 0, false, &ctx, op)
	}
	if ctx.precision == 0 {
		return Decimal{}, 0, conditionError(op, Inexact, expRemedy)
	}
	if ctx.rounding == Exact {
		return contextExactRefusal(op)
	}
	pr := evalProblem{kind: evalExp}
	pr.x.load(x)
	pr.xDigits, _ = arithmeticDigits(&pr.x)
	pr.xExp, pr.xNeg = int64(x.exponent()), x.negative()
	return ev.certify(&pr, &ctx, op)
}

// finishExact publishes an exact nonzero result r·10^t, r holding a spare
// limb, at its chosen cohort: as is under an unlimited context, otherwise
// once through the finisher with its ideal exponent.
func (ev *evaluator) finishExact(r []uint32, t, ideal int64, neg bool, ctx *Context, op string) (Decimal, Conditions, error) {
	if ctx.precision == 0 {
		result := ev.publish(r, t, neg)
		if !ev.ok() {
			return ev.failure(op)
		}
		return result, 0, nil
	}
	var etiny int64
	if ctx.guarded {
		etiny = int64(ctx.guards.Emin) - (int64(ctx.precision) - 1)
	}
	return ev.finish(r, divExactClass, t, etiny, ideal, neg, ctx, op)
}

// evalKind selects a certified evaluation.
type evalKind uint8

const (
	evalExp evalKind = iota
	evalLn
	evalLog10
	evalPow
	evalSin
	evalCos
	evalTan
	evalAsin
	evalAcos
	evalAtan
	evalAtan2
	evalSinh
	evalCosh
	evalTanh
	evalAsinh
	evalAcosh
	evalAtanh
)

// evalSlots bounds the buffers one stage holds at once, per kind.
var evalSlots = [...]int{evalExp: 30, evalLn: 32, evalLog10: 36, evalPow: 44,
	evalSin: 48, evalCos: 48, evalTan: 52, evalAsin: 52, evalAcos: 52, evalAtan: 48, evalAtan2: 56,
	evalSinh: 48, evalCosh: 48, evalTanh: 56, evalAsinh: 60, evalAcosh: 64, evalAtanh: 60}

// evalProblem is one certified evaluation: the exp argument x, or the
// logarithm/power base reduced in ln, and the power exponent y and sign.
type evalProblem struct {
	kind    evalKind
	x, y    coefficientView
	xDigits uint64
	yDigits uint64
	xExp    int64
	yExp    int64
	xNeg    bool
	yNeg    bool
	neg     bool
	swap    bool // Atan2: |y| > |x|, so atan takes x/y
	ln      lnInput
}

// evalFirstDigits is the first stage's working digits for precision p.
func evalFirstDigits(p uint64) uint64 { return max(p, 16) + 8 }

// evalStageLimbs is a stage's limb count L for w working digits.
func evalStageLimbs(w uint64) int { return evalLimbs(w + 9) }

// certify encloses the problem at w = max(p,16)+8 working digits and
// doubles w until the enclosure certifies the rounding input. There is no
// iteration cap: refinement stops only on certification or refusal.
func (ev *evaluator) certify(pr *evalProblem, ctx *Context, op string) (Decimal, Conditions, error) {
	p := uint64(ctx.precision)
	var etiny int64
	if ctx.guarded {
		etiny = int64(ctx.guards.Emin) - int64(p-1)
	}
	w := evalFirstDigits(p)
	for {
		// At least w digits below a short top limb; a stage whose buffers
		// cannot be indexed by int on this target is a storage refusal.
		if (w+17)/9 > uint64(math.MaxInt/64) {
			ev.fail(evaluationStatus{code: ErrInsufficientStorage})
			return ev.failure(op)
		}
		L := evalStageLimbs(w)
		// Buffers hold three enclosure widths plus the ln reduction's
		// leading zero limbs and the final prefix of p+2 digits.
		size := 3*(L+pr.ln.zeros+8) + evalLimbs(p+2) + 8
		cells, ok1 := arithmeticMul(uint64(size), uint64(evalSlots[pr.kind]))
		if !ok1 {
			ev.fail(evaluationStatus{code: ErrInsufficientStorage})
			return ev.failure(op)
		}
		ev.stages++
		st := evalStage{ar: ev.arena(cells), L: L, size: size}
		result, conditions, err, done := ev.stage(pr, &st, ctx, etiny, op)
		ev.release(&st.ar)
		if done {
			return result, conditions, err
		}
		if !ev.ok() {
			return ev.failure(op)
		}
		if w > 1<<60 {
			ev.fail(evaluationStatus{code: ErrInsufficientStorage})
			return ev.failure(op)
		}
		w *= 2
	}
}

// stage runs one working precision and reports whether it decided.
func (ev *evaluator) stage(pr *evalProblem, st *evalStage, ctx *Context, etiny int64, op string) (Decimal, Conditions, error, bool) {
	lb, hb, ra, rb := st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev)
	if !ev.ok() || !ev.charge(1) {
		return Decimal{}, 0, nil, false
	}
	L := st.L
	var lo, hi evalNum
	rng := evalInRange
	switch pr.kind {
	case evalExp:
		zl, zh := st.buf(ev), st.buf(ev)
		// |x| < 10^11 in range: two more limbs keep r = x − k·ln 10 at L.
		zlo := ev.load(zl, &pr.x, pr.xDigits, pr.xExp, pr.xNeg, L+2, false)
		zhi := ev.load(zh, &pr.x, pr.xDigits, pr.xExp, pr.xNeg, L+2, true)
		lo, hi, rng = ev.expEnclose(st, lb, hb, zlo, zhi, L)
	case evalLn:
		lo, hi = ev.lnEnclose(st, lb, hb, &pr.ln, L)
	case evalLog10:
		lo, hi = ev.log10Enclose(st, lb, hb, &pr.ln, L)
	case evalPow:
		lo, hi, rng = ev.powEnclose(st, lb, hb, pr, L)
	case evalSin, evalCos, evalTan:
		lo, hi, rng = ev.sinCosTanEnclose(st, lb, hb, pr, L)
	case evalAsin, evalAcos, evalAtan, evalAtan2:
		lo, hi, rng = ev.inverseTrigEnclose(st, lb, hb, pr, L)
	default:
		lo, hi, rng = ev.hyperbolicEnclose(st, lb, hb, pr, L)
	}
	if !ev.ok() {
		return Decimal{}, 0, nil, false
	}
	switch rng {
	case evalHuge:
		if ctx.guarded {
			result, conditions, err := ev.overflow(pr.neg, ctx, op)
			return result, conditions, err, true
		}
		result, conditions, err := contextFailure(op, ErrExponentRange)
		return result, conditions, err, true
	case evalTiny:
		if ctx.guarded {
			// Below every guarded quantum by far: zero or one quantum.
			result, conditions, err := ev.finish(ra[:0], divBelow, etiny, etiny, etiny, pr.neg, ctx, op)
			return result, conditions, err, true
		}
		result, conditions, err := contextFailure(op, ErrExponentRange)
		return result, conditions, err, true
	case evalWide:
		return Decimal{}, 0, nil, false
	}
	r, tPrime, class, neg, ok := ev.classify(lo, hi, ctx, etiny, ra, rb)
	if !ok {
		return Decimal{}, 0, nil, false
	}
	result, conditions, err := ev.finish(r, class, tPrime, etiny, tPrime, neg, ctx, op)
	return result, conditions, err, true
}
