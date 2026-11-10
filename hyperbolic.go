// SPDX-License-Identifier: Apache-2.0

package decimal

// positiveSeries encloses Σ t_j for t_0 = first and
// t_j = t_{j−1}·ratio/((2j−1+off)(2j+off)), off 0 for cosh and 1 for sinh,
// with every term ratio at most 1/8 (|a| ≤ 1/2), at L limbs: the sum at
// one guard limb, rounded once.
func (ev *evaluator) positiveSeries(st *evalStage, dst []uint32, first, ratio evalNum, off uint64, L int, up bool) evalNum {
	mark := st.scope()
	defer st.restore(mark)
	return ev.round(dst, ev.positiveSum(st, first, ratio, off, L+1, up), L, up)
}

// positiveSum is positiveSeries at W limbs in the stage's scratch, which
// the caller scopes. The tail after the last added term t_N is at most
// t_N/7, which the upper bound adds. The loop stops on a term below one
// unit of the sum, so the tail can carry the true value past the unit that
// term's addition rounded to (TestPositiveSeriesEnclosesTailCriticalArguments).
// The tail addend t_N/7 lies below that unit, so the upper bound rises by
// exactly one unit for any divisor at least 7.
func (ev *evaluator) positiveSum(st *evalStage, first, ratio evalNum, off uint64, W int, up bool) evalNum {
	tb, pb, sb, nb := st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev)
	if !ev.ok() {
		return evalNum{}
	}
	term := ev.round(tb, first, W, up)
	sum := ev.round(sb, first, W, up)
	for j := uint64(1); ev.ok(); j++ {
		if !ev.charge(1) {
			break
		}
		term = ev.divPair(tb, ev.mul(pb, term, ratio, W, up), 2*j-1+off, 2*j+off, W, up)
		sum = ev.add(nb, sum, term, W, up)
		sb, nb = nb, sb
		if term.isZero() || term.top() <= sum.top()-int64(W) {
			break
		}
	}
	if up {
		sum = ev.add(nb, sum, ev.divSmall(tb, term, 7, W, true), W, true)
	}
	return sum
}

// sinhCoshSmall encloses sinh a (off 1) or cosh a (off 0) for exact
// 0 ≤ a ≤ 1/2 by the positive series.
func (ev *evaluator) sinhCoshSmall(st *evalStage, dst []uint32, a evalNum, off uint64, L int, up bool) evalNum {
	mark := st.scope()
	defer st.restore(mark)
	rb := st.buf(ev)
	if !ev.ok() {
		return evalNum{}
	}
	var one [3]uint32
	first := a
	if off == 0 {
		first = evalOne(one[:])
	} else if a.isZero() {
		return evalNum{}
	}
	return ev.positiveSeries(st, dst, first, ev.mul(rb, a, a, L+1, up), off, L, up)
}

// lnPoint encloses ln v for an exact v > 0 through lnEnclose.
func (ev *evaluator) lnPoint(st *evalStage, dst []uint32, v evalNum, L int, up bool) evalNum {
	mark := st.scope()
	defer st.restore(mark)
	lb, hb := st.buf(ev), st.buf(ev)
	if !ev.ok() {
		return evalNum{}
	}
	in := ev.newLnInput(coefficientView{slow: v.m, count: len(v.m)}, limbsDigits(v.m), 9*v.e)
	if in.unit && in.k == 0 {
		return evalNum{}
	}
	lo, hi := ev.lnEnclose(st, lb, hb, &in, L)
	if up {
		return ev.round(dst, hi, L, true)
	}
	return ev.round(dst, lo, L, false)
}

// asinhDirected encloses asinh a for an exact a ≥ 0:
// 2·atanh(a/(1+√(1+a²))) up to 1/2, ln(a + √(a²+1)) above.
func (ev *evaluator) asinhDirected(st *evalStage, dst []uint32, a evalNum, L int, up bool) evalNum {
	if a.isZero() {
		return evalNum{}
	}
	mark := st.scope()
	defer st.restore(mark)
	m, q, r, w := st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev)
	if !ev.ok() {
		return evalNum{}
	}
	var one, two [3]uint32
	oneN := evalOne(one[:])
	halfL := [1]uint32{500_000_000}
	if evalCmp(a, evalNum{m: halfL[:], e: -1}) <= 0 {
		// The quotient rises as its denominator falls: round that against up.
		s := ev.add(m, ev.mul(q, a, a, L+1, !up), oneN, L+1, !up)
		den := ev.add(q, ev.sqrtDirected(st, r, s, L+1, !up), oneN, L+1, !up)
		t := ev.atanhDirected(st, w, ev.div(m, r, a, den, L+1, up), L+1, up)
		return ev.mul(dst, t, evalSmall(two[:], 2, false), L, up)
	}
	s := ev.add(m, ev.mul(q, a, a, L+2, up), oneN, L+2, up)
	v := ev.add(q, ev.sqrtDirected(st, r, s, L+2, up), a, L+2, up)
	return ev.lnPoint(st, dst, v, L, up)
}

// hyperbolicEnclose encloses sinh, cosh, tanh, asinh, acosh or atanh.
func (ev *evaluator) hyperbolicEnclose(st *evalStage, lo, hi []uint32, pr *evalProblem, L int) (evalNum, evalNum, evalRange) {
	mark := st.scope()
	defer st.restore(mark)
	al, ah, el, eh, tl, th, sb, cb := st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev)
	if !ev.ok() {
		return evalNum{}, evalNum{}, evalInRange
	}
	alo := ev.load(al, &pr.x, pr.xDigits, pr.xExp, false, L+2, false)
	ahi := ev.load(ah, &pr.x, pr.xDigits, pr.xExp, false, L+2, true)
	var one, two [3]uint32
	oneN := evalOne(one[:])
	halfL := [1]uint32{500_000_000}
	half := evalNum{m: halfL[:], e: -1}
	small := evalCmp(ahi, half) <= 0
	switch pr.kind {
	case evalSinh, evalCosh:
		if pr.kind == evalSinh {
			if l, h, ok := ev.tinyOdd(lo, hi, alo, ahi, L, true); ok {
				return evalOdd(l, h, pr.xNeg)
			}
		} else if l, h, ok := ev.tinyEven(lo, hi, ahi, L, true); ok {
			return l, h, evalInRange
		}
		off := uint64(0)
		if pr.kind == evalSinh {
			off = 1
		}
		if small {
			return evalOdd(ev.sinhCoshSmall(st, lo, alo, off, L, false), ev.sinhCoshSmall(st, hi, ahi, off, L, true), pr.xNeg && off == 1)
		}
		eLo, eHi, rng := ev.expEnclose(st, el, eh, alo, ahi, L+1)
		if rng != evalInRange {
			return evalNum{}, evalNum{}, rng
		}
		// (E ∓ 1/E)/2 rises with E ≥ 1; the reciprocal is rounded so each
		// bound moves its own way.
		sign := func(r evalNum) evalNum {
			if off == 1 {
				return r.negate()
			}
			return r
		}
		// sinh's lower bound subtracts 1/E rounded up; cosh's adds it down.
		rLo := ev.div(tl, sb, oneN, eLo, L+1, off == 1)
		rHi := ev.div(th, sb, oneN, eHi, L+1, off == 0)
		l := ev.divSmall(lo, ev.add(cb, eLo, sign(rLo), L+1, false), 2, L, false)
		h := ev.divSmall(hi, ev.add(cb, eHi, sign(rHi), L+1, true), 2, L, true)
		return evalOdd(l, h, pr.xNeg && off == 1)
	case evalTanh:
		if l, h, ok := ev.tinyOdd(lo, hi, alo, ahi, L, false); ok {
			return evalOdd(l, h, pr.xNeg)
		}
		if small {
			sLo, sHi := ev.sinhCoshSmall(st, el, alo, 1, L+1, false), ev.sinhCoshSmall(st, eh, ahi, 1, L+1, true)
			cLo, cHi := ev.sinhCoshSmall(st, tl, alo, 0, L+1, false), ev.sinhCoshSmall(st, th, ahi, 0, L+1, true)
			return evalOdd(ev.div(lo, sb, sLo, cHi, L, false), ev.div(hi, sb, sHi, cLo, L, true), pr.xNeg)
		}
		// t = e^(−2a) ∈ [e^(−2ahi), e^(−2alo)]; tanh = (1−t)/(1+t) falls with t.
		zlo := ev.mul(tl, ahi, evalSmall(two[:], 2, true), evalExact, false)
		zhi := ev.mul(th, alo, evalSmall(two[:], 2, true), evalExact, true)
		tLo, tHi, rng := ev.expEnclose(st, el, eh, zlo, zhi, L+1)
		switch rng {
		case evalTiny:
			l, h, _ := ev.tinyEven(lo, hi, evalNum{}, L, false)
			return evalOdd(l, h, pr.xNeg)
		case evalInRange:
		default:
			return evalNum{}, evalNum{}, rng
		}
		l := ev.div(lo, sb, ev.oneMinus(tl, tHi, false, false), ev.add(cb, oneN, tHi, L+1, true), L, false)
		h := ev.div(hi, sb, ev.oneMinus(th, tLo, false, true), ev.add(cb, oneN, tLo, L+1, false), L, true)
		return evalOdd(l, h, pr.xNeg)
	case evalAsinh:
		if l, h, ok := ev.tinyOdd(lo, hi, alo, ahi, L, false); ok {
			return evalOdd(l, h, pr.xNeg)
		}
		return evalOdd(ev.asinhDirected(st, lo, alo, L, false), ev.asinhDirected(st, hi, ahi, L, true), pr.xNeg)
	case evalAcosh:
		// 2·asinh(√((x−1)/2)), rising in x; x − 1 exact below two.
		acosh := func(dst []uint32, x evalNum, up bool) evalNum {
			var d evalNum
			if evalCmp(x, evalSmall(two[:], 2, false)) < 0 {
				d = ev.oneMinus(cb, x, false, !up).negate()
			} else {
				d = ev.add(cb, x, oneN.negate(), L+2, up)
			}
			s := ev.sqrtDirected(st, sb, ev.divSmall(cb, d, 2, L+2, up), L+2, up)
			return ev.mul(dst, ev.asinhDirected(st, tl, s, L+1, up), evalSmall(two[:], 2, false), L, up)
		}
		if evalCmp(alo, oneN) < 0 {
			alo = oneN
		}
		return acosh(lo, alo, false), acosh(hi, ahi, true), evalInRange
	}
	// Atanh: |x| < 1 is proved by the domain check; a rounded endpoint at
	// one refines.
	if cmpMag(ahi, oneN) >= 0 {
		return evalNum{}, evalNum{}, evalWide
	}
	if l, h, ok := ev.tinyOdd(lo, hi, alo, ahi, L, true); ok {
		return evalOdd(l, h, pr.xNeg)
	}
	atanh := func(dst []uint32, a evalNum, up bool) evalNum {
		if evalCmp(a, half) <= 0 {
			return ev.atanhDirected(st, dst, a, L, up)
		}
		// ½·ln((1+a)/(1−a)), rising in a.
		r := ev.div(cb, sb, ev.oneMinus(tl, a, true, up), ev.oneMinus(th, a, false, !up), L+1, up)
		return ev.divSmall(dst, ev.lnPoint(st, el, r, L+1, up), 2, L, up)
	}
	return evalOdd(atanh(lo, alo, false), atanh(hi, ahi, true), pr.xNeg)
}

// Sinh returns sinh d exactly: Sinh(0) is 0; every other finite d returns a
// *Error with Condition Inexact and a remedy naming SinhWithContext.
func (d Decimal) Sinh() (Decimal, error) {
	result, _, err := d.elementary(evalSinh, Decimal{}, Context{}, Budget{}, "Sinh")
	return result, err
}

// SinhWithContext rounds sinh d once to the context precision in the
// context's mode, with guards and traps; the exact case keeps exponent 0 and
// every other result is inexact. Context{} behaves as Sinh.
func (d Decimal) SinhWithContext(ctx Context) (Decimal, Conditions, error) {
	return d.elementary(evalSinh, Decimal{}, ctx, ctx.Budget(), "SinhWithContext")
}

// Cosh returns cosh d exactly: Cosh(0) is 1; every other finite d returns a
// *Error with Condition Inexact and a remedy naming CoshWithContext.
func (d Decimal) Cosh() (Decimal, error) {
	result, _, err := d.elementary(evalCosh, Decimal{}, Context{}, Budget{}, "Cosh")
	return result, err
}

// CoshWithContext rounds cosh d once to the context precision in the
// context's mode, with guards and traps; the exact case keeps exponent 0 and
// every other result is inexact. Context{} behaves as Cosh.
func (d Decimal) CoshWithContext(ctx Context) (Decimal, Conditions, error) {
	return d.elementary(evalCosh, Decimal{}, ctx, ctx.Budget(), "CoshWithContext")
}

// Tanh returns tanh d exactly: Tanh(0) is 0; every other finite d returns a
// *Error with Condition Inexact and a remedy naming TanhWithContext.
func (d Decimal) Tanh() (Decimal, error) {
	result, _, err := d.elementary(evalTanh, Decimal{}, Context{}, Budget{}, "Tanh")
	return result, err
}

// TanhWithContext rounds tanh d once to the context precision in the
// context's mode, with guards and traps; the exact case keeps exponent 0 and
// every other result is inexact. Context{} behaves as Tanh.
func (d Decimal) TanhWithContext(ctx Context) (Decimal, Conditions, error) {
	return d.elementary(evalTanh, Decimal{}, ctx, ctx.Budget(), "TanhWithContext")
}

// Asinh returns asinh d exactly: Asinh(0) is 0; every other finite d returns
// a *Error with Condition Inexact and a remedy naming
// AsinhWithContext.
func (d Decimal) Asinh() (Decimal, error) {
	result, _, err := d.elementary(evalAsinh, Decimal{}, Context{}, Budget{}, "Asinh")
	return result, err
}

// AsinhWithContext rounds asinh d once to the context precision in the
// context's mode, with guards and traps; the exact case keeps exponent 0 and
// every other result is inexact. Context{} behaves as Asinh.
func (d Decimal) AsinhWithContext(ctx Context) (Decimal, Conditions, error) {
	return d.elementary(evalAsinh, Decimal{}, ctx, ctx.Budget(), "AsinhWithContext")
}

// Acosh returns acosh d ≥ 0 exactly: Acosh(1) is 0, other d ≥ 1 return a
// *Error with Condition Inexact and a remedy naming AcoshWithContext,
// and d < 1 returns ErrInvalidOperation.
func (d Decimal) Acosh() (Decimal, error) {
	result, _, err := d.elementary(evalAcosh, Decimal{}, Context{}, Budget{}, "Acosh")
	return result, err
}

// AcoshWithContext rounds acosh d once to the context precision in the
// context's mode, with guards and traps; the exact case keeps exponent 0 and
// every other result is inexact. Context{} behaves as Acosh.
func (d Decimal) AcoshWithContext(ctx Context) (Decimal, Conditions, error) {
	return d.elementary(evalAcosh, Decimal{}, ctx, ctx.Budget(), "AcoshWithContext")
}

// Atanh returns atanh d exactly: Atanh(0) is 0, other d in (−1, 1) return a
// *Error with Condition Inexact and a remedy naming AtanhWithContext;
// d = ±1 returns ErrDivisionByZero and |d| > 1 ErrInvalidOperation.
func (d Decimal) Atanh() (Decimal, error) {
	result, _, err := d.elementary(evalAtanh, Decimal{}, Context{}, Budget{}, "Atanh")
	return result, err
}

// AtanhWithContext rounds atanh d once to the context precision in the
// context's mode, with guards and traps; the exact case keeps exponent 0 and
// every other result is inexact. Context{} behaves as Atanh.
func (d Decimal) AtanhWithContext(ctx Context) (Decimal, Conditions, error) {
	return d.elementary(evalAtanh, Decimal{}, ctx, ctx.Budget(), "AtanhWithContext")
}
