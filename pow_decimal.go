// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"math"
	"math/bits"
	"slices"
)

const powDecimalRemedy = "non-terminating power: supply a finite-precision context (PowDecimalWithContext)"

// PowDecimal returns d^y exactly for a Decimal exponent y. An
// int32-valued y is Pow(y): the repeated-multiplication cohort, or the
// reciprocal cohort for y < 0, and 0⁰ = 1. Other integral y extend the same
// cohorts to the full exponent domain. A noninteger y whose power is a
// finite decimal gives its shortest representable cohort: 4^0.5 is exactly
// 2. A power that is irrational or not a finite decimal, such as 2^0.5 or
// (9/4)^−0.5 = 2/3, returns a *Error with Condition Inexact and a
// remedy naming PowDecimalWithContext. A negative d with a noninteger y
// returns ErrInvalidOperation, even where a real odd root exists; zero to
// a negative power returns ErrDivisionByZero, and zero to a positive
// noninteger power is 0.
func (d Decimal) PowDecimal(y Decimal) (Decimal, error) {
	result, _, err := d.powDecimal(y, Context{}, Budget{}, "PowDecimal")
	return result, err
}

// PowDecimalWithContext rounds d^y once to the context precision in the
// context's mode, with guards and traps. Exact powers keep the cohort
// nearest the ideal one that fits; mathematical exactness alone decides
// Inexact, so (81/16)^0.5 = 2.25 at two digits is an exact tie.
func (d Decimal) PowDecimalWithContext(y Decimal, ctx Context) (Decimal, Conditions, error) {
	return d.powDecimal(y, ctx, ctx.Budget(), "PowDecimalWithContext")
}

func (d Decimal) powDecimal(y Decimal, ctx Context, budget Budget, op string) (Decimal, Conditions, error) {
	ev := newEvaluator(budget)
	return ev.powDecimal(d, y, ctx, op)
}

func (ev *evaluator) powDecimal(x, y Decimal, ctx Context, op string) (Decimal, Conditions, error) {
	switch {
	case y.isZero():
		return ev.powInt32(x, 0, ctx, op)
	case x.isZero() && y.negative():
		return contextFailure(op, ErrDivisionByZero) // known from the headers
	}
	e := ev.classifyExponent(y)
	if !ev.ok() {
		return ev.failure(op)
	}
	if e.small {
		return ev.powInt32(x, e.n32, ctx, op)
	}
	switch {
	case x.isZero():
		if y.negative() {
			return contextFailure(op, ErrDivisionByZero)
		}
		ideal := int64(0)
		if e.integer {
			// The cohort exponent y·e of a zero.
			if ideal = powSaturatedProduct(y, x.exponent()); ideal < math.MinInt32 || ideal > math.MaxInt32 {
				return contextFailure(op, ErrExponentRange)
			}
		}
		result := ev.publish(nil, ideal, false)
		if !ev.ok() {
			return ev.failure(op)
		}
		return result, 0, nil
	case x.negative() && !e.integer:
		return contextFailure(op, ErrInvalidOperation)
	}
	neg := x.negative() && e.odd
	p := uint64(ctx.precision)
	v := coefficientViewOf(x)
	ar := ev.arena(2*uint64(v.count) + 2)
	defer ev.release(&ar)
	base := ev.factorBase(&ar, x)
	r := ev.powRational(&base, y, e)
	if !ev.ok() {
		return ev.failure(op)
	}
	// Integral y > 0 keeps the repeated-multiplication cohort y·e; y < 0
	// and nonintegers use the shortest exact form.
	cohort := e.integer && !y.negative()
	ideal := r.h
	if cohort {
		ideal = powSaturatedProduct(y, x.exponent())
	}
	switch {
	case !r.finite:
		return ev.powInexact(x, y, neg, &ctx, op)
	case r.overflow && r.tenPower:
		// 10^(A·y) with A·y beyond int64: a range verdict, exact or not,
		// except that a bare cohort at exponent 0 has an unstorable
		// coefficient, exactly as for any other base.
		if p == 0 && cohort && x.exponent() == 0 && !r.tiny {
			ev.fail(evaluationStatus{code: ErrInsufficientStorage})
			return ev.failure(op)
		}
		if p == 0 || !ctx.guarded {
			return contextFailure(op, ErrExponentRange)
		}
		if ctx.rounding == Exact {
			return contextExactRefusal(op)
		}
		return ev.powOutOfRange(neg, r.tiny, &ctx, op)
	case r.overflow:
		// S has more than 2^62 digits.
		if p == 0 {
			if cohort && x.exponent() == 0 || !cohort && !r.tiny {
				ev.fail(evaluationStatus{code: ErrInsufficientStorage})
				return ev.failure(op)
			}
			return contextFailure(op, ErrExponentRange)
		}
		return ev.powInexact(x, y, neg, &ctx, op)
	}
	if p != 0 {
		limit := p + 3
		if ctx.rounding == Exact {
			limit = p
		}
		if r.longer(&base, limit) {
			// Not a boundary the finisher can see: the enclosure decides.
			return ev.powInexact(x, y, neg, &ctx, op)
		}
	} else {
		if cohort && (ideal < math.MinInt32 || ideal > math.MaxInt32) || !cohort && r.h < math.MinInt32 {
			return contextFailure(op, ErrExponentRange)
		}
		// The published coefficient is S followed by the cohort zeros, both
		// known here: refuse the digit cap before any allocation.
		if limit := ev.meter.budget.MaxDigits; limit != 0 {
			pad := powPad(r.h, ideal, cohort)
			if pad >= limit || r.longer(&base, limit-pad) {
				ev.fail(ev.meter.resultDigits(math.MaxUint64))
				return ev.failure(op)
			}
		}
	}
	root := base.c
	if base.unit() {
		r.m = 0 // 1^m
	} else {
		var perfect bool
		root, perfect = ev.intRootPower(base.c, uint64(r.n))
		if !ev.ok() {
			return ev.failure(op)
		}
		if !perfect {
			return ev.powInexact(x, y, neg, &ctx, op)
		}
	}
	return ev.powExact(root, r, neg, ideal, cohort, &ctx, op)
}

// powInexact settles a power that is not a finite decimal with at most p+3
// significant digits: bare and Exact forms refuse, others enclose it.
func (ev *evaluator) powInexact(x, y Decimal, neg bool, ctx *Context, op string) (Decimal, Conditions, error) {
	if ctx.precision == 0 {
		return Decimal{}, 0, conditionError(op, Inexact, powDecimalRemedy)
	}
	if ctx.rounding == Exact {
		return contextExactRefusal(op)
	}
	pr := evalProblem{kind: evalPow, neg: neg}
	v := coefficientViewOf(x)
	digits, _ := arithmeticDigits(&v)
	pr.ln = ev.newLnInput(v, digits, int64(x.exponent()))
	pr.y.load(y)
	pr.yDigits, _ = arithmeticDigits(&pr.y)
	pr.yExp, pr.yNeg = int64(y.exponent()), y.negative()
	if !ev.ok() {
		return ev.failure(op)
	}
	return ev.certify(&pr, ctx, op)
}

// powOutOfRange publishes a guarded overflow or a value below a tenth of
// the Etiny quantum.
func (ev *evaluator) powOutOfRange(neg, tiny bool, ctx *Context, op string) (Decimal, Conditions, error) {
	if !tiny {
		return ev.overflow(neg, ctx, op)
	}
	etiny := int64(ctx.guards.Emin) - (int64(ctx.precision) - 1)
	var r [1]uint32
	return ev.finish(r[:0], divBelow, etiny, etiny, etiny, neg, ctx, op)
}

// powSaturatedProduct is y·e for an integral |y| > MaxInt32, saturated far
// outside the int32 range; only comparisons with stored exponents use it.
// One such product is a stored exponent: 2^31·(−1) = MinInt32.
func powSaturatedProduct(y Decimal, e int32) int64 {
	const far = int64(1) << 62
	switch {
	case e == 0:
		return 0
	case e == -1 && y.Equal(inlineDecimal(uint128{lo: 1 << 31}, 0, false)):
		return math.MinInt32
	case y.negative() != (e < 0):
		return -far
	default:
		return far
	}
}

// powInt32 is PowDecimal on an int32-valued exponent: Pow's semantics,
// admitted as one phase of Pow's completion Cost (its work plus cumulative
// heap bound), then the adaptive family's result digit cap.
func (ev *evaluator) powInt32(x Decimal, n int32, ctx Context, op string) (Decimal, Conditions, error) {
	var cost Cost
	var err error
	if ctx.precision == 0 {
		cost, err = estimatePow(x.Shape(), n)
	} else {
		cost, err = EstimatePow(x.Shape(), n, ctx)
	}
	switch {
	case err == nil:
		ev.fail(ev.meter.phase(cost.WorkUnits, cost.HeapBytes))
	case err == ErrInsufficientStorage && ev.meter.budget.MaxWork != 0:
		ev.fail(ev.meter.unitRefusal())
	default:
		ev.charge(1) // a shape-determined refusal: Pow refuses before work
	}
	if !ev.ok() {
		return ev.failure(op)
	}
	// Pow refuses its digit cap before allocating; only that cap can refuse
	// storage for a result of at most cap digits, so its storage refusal is
	// the adaptive digit limit.
	limit := ev.meter.budget.MaxDigits
	result, conditions, err := x.powContext(n, ctx, limits{MaxDigits: limit}, op, nil)
	if oe, ok := err.(*Error); ok && limit != 0 && oe.Code == ErrInsufficientStorage && oe.Resource == 0 {
		ev.fail(ev.meter.resultDigits(math.MaxUint64))
		return ev.failure(op)
	}
	if ce, ok := err.(*Error); ok && ce.Remedy == powRemedy {
		ce.Remedy = powDecimalRemedy
	}
	// A refusal returns zero, which one digit always admits.
	if s := ev.meter.resultDigits(result.CoefficientDigits()); s.code != 0 {
		ev.fail(s)
		return ev.failure(op)
	}
	return result, conditions, err
}

// powExponent classifies y = cy·10^ey from its digits, never by converting
// it to a machine integer: integrality, int32 fit and parity, or, for a
// noninteger, the reduced denominator 2^alpha·5^beta.
type powExponent struct {
	integer     bool
	small       bool
	n32         int32
	odd         bool
	alpha, beta uint64
}

func (ev *evaluator) classifyExponent(y Decimal) powExponent {
	v := coefficientViewOf(y)
	digits, _ := arithmeticDigits(&v)
	if !ev.charge(uint64(v.count) + 10) {
		return powExponent{}
	}
	tz := countTrailingZeros(&v)
	ey := int64(y.exponent())
	var c powExponent
	if ey+int64(tz) >= 0 {
		c.integer = true
		c.odd = ey <= 0 && quantizeDigit(&v, uint64(-ey))%2 == 1
		if int64(digits)+ey <= 10 {
			var n uint64
			for i := int64(digits) - 1; i >= max(0, -ey); i-- {
				n = 10*n + uint64(quantizeDigit(&v, uint64(i)))
			}
			for range max(0, ey) {
				n *= 10
			}
			limit := uint64(math.MaxInt32)
			if y.negative() {
				limit++
			}
			if n <= limit {
				c.small = true
				c.n32 = int32(int64(n))
				if y.negative() {
					c.n32 = int32(-int64(n))
				}
			}
		}
		return c
	}
	// y = cy/10^K, K = −ey, reduces by 2^min(K, v2(cy)) and 5^min(K, v5(cy)).
	k := uint64(-ey)
	var two, five uint64
	switch last := quantizeDigit(&v, tz); {
	case last%2 == 0:
		two = ev.coefficientValuation(&v, tz, 2, k-tz)
	case last == 5:
		five = ev.coefficientValuation(&v, tz, 5, k-tz)
	}
	c.alpha = k - min(k, tz+two)
	c.beta = k - min(k, tz+five)
	return c
}

// coefficientValuation is min(v_p(C/10^tz), limit) from an admitted copy.
func (ev *evaluator) coefficientValuation(v *coefficientView, tz uint64, p, limit uint64) uint64 {
	ar := ev.arena(2*uint64(v.count) + 2)
	defer ev.release(&ar)
	buf, tmp := ev.take(&ar, v.count+1), ev.take(&ar, v.count+1)
	if !ev.ok() || !ev.charge(2*uint64(v.count)) {
		return 0
	}
	for i := range v.count {
		buf[i] = v.limb(i)
	}
	shiftRightDigits(buf[:v.count], tz)
	_, n := ev.valuation(trimLimbs(buf[:v.count]), tmp, p, limit)
	return n
}

// valuation divides the trimmed integer n by p ∈ {2, 5} while divisible,
// at most limit times, alternating with tmp, and returns the quotient.
func (ev *evaluator) valuation(n, tmp []uint32, p, limit uint64) ([]uint32, uint64) {
	d, step := uint64(1<<29), uint64(29)
	if p == 5 {
		d, step = 244_140_625, 12
	}
	var count uint64
	for len(n) > 0 {
		if count+step > limit {
			if step == 1 {
				break
			}
			d, step = p, 1
			continue
		}
		if !ev.charge(uint64(len(n))) {
			break
		}
		var r uint64
		for i := len(n) - 1; i >= 0; i-- {
			cur := r*decimalLimbBase + uint64(n[i])
			tmp[i], r = uint32(cur/d), cur%d
		}
		if r != 0 {
			if step == 1 {
				break
			}
			d, step = p, 1
			continue
		}
		n, tmp = trimLimbs(tmp[:len(n)]), n[:cap(n)]
		count += step
	}
	return n, count
}

// powBase is |x| = C·2^A·5^B with gcd(C, 10) = 1, from an admitted copy.
type powBase struct {
	c    []uint32 // C, trimmed
	a, b int64
}

func (ev *evaluator) factorBase(ar *evalArena, x Decimal) powBase {
	v := coefficientViewOf(x)
	buf, tmp := ev.take(ar, v.count+1), ev.take(ar, v.count+1)
	if !ev.ok() || !ev.charge(3*uint64(v.count)) {
		return powBase{}
	}
	tz := countTrailingZeros(&v)
	for i := range v.count {
		buf[i] = v.limb(i)
	}
	shiftRightDigits(buf[:v.count], tz)
	c := trimLimbs(buf[:v.count])
	var s2, s5 uint64
	switch last := c[0] % 10; {
	case last%2 == 0:
		c, s2 = ev.valuation(c, tmp, 2, math.MaxUint64)
	case last == 5:
		c, s5 = ev.valuation(c, tmp, 5, math.MaxUint64)
	}
	e := int64(x.exponent()) + int64(tz)
	return powBase{c: c, a: e + int64(s2), b: e + int64(s5)}
}

func (b *powBase) unit() bool { return len(b.c) == 1 && b.c[0] == 1 }

// log2Floor is a lower bound on log2 C in thousandths: C ≥ top·10^(9(n−1)).
func (b *powBase) log2Floor() uint64 {
	n := uint64(len(b.c))
	return uint64(bits.Len32(b.c[n-1])-1)*1000 + (n-1)*29_897
}

// powValue describes x^y for y = m/n reduced: rational iff n divides A, B
// and C's maximal perfect-power exponent, and a finite decimal iff also
// C = 1 or y > 0. Then x^y = S·10^h with S = R^m·2^e2·5^e5 free of
// trailing zeros and R = C^(1/n); the root itself is tested only once the
// value is known to be short.
type powValue struct {
	finite   bool
	overflow bool // m, A·y or B·y exceeds int64
	tenPower bool // C = 1 and A = B: x^y = 10^(A·y)
	tiny     bool // an overflowing smallest exponent is negative
	m, n     int64
	e2, e5   int64
	h        int64
}

func (ev *evaluator) powRational(b *powBase, y Decimal, e powExponent) powValue {
	var r powValue
	if !ev.ok() {
		return r
	}
	if b.unit() && b.a == 0 && b.b == 0 {
		// x = 1: S = 1 at exponent 0 for every y, whatever its denominator.
		r.finite, r.tenPower, r.n = true, true, 1
		return r
	}
	n := uint64(1)
	if !e.integer {
		if e.alpha > 62 || e.beta > 26 {
			return r // n > 2^62 divides neither A nor B, and x ≠ 1
		}
		n <<= e.alpha
		for range e.beta {
			if n *= 5; n > 1<<62 {
				return r
			}
		}
	}
	if b.a%int64(n) != 0 || b.b%int64(n) != 0 {
		return r
	}
	// C = c^k with k < log2 C < 3.33·digits(C) ≤ 30·limbs: n | k needs n below.
	if !b.unit() && (y.negative() || n > 30*uint64(len(b.c))) {
		return r // C > 1 with y < 0 keeps a prime other than 2 or 5
	}
	r.finite, r.n = true, int64(n)
	r.tenPower = b.unit() && b.a == b.b
	m, ok := ev.exponentNumerator(y, n)
	if !ev.ok() {
		return r
	}
	a, ok1 := mulInt64(b.a/int64(n), m)
	c, ok2 := mulInt64(b.b/int64(n), m)
	if !ok || !ok1 || !ok2 {
		r.overflow = true
		// The smaller of A·y and B·y is hugely negative when a nonzero
		// valuation has the opposite sign of y.
		r.tiny = b.a != 0 && (b.a < 0) != y.negative() || b.b != 0 && (b.b < 0) != y.negative()
		return r
	}
	r.m, r.h = m, min(a, c)
	r.e2, r.e5 = a-r.h, c-r.h
	if r.e2 < 0 || r.e5 < 0 || r.h < -(1<<61) || r.h > 1<<61 {
		r.overflow = true
		r.tiny = r.h < 0
	}
	return r
}

// exponentNumerator is m = y·n, an integer, when it fits int64.
func (ev *evaluator) exponentNumerator(y Decimal, n uint64) (int64, bool) {
	v := coefficientViewOf(y)
	digits, _ := arithmeticDigits(&v)
	if int64(digits)+int64(y.exponent()) > 19 {
		return 0, false // |y| ≥ 10^19 > 2^63
	}
	L := v.count + 2
	ar := ev.arena(uint64(3 * (L + 4)))
	defer ev.release(&ar)
	yb, pb := ev.take(&ar, L+4), ev.take(&ar, 2*(L+4))
	if !ev.ok() {
		return 0, false
	}
	var nb [3]uint32
	yn := ev.load(yb, &v, digits, int64(y.exponent()), false, L, false)
	prod := ev.mul(pb, yn, evalSmall(nb[:], n, false), L+3, false)
	if !ev.charge(uint64(len(prod.m))) {
		return 0, false
	}
	u, ok := evalUint(evalStripZeros(prod))
	if !ok || u > math.MaxInt64 {
		return 0, false
	}
	if y.negative() {
		return -int64(u), true
	}
	return int64(u), true
}

// evalStripZeros drops zero low limbs.
func evalStripZeros(x evalNum) evalNum {
	for len(x.m) > 0 && x.m[0] == 0 {
		x.m = x.m[1:]
		x.e++
	}
	return x
}

func mulInt64(a, b int64) (int64, bool) {
	hi, lo := bits.Mul64(uint64(max(a, -a)), uint64(max(b, -b)))
	if a == math.MinInt64 || b == math.MinInt64 || hi != 0 || lo > math.MaxInt64 {
		return 0, false
	}
	if (a < 0) != (b < 0) {
		return -int64(lo), true
	}
	return int64(lo), true
}

// longer reports that S certainly has more than limit digits, from
// log10 S ≥ y·log10 C + e2·log10 2 + e5·log10 5 with log10 C bounded by C's
// bit length, log10 2 > 0.30102 and log10 5 > 0.69897.
func (r *powValue) longer(b *powBase, limit uint64) bool {
	// Units of 10^−8. An overflowing sum proves only log10 S ≥ 2^64·10^−8.
	const saturated = math.MaxUint64 / 100_000_000
	var sum uint64
	if !b.unit() {
		hi, lo := bits.Mul64(uint64(r.m), b.log2Floor()*30_102)
		if hi >= uint64(r.n) {
			return limit <= saturated
		}
		sum, _ = bits.Div64(hi, lo, uint64(r.n))
	}
	for _, t := range [2][2]uint64{{uint64(r.e2), 30_102_000}, {uint64(r.e5), 69_897_000}} {
		hi, lo := bits.Mul64(t[0], t[1])
		var c uint64
		sum, c = bits.Add64(sum, lo, 0)
		if hi != 0 || c != 0 {
			return limit <= saturated
		}
	}
	// digits(S) = ⌊log10 S⌋+1 exceeds limit once log10 S ≥ limit.
	hi, threshold := bits.Mul64(limit, 100_000_000)
	return hi == 0 && sum >= threshold
}

// powExact computes S = R^m·2^e2·5^e5 exactly and publishes S·10^h at its
// cohort: toward the ideal exponent of an integral cohort, or padded down
// to MaxInt32 when the shortest exponent exceeds it.
func (ev *evaluator) powExact(root []uint32, r powValue, neg bool, ideal int64, cohort bool, ctx *Context, op string) (Decimal, Conditions, error) {
	pad := powPad(r.h, ideal, cohort)
	room := pad
	if ctx.precision != 0 {
		room = min(pad, uint64(ctx.precision)) // at most p zeros can return
	}
	ar, s := ev.intProduct(root, uint64(r.m), uint64(r.e2), uint64(r.e5), room)
	defer ev.release(&ar)
	if !ev.ok() {
		return ev.failure(op)
	}
	if ctx.precision != 0 {
		// Restore only the zeros that fit the precision; a noninteger
		// cohort above MaxInt32 either fits entirely or rounds.
		p, d := uint64(ctx.precision), limbsDigits(s)
		room := p - min(p, d)
		if cohort {
			pad = min(pad, room)
		} else if pad > room {
			pad = 0
		}
	}
	h := r.h
	if pad > 0 {
		s = ev.shiftLeftDigits(s, pad)
		h -= int64(pad)
	}
	if !cohort {
		ideal = h // the shortest representable exponent, after any padding
	}
	if !ev.ok() {
		return ev.failure(op)
	}
	return ev.finishExact(s, h, ideal, neg, ctx, op)
}

// powPad is the number of cohort zeros an exact S·10^h gains: toward the
// ideal exponent of an integral cohort, or down to MaxInt32.
func powPad(h, ideal int64, cohort bool) uint64 {
	switch {
	case cohort && ideal < h:
		return uint64(h - ideal)
	case h > math.MaxInt32:
		return uint64(h - math.MaxInt32)
	}
	return 0
}

// shiftLeftDigits multiplies the limbs s, whose buffer has room for the
// shift and a spare limb, by 10^k in place.
func (ev *evaluator) shiftLeftDigits(s []uint32, k uint64) []uint32 {
	whole, part := int(k/9), k%9
	n := len(s) + whole + 1
	if n+1 > cap(s) || !ev.charge(uint64(n)) {
		ev.broken()
		return s
	}
	full := s[:n+1]
	clear(full[len(s):])
	f := uint64(decimalPowers[part])
	// From the top down every source limb is read before its slot is
	// rewritten; a shifted limb's high and low parts occupy disjoint digits.
	for i, v := range slices.Backward(s) {
		v := uint64(v) * f
		full[i+whole+1] += uint32(v / decimalLimbBase)
		full[i+whole] = uint32(v % decimalLimbBase)
	}
	clear(full[:whole])
	return trimLimbs(full[:n])
}

// intProduct returns S = root^m·2^e2·5^e5 in an admitted arena whose final
// buffer also holds pad more digits and a carry limb.
func (ev *evaluator) intProduct(root []uint32, m, e2, e5, pad uint64) (evalArena, []uint32) {
	// Digits: m·digits(root) + e2·log10 2 + e5·log10 5 + 2, checked.
	var tally costTally
	rootDigits := limbsDigits(root)
	d := tally.add(tally.mul(m, rootDigits), e2/3+1, tally.mul(e5, 7)/10+1, 2)
	padded := tally.add(d, pad)
	if tally.overflow || padded > 1<<50 {
		ev.fail(evaluationStatus{code: ErrInsufficientStorage})
		return evalArena{}, nil
	}
	// Products need twice S's limbs; only the output also holds the pad.
	limbs, outLimbs := int(d/9)+3, int(padded/9)+3
	ar := ev.arena(uint64(6*limbs + 2*outLimbs + 16))
	x, y, t, out := ev.take(&ar, 2*limbs+2), ev.take(&ar, 2*limbs+2), ev.take(&ar, 2*limbs+2), ev.take(&ar, 2*outLimbs+2)
	if !ev.ok() {
		return ar, nil
	}
	var one [3]uint32
	acc := evalOne(out)
	if m > 0 && !(len(root) == 1 && root[0] == 1) {
		acc = ev.intPower(x, y, evalNum{m: root}, m, evalExact)
		acc = ev.round(out, acc, evalExact, false)
	}
	for _, f := range [2][2]uint64{{2, e2}, {5, e5}} {
		if f[1] == 0 {
			continue
		}
		fp := ev.intPower(x, y, evalSmall(one[:], f[0], false), f[1], evalExact)
		acc = ev.round(out, ev.mul(t, acc, fp, evalExact, false), evalExact, false)
	}
	if !ev.ok() {
		return ar, nil
	}
	// acc is an integer; its limbs from exponent 0 up, zero filled.
	res := out[:acc.top()]
	if acc.e > 0 {
		copy(res[acc.e:], acc.m)
		clear(res[:acc.e])
	}
	return ar, res
}

// intPower is b^k exactly by left-to-right binary powering between the
// two buffers.
func (ev *evaluator) intPower(x, y []uint32, b evalNum, k uint64, L int) evalNum {
	acc := ev.round(x, b, L, false)
	for i := bits.Len64(k) - 2; i >= 0 && ev.ok(); i-- {
		sq := ev.mul(y, acc, acc, L, false)
		acc = ev.round(x, sq, L, false)
		if k>>uint(i)&1 == 1 {
			acc = ev.round(x, ev.mul(y, acc, b, L, false), L, false)
		}
	}
	return acc
}

// intRootPower returns C^(1/n) for n = 2^α·5^β by successive exact square
// and fifth roots, and false once a root is not exact.
func (ev *evaluator) intRootPower(c []uint32, n uint64) ([]uint32, bool) {
	for n > 1 && ev.ok() {
		k := uint64(2)
		if n%2 != 0 {
			k = 5
		}
		root, exact := ev.intRoot(c, k)
		if !exact {
			return nil, false
		}
		c, n = root, n/k
	}
	return c, ev.ok()
}

// intRoot is ⌊N^(1/k)⌋ for k ∈ {2, 5} and whether it is exact, by the
// integer Newton iteration x ← ⌊((k−1)x + ⌊N/x^(k−1)⌋)/k⌋, which decreases
// strictly from any x ≥ ⌊N^(1/k)⌋ until it reaches the floor root.
func (ev *evaluator) intRoot(c []uint32, k uint64) ([]uint32, bool) {
	N := evalNum{m: c}
	size := 3*len(c) + 16
	ar := ev.arena(uint64(8 * size))
	// The root outlives this arena only through its caller's copy below.
	xb, yb, pb, qb, sb, tb, rb := ev.take(&ar, size), ev.take(&ar, size), ev.take(&ar, size), ev.take(&ar, size), ev.take(&ar, 2*size), ev.take(&ar, size), ev.take(&ar, size)
	if !ev.ok() {
		ev.release(&ar)
		return nil, false
	}
	var kb [3]uint32
	digits := limbsDigits(c)
	start := int64((digits + k - 1) / k)
	x := ev.scale(xb, evalOne(rb), start)
	for ev.ok() {
		if !ev.charge(1) {
			break
		}
		xp := ev.round(pb, x, evalExact, false)
		for range k - 2 {
			xp = ev.round(pb, ev.mul(tb, xp, x, evalExact, false), evalExact, false)
		}
		q := evalFloor(ev.div(qb, sb, N, xp, int(N.top()-xp.top())+3, false))
		t := ev.mul(tb, x, evalSmall(kb[:], k-1, false), evalExact, false)
		t = ev.add(yb, t, q, evalExact, false)
		y := evalFloor(ev.divSmall(tb, t, k, int(t.top())+2, false))
		if !ev.charge(uint64(len(x.m) + len(y.m))) {
			break
		}
		if cmpMag(y, x) >= 0 {
			break
		}
		x = ev.round(xb, y, evalExact, false)
	}
	xp := ev.round(pb, x, evalExact, false)
	for range k - 1 {
		xp = ev.round(pb, ev.mul(tb, xp, x, evalExact, false), evalExact, false)
	}
	// The comparison, clear and copy-back each visit at most cap(c) limbs.
	perfect := ev.charge(3*uint64(cap(c))+uint64(len(xp.m))) && cmpMag(xp, N) == 0
	if !perfect {
		ev.release(&ar)
		return nil, false
	}
	// Copy the root back into c's own buffer, which it never outgrows.
	out := c[:cap(c)]
	clear(out)
	for i := range x.m {
		out[int(x.e)+i] = x.m[i]
	}
	ev.release(&ar)
	return trimLimbs(out[:x.top()]), true
}

// evalFloor truncates a nonnegative endpoint to an integer.
func evalFloor(x evalNum) evalNum {
	if x.e >= 0 {
		return x
	}
	if int64(len(x.m)) <= -x.e {
		return evalNum{}
	}
	x.m = x.m[-x.e:]
	x.e = 0
	return x
}

// powEnclose encloses |x|^y = exp(y·ln|x|), negated for an odd integral y
// of a negative base.
func (ev *evaluator) powEnclose(st *evalStage, lo, hi []uint32, pr *evalProblem, L int) (evalNum, evalNum, evalRange) {
	mark := st.scope()
	defer st.restore(mark)
	yl, yh, ll, lh := st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev)
	pl, ph, zl, zh := st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev)
	if !ev.ok() {
		return evalNum{}, evalNum{}, evalInRange
	}
	W := L + 2 // |z| < 10^11 in range
	ylo := ev.load(yl, &pr.y, pr.yDigits, pr.yExp, pr.yNeg, W, false)
	yhi := ev.load(yh, &pr.y, pr.yDigits, pr.yExp, pr.yNeg, W, true)
	llo, lhi := ev.lnEnclose(st, ll, lh, &pr.ln, W)
	// z = y·ln|x| lies between the extreme endpoint products.
	var zlo, zhi evalNum
	first := true
	for _, a := range [2]evalNum{ylo, yhi} {
		for _, b := range [2]evalNum{llo, lhi} {
			if !ev.charge(2 * uint64(W)) {
				return evalNum{}, evalNum{}, evalInRange
			}
			d := ev.mul(pl, a, b, W, false)
			if first || evalCmp(d, zlo) < 0 {
				zlo = ev.round(zl, d, W, false)
			}
			u := ev.mul(ph, a, b, W, true)
			if first || evalCmp(u, zhi) > 0 {
				zhi = ev.round(zh, u, W, true)
			}
			first = false
		}
	}
	elo, ehi, rng := ev.expEnclose(st, lo, hi, zlo, zhi, L)
	if pr.neg {
		elo, ehi = ehi.negate(), elo.negate()
	}
	return elo, ehi, rng
}
