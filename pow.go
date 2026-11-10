// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"math"
	"math/bits"
)

// How Pow computes integer powers: write the operand's
// coefficient as C = c·10^z with c free of trailing zeros, and m = |n|.
//
//   - The exact path multiplies c by binary exponentiation over exact
//     base-10⁹ limbs, sized from a digit bracket of c^m computed in 64-bit
//     fixed point. The bare form appends the m·z zeros of the
//     repeated-multiplication cohort; at finite precision they are an
//     exponent shift.
//   - At finite precision p, when c^m certainly has more than p+1 digits,
//     a Ziv loop brackets C^m between a truncated power rounded down (L)
//     and one rounded up (U) at w digits, and accepts when both share the
//     (p+1)-digit prefix at U's fixed exponent. The true value then has
//     that prefix and a nonzero tail, so the context finisher rounds it
//     once in any mode. Otherwise w doubles; once w reaches the bracket's
//     upper bound the exact path decides.
//
// Correctness never rests on an approximation: the bracket and the
// interval are rigorous bounds, and every rounding is decided from an
// exact prefix and an exact class; the kernel uses no math/big.

const powRemedy = "non-terminating power: supply a finite-precision context (PowWithContext)"

// Pow returns x^n exactly. For n ≥ 0 the result is the
// repeated-multiplication cohort: C^n at exponent n·e, so 1.10² is
// 1.2100. 0⁰ is 1, the empty product (GDA's power gives NaN; a documented
// deviation). For n < 0 the result is the reciprocal of x^|n| when it
// terminates, at the reciprocal-then-multiply exponent (2⁻³ is 0.125);
// otherwise, as for 3⁻¹, Pow returns a *Error with Condition Inexact
// and a remedy naming PowWithContext. 0ⁿ with n < 0 returns
// ErrDivisionByZero, and an exponent outside int32 returns
// ErrExponentRange.
func (d Decimal) Pow(n int32) (Decimal, error) {
	result, _, err := d.powUnlimited(n, limits{}, "Pow", nil)
	return result, err
}

// PowWithContext rounds x^n once to the context precision in the
// context's mode, with guards and traps. An exact power keeps the exponent
// nearest the cohort's that fits the precision, reporting Rounded when
// only zeros are dropped. n = 1 is RoundToPrecisionWithContext and n = −1
// is DivWithContext of one by x. Context{} behaves as Pow.
func (d Decimal) PowWithContext(n int32, ctx Context) (Decimal, Conditions, error) {
	return d.powContext(n, ctx, ctx.arith, "PowWithContext", nil)
}

// powCount records kernel work for the counted-loop tests and carries the
// package-internal test seam. Production calls pass nil.
type powCount struct {
	work     uint64   // Mul-family units: t(a)·t(b)+a+b per multiply, digit reads, appended zeros
	div      divCount // Div-family units of the reciprocal divisions
	levels   []uint64 // widths of the truncated levels run
	exact    bool     // the exact power ran
	escalate bool     // seam: reject every truncated level (forces the exact fallback)
}

func (c *powCount) add(n uint64) {
	if c != nil {
		c.work += n
	}
}

func (c *powCount) divCounter() *divCount {
	if c == nil {
		return nil
	}
	return &c.div
}

// powMagnitude is |n| without overflow at MinInt32.
func powMagnitude(n int32) uint64 {
	if n < 0 {
		return uint64(-int64(n))
	}
	return uint64(n)
}

// powLog10Two is ⌊log10(2)·2⁶⁴⌋; the next integer is an upper bound.
const powLog10Two = 5553023288523357132

// powLog2 brackets log2(y) for y ∈ [1, 2) held in Q1.63 as Y = y·2⁶³, in
// Q0.62: the bits of the repeated-squaring expansion under rounding down
// give a lower bound B (log2 y ≥ B·2⁻⁶²), and under rounding up an upper
// bound (log2 y < (B+1)·2⁻⁶²). Each process keeps y^(2^k)/2^(B_k) between
// 1 and 2 on its side of the true value, so the bounds are rigorous.
func powLog2(y uint64, up bool) uint64 {
	var b uint64
	for range 62 {
		hi, lo := bits.Mul64(y, y) // y²·2¹²⁶
		var bit uint64
		switch {
		case hi >= 1<<63: // y² ≥ 2: halve
			bit, y = 1, hi // ⌊y²·2⁶²⌋
			if up && lo != 0 {
				y++ // y < 2 keeps hi+1 below 2⁶⁴
			}
		case up:
			v, carry := bits.Add64(hi<<1|lo>>63, 0, 0)
			if lo<<1 != 0 {
				v, carry = bits.Add64(v, 1, 0)
			}
			if carry != 0 { // ⌈y²⌉ is exactly 2
				bit, y = 1, 1<<63
			} else {
				y = v
			}
		default:
			y = hi<<1 | lo>>63
		}
		b = b<<1 | bit
	}
	return b
}

// powLog is a bracket of λ = log10(M/10¹⁸) for the leading 19 digits M of
// c in Q0.64: lo ≤ λ(M) and hi ≥ λ(M′), with M′ = M+1 when M truncates c
// (one reports hi ≥ 1). It is computed once per call.
type powLog struct {
	lo, hi uint64
	one    bool
}

// powLog10 is log10(M/10¹⁸) for M ∈ [10¹⁸, 10¹⁹] in Q0.64, rounded down
// or up; one reports an upward value of at least 1.
func powLog10(m uint64, up bool) (uint64, bool) {
	j := uint(0)
	for j < 3 && m >= uint64(2)<<j*1_000_000_000_000_000_000 {
		j++
	}
	// y = M/(2^j·10¹⁸) ∈ [1, 2) as Q1.63: ⌊M·2^(63−j)/10¹⁸⌋, rounded.
	q, r := bits.Div64(m>>(1+j), m<<(63-j), 1_000_000_000_000_000_000)
	if up && r != 0 {
		q++
	}
	frac := powLog2(q, up)
	if up {
		frac++
	}
	l2 := uint64(j)<<62 + frac // log2(M/10¹⁸) in Q2.62
	c := uint64(powLog10Two)
	if up {
		c++
	}
	hi, lo := bits.Mul64(l2, c) // λ·2¹²⁶
	if hi>>62 != 0 {
		return 0, true
	}
	v := hi<<2 | lo>>62
	if up && lo<<2 != 0 {
		if v == math.MaxUint64 {
			return 0, true
		}
		v++
	}
	return v, false
}

func newPowLog(m uint64, exact bool) powLog {
	lo, _ := powLog10(m, false)
	if !exact {
		m++
	}
	hi, one := powLog10(m, true)
	return powLog{lo: lo, hi: hi, one: one}
}

// powLogFull is the bracket the estimators use when only the digit count
// is known: every partial power is bounded by k·d digits.
var powLogFull = powLog{one: true}

// digits brackets D = digits(c^k) for a d-digit c: D = k(d−1) +
// ⌊k·log10 m′⌋ + 1 with m′ ∈ [M, M+1)/10¹⁸, so lo uses λ.lo and hi uses
// λ.hi. With λ.hi < 1, ⌊k·λ.hi⌋ ≤ k−1 keeps hi ≤ k·d (c < 10^d); λ.hi ≥ 1
// (one) gives k·d itself. Every product is checked; ok is false when k·d
// leaves the int64/4 range the exponent arithmetic needs.
func (l powLog) digits(d, k uint64) (lo, hi uint64, ok bool) {
	if k == 0 {
		return 1, 1, true
	}
	cap, ok1 := arithmeticMul(k, d)
	if !ok1 || cap > math.MaxInt64/4 {
		return 0, 0, false
	}
	base := cap - k // k(d−1)
	f, _ := bits.Mul64(k, l.lo)
	lo = base + f + 1
	hi = cap
	if !l.one {
		g, _ := bits.Mul64(k, l.hi)
		hi = base + g + 1
	}
	return lo, hi, true
}

// powPlan is the exact binary-exponentiation plan of c^m (left to right:
// square, then multiply by c on a set bit): its charge Σ t(a)·t(b)+a+b over
// the steps with a and b from the bracket of each partial power, the limb
// capacity each product buffer needs, and the bracket of the result.
type powPlan struct {
	charge, limbs uint64
	lo, hi        uint64
	ok            bool
}

func powStepCharge(a, b uint64) (uint64, bool) {
	ta, tb := digitLimbs(a), digitLimbs(b)
	tiles, ok1 := arithmeticMul(ta, tb)
	total, ok2 := checkedSum(tiles, a, b)
	return total, ok1 && ok2
}

func newPowPlan(l powLog, d, m uint64) powPlan {
	p := powPlan{limbs: digitLimbs(d), ok: true}
	td := digitLimbs(d)
	k := uint64(1)
	for i := bits.Len64(m) - 2; i >= 0; i-- {
		_, h, _ := l.digits(d, k) // fails only if the final bracket does (k ≤ m)
		sq, ok2 := powStepCharge(h, h)
		var ok bool
		p.charge, ok = checkedSum(p.charge, sq)
		p.ok = p.ok && ok && ok2
		p.limbs = max(p.limbs, 2*digitLimbs(h))
		k *= 2
		if m>>uint(i)&1 == 1 {
			_, h, _ = l.digits(d, k)
			mul, ok2 := powStepCharge(h, d)
			p.charge, ok = checkedSum(p.charge, mul)
			p.ok = p.ok && ok && ok2
			p.limbs = max(p.limbs, digitLimbs(h)+td)
			k++
		}
	}
	var ok bool
	p.lo, p.hi, ok = l.digits(d, m)
	p.ok = p.ok && ok
	return p
}

// newPowPlanBound bounds newPowPlan(l, d, m) for every m ≤ mMax: the step
// i places from the end squares c^k with k ≤ ⌊mMax/2^(i+1)⌋ and may
// multiply c^k′ by c with k′ < ⌊mMax/2^i⌋, and the bracket is monotone in
// k. The estimators use it where the exponent is known only by a bound.
func newPowPlanBound(l powLog, d, mMax uint64) powPlan {
	p := powPlan{limbs: digitLimbs(d), ok: true}
	td := digitLimbs(d)
	for i := bits.Len64(mMax) - 2; i >= 0; i-- {
		_, hs, ok1 := l.digits(d, mMax>>uint(i+1))
		_, hm, ok2 := l.digits(d, mMax>>uint(i))
		sq, ok3 := powStepCharge(hs, hs)
		mul, ok4 := powStepCharge(hm, d)
		var ok5 bool
		p.charge, ok5 = checkedSum(p.charge, sq, mul)
		p.ok = p.ok && ok1 && ok2 && ok3 && ok4 && ok5
		p.limbs = max(p.limbs, 2*digitLimbs(hs), digitLimbs(hm)+td)
	}
	var ok bool
	p.lo, p.hi, ok = l.digits(d, mMax)
	p.ok = p.ok && ok
	return p
}

// powStackLimbs holds the scratch of every Decimal128 truncated level and
// of exact powers of up to about 250 digits.
const powStackLimbs = 160

// powArena hands out consecutive, capacity-bounded slices of one scratch
// buffer, so a kernel's buffers are one allocation (or the caller's stack).
type powArena struct{ buf []uint32 }

func (a *powArena) take(n uint64) []uint32 {
	s := a.buf[:n:n]
	a.buf = a.buf[n:]
	return s
}

// powScratch returns total limbs from the caller's stack when they fit,
// after physical admission of the heap plan and a result of resultDigits.
func powScratch(stack *[powStackLimbs]uint32, total, resultDigits uint64) (powArena, bool) {
	if !divAdmitted(total, resultDigits) {
		return powArena{}, false
	}
	if total <= powStackLimbs {
		buf := stack[:total]
		clear(buf)
		return powArena{buf: buf}, true
	}
	return powArena{buf: make([]uint32, total)}, true
}

// powView is a read-only view of trimmed limbs.
func powView(r []uint32) coefficientView { return coefficientView{slow: r, count: len(r)} }

// powTop returns the leading 19 digits of a dfull-digit coefficient,
// padded with zeros when it is shorter.
func powTop(v *coefficientView, dfull uint64) uint64 {
	var m uint64
	for i := range uint64(19) {
		m *= 10
		if i < dfull {
			m += uint64(quantizeDigit(v, dfull-1-i))
		}
	}
	return m
}

// powTruncate writes ⌊v/10^s⌋ into out (which has room for it) and returns
// it trimmed.
func powTruncate(v *coefficientView, s uint64, out []uint32) []uint32 {
	clear(out)
	whole := s / 9
	for i := range out {
		if whole+uint64(i) >= uint64(v.count) {
			break
		}
		out[i] = quantizeQuotientLimb(v, s, i)
	}
	return trimLimbs(out)
}

// powStrip is c = C/10^z as a view: a subslice of C's limbs when z is a
// whole number of limbs, otherwise a shifted copy in buf.
func powStrip(v *coefficientView, z uint64, buf []uint32) coefficientView {
	if z == 0 {
		return *v
	}
	if z%9 == 0 && v.slow != nil {
		s := v.slow[z/9:]
		return coefficientView{slow: s, count: len(s)}
	}
	return powView(powTruncate(v, z, buf))
}

// powStripLimbs is the scratch powStrip needs.
func powStripLimbs(v *coefficientView, z, dc uint64) uint64 {
	if z == 0 || z%9 == 0 && v.slow != nil {
		return 0
	}
	return digitLimbs(dc)
}

// powMultiply writes a·b into out (cleared, len(a)+len(b) limbs), counts
// t(a)·t(b)+a+b and returns the trimmed product.
func powMultiply(out []uint32, a, b *coefficientView, cnt *powCount) []uint32 {
	out = out[:a.count+b.count]
	clear(out)
	fillMultiply(out, a, b)
	if cnt != nil {
		da, _ := arithmeticDigits(a)
		db, _ := arithmeticDigits(b)
		cnt.add(uint64(a.count*b.count) + da + db)
	}
	return trimLimbs(out)
}

// powExact computes c^m for m ≥ 1 by left-to-right binary exponentiation
// over exact limbs. x and y hold the plan's limbs plus one spare each; the
// result, trimmed, keeps a zero limb beyond its length for a rounding
// carry.
func powExact(c *coefficientView, m uint64, x, y []uint32, cnt *powCount) []uint32 {
	cur := x[:c.count]
	for i := range cur {
		cur[i] = c.limb(i)
	}
	for i := bits.Len64(m) - 2; i >= 0; i-- {
		v := powView(cur)
		cur = powMultiply(y, &v, &v, cnt)
		x, y = y, x
		if m>>uint(i)&1 == 1 {
			v = powView(cur)
			cur = powMultiply(y, &v, c, cnt)
			x, y = y, x
		}
	}
	// The product buffers are one limb longer than any product.
	clear(x[len(cur):])
	return cur
}

// powPublish publishes an exact coefficient r followed by zeros trailing
// zeros, at exponent, after the final digit cap. W = B was admitted before
// the work. The result never aliases scratch.
func powPublish(r []uint32, zeros uint64, exponent int64, negative bool, budget limits, op string, cnt *powCount) (Decimal, error) {
	if exponent < math.MinInt32 || exponent > math.MaxInt32 {
		return arithmeticFailure(op, ErrExponentRange)
	}
	n, ok := arithmeticAdd(limbsDigits(r), zeros)
	if !ok || !admitted(budget.MaxDigits, n, true) {
		return arithmeticFailure(op, ErrInsufficientStorage)
	}
	e := int32(exponent)
	if zeros == 0 {
		if n <= 38 {
			return publishInlineArithmetic(r, e, negative), nil
		}
		return publishScratch(r, e, negative), nil
	}
	cnt.add(zeros)
	count := digitLimbs(n)
	if n <= 38 {
		var inline [5]uint32
		out := inline[:count]
		powShiftLeft(out, r, zeros)
		return publishInlineArithmetic(out, e, negative), nil
	}
	if count <= slowSmallLimbs {
		var small [slowSmallLimbs]uint32
		out := small[:count]
		powShiftLeft(out, r, zeros)
		return publishScratch(out, e, negative), nil
	}
	if _, err := arithmeticLimbCount(n, op); err != nil {
		return Decimal{}, err
	}
	out := make([]uint32, count)
	powShiftLeft(out, r, zeros)
	return publishOwned(out, e, negative), nil
}

// powShiftLeft writes r·10^k into out, which holds exactly that many limbs.
func powShiftLeft(out, r []uint32, k uint64) {
	clear(out)
	whole, part := k/9, k%9
	factor := uint64(decimalPowers[part])
	var carry uint64
	for i, limb := range r {
		v := uint64(limb)*factor + carry
		out[whole+uint64(i)] = uint32(v % decimalLimbBase)
		carry = v / decimalLimbBase
	}
	if carry != 0 {
		out[whole+uint64(len(r))] = uint32(carry)
	}
}

// powOperand is the reduced operand: C = c·10^z with d = digits(c), and
// its leading-digit bracket. scan is the work of finding z: the ⌊z/9⌋
// zero limbs and the limb holding c's last digit, at most t(dfull).
type powOperand struct {
	v        coefficientView // C
	dfull, z uint64
	d        uint64 // digits(c)
	scan     uint64
	log      powLog
}

func newPowOperand(x Decimal) powOperand {
	o := powOperand{v: coefficientViewOf(x)}
	o.dfull, _ = arithmeticDigits(&o.v)
	o.z = countTrailingZeros(&o.v)
	o.d = o.dfull - o.z
	o.scan = o.z/9 + 1
	o.log = newPowLog(powTop(&o.v, o.dfull), o.d <= 19)
	return o
}

// lastDigit is c's lowest digit.
func (o *powOperand) lastDigit() uint32 { return quantizeDigit(&o.v, o.z) }

// powZero is x^n for a zero x and n ≠ 0: an unsigned zero at n·e, or
// ErrDivisionByZero for n < 0. finalWork is W for one digit.
func powZero(n int32, e int32, finalWork uint64, budget limits, op string) (Decimal, Conditions, error) {
	if n < 0 {
		return contextFailure(op, ErrDivisionByZero)
	}
	exponent := int64(n) * int64(e)
	if exponent < math.MinInt32 || exponent > math.MaxInt32 {
		return contextFailure(op, ErrExponentRange)
	}
	if !admitted(budget.MaxDigits, 1, true) || !admitted(budget.MaxWork, finalWork, true) {
		return contextFailure(op, ErrInsufficientStorage)
	}
	return zeroDecimal(int32(exponent)), 0, nil
}

// powUnlimited is bare Pow and a context with unlimited precision.
func (d Decimal) powUnlimited(n int32, budget limits, op string, cnt *powCount) (Decimal, Conditions, error) {
	switch {
	case n == 0:
		if !admitted(budget.MaxDigits, 1, true) || !admitted(budget.MaxWork, 1, true) {
			return contextFailure(op, ErrInsufficientStorage)
		}
		return New(1, 0), 0, nil
	case d.isZero():
		return powZero(n, d.exponent(), 1, budget, op)
	case n == 1:
		return d.roundToPrecision(Context{arith: budget}, op)
	case n == -1:
		result, conditions, err := One().divUnlimited(d, budget, op)
		if ce, ok := err.(*Error); ok && ce.Remedy == divRemedy {
			ce.Remedy = powRemedy
		}
		return result, conditions, err
	}
	if n > 1 && cnt == nil && budget == (limits{}) && d.slow == nil {
		if a, b, ok := powInlineFactors(d, n); ok {
			if result, ok := inlineMul(a, b); ok {
				return result, 0, nil
			}
		}
	}
	o := newPowOperand(d)
	cnt.add(o.scan)
	m := powMagnitude(n)
	negative := d.negative() && n&1 != 0
	var result Decimal
	var err error
	if n > 0 {
		result, err = o.powPositive(m, d.exponent(), negative, budget, op, cnt)
	} else {
		result, err = o.powReciprocal(m, d.exponent(), negative, budget, op, cnt)
	}
	return result, 0, err
}

// powInlineFactors returns inline a and b with a·b = x^n exactly, in the
// repeated-multiplication cohort (coefficient C^n at exponent n·e), for a
// nonzero inline x and n ≥ 2: left-to-right binary exponentiation whose
// every multiplication but the last is an exact inline product. The last
// is left to the caller, who may round it. ok is false when a partial
// power leaves 128 bits or its exponent leaves int32.
func powInlineFactors(x Decimal, n int32) (a, b Decimal, ok bool) {
	acc := x
	for bit := bits.Len32(uint32(n)) - 2; ; bit-- {
		odd := n>>uint(bit)&1 != 0
		if bit == 0 && !odd {
			return acc, acc, true
		}
		if acc, ok = inlineMul(acc, acc); !ok {
			return Decimal{}, Decimal{}, false
		}
		if odd {
			if bit == 0 {
				return acc, x, true
			}
			if acc, ok = inlineMul(acc, x); !ok {
				return Decimal{}, Decimal{}, false
			}
		}
	}
}

// powWideOdd returns the coefficient C^n and the cohort exponent n·e of a
// nonzero inline x for an odd n ≥ 3 that powInlineFactors declines: the
// partial power C^((n−1)/2) is inline but its square is not, and the square
// times C still fits 256 bits. With powInlineFactors, whose final product
// of two inline factors covers every even n and every odd n with an inline
// square, this serves every power below 2^256. ok is false for an even n,
// a wider partial power, a product of 2^256 or more and a partial exponent
// outside int32.
//
//go:noinline
func powWideOdd(x Decimal, n int32) (power wide256, exponent int64, ok bool) {
	if n&1 == 0 {
		return wide256{}, 0, false
	}
	half := x
	if h := n >> 1; h > 1 {
		a, b, ok := powInlineFactors(x, h)
		if !ok {
			return wide256{}, 0, false
		}
		if half, ok = inlineMul(a, b); !ok {
			return wide256{}, 0, false
		}
	}
	power = mulWide(half.words, half.words)
	if !power.mulWords(x.words) {
		return wide256{}, 0, false
	}
	return power, int64(n) * int64(x.exponent()), true
}

// powPositive is the bare exact power for n = m ≥ 2: c^m followed by m·z
// zeros at exponent m·e.
func (o *powOperand) powPositive(m uint64, e int32, negative bool, budget limits, op string, cnt *powCount) (Decimal, error) {
	exponent := int64(m) * int64(e)
	if exponent < math.MinInt32 || exponent > math.MaxInt32 {
		return arithmeticFailure(op, ErrExponentRange)
	}
	plan := newPowPlan(o.log, o.d, m)
	zeros, ok1 := arithmeticMul(m, o.z)
	lo, ok2 := arithmeticAdd(plan.lo, zeros)
	hi, ok3 := arithmeticAdd(plan.hi, zeros)
	charge, ok4 := checkedSum(plan.charge, zeros, o.scan)
	if !plan.ok || !ok1 || !ok2 || !ok3 || !ok4 {
		return arithmeticFailure(op, ErrInsufficientStorage)
	}
	if !admitted(budget.MaxDigits, lo, true) || !admitted(budget.MaxWork, charge, true) {
		return arithmeticFailure(op, ErrInsufficientStorage)
	}
	strip := powStripLimbs(&o.v, o.z, o.d)
	total, ok := checkedSum(2*(plan.limbs+1), strip)
	var stack [powStackLimbs]uint32
	arena, admittedPlan := powScratch(&stack, total, hi)
	if !ok || !admittedPlan {
		return arithmeticFailure(op, ErrInsufficientStorage)
	}
	x, y := arena.take(plan.limbs+1), arena.take(plan.limbs+1)
	c := powStrip(&o.v, o.z, arena.take(strip))
	if cnt != nil {
		cnt.exact = true
	}
	r := powExact(&c, m, x, y, cnt)
	return powPublish(r, zeros, exponent, negative, budget, op, cnt)
}

// powPredicateSteps is the base and the power removed per pass of the
// terminating-reciprocal test: 2²⁹ and 5¹² fit one limb.
func powPredicateSteps(five bool) (base, q, step uint64) {
	if five {
		return 5, 244_140_625, 12
	}
	return 2, 1 << 29, 29
}

// powPredicateMax bounds the exponent a of a d-digit c = 2^a (a <
// d·log2 10) or c = 5^a (a < d·log5 10).
func powPredicateMax(d uint64, five bool) uint64 {
	if five {
		return d/1000*1431 + d%1000*1431/1000
	}
	return d/1000*3322 + d%1000*3322/1000
}

// powPredicateCharge is the test's work bound t(d)·(1 + ⌊a_max/step⌋):
// each pass that divides by 2²⁹ (or 5¹²) touches at most t(d) limbs, and
// at most one pass fails or finishes on a single limb.
func powPredicateCharge(d uint64, five bool) (uint64, bool) {
	_, _, step := powPredicateSteps(five)
	return arithmeticMul(digitLimbs(d), 1+powPredicateMax(d, five)/step)
}

// powPredicate reports whether the trimmed limbs v (destroyed) are 2^a (or
// 5^a when five), and a.
func powPredicate(v []uint32, five bool, cnt *powCount) (uint64, bool) {
	base, q, step := powPredicateSteps(five)
	var a uint64
	for {
		cnt.add(uint64(len(v)))
		if len(v) == 1 && uint64(v[0]) < q {
			x := uint64(v[0])
			for x > 1 {
				if x%base != 0 {
					return 0, false
				}
				x /= base
				a++
			}
			return a, x == 1
		}
		var r uint64
		for i := len(v) - 1; i >= 0; i-- {
			cur := r*decimalLimbBase + uint64(v[i])
			v[i] = uint32(cur / q)
			r = cur % q
		}
		if r != 0 {
			return 0, false
		}
		v = trimLimbs(v)
		a += step
	}
}

// powReciprocal is the bare exact power for n = −m ≤ −2. 1/x^m terminates
// iff c = 2^a or c = 5^b (Div's predicate on C); the value is then
// 5^(a·m) (or 2^(b·m)) at exponent −m·(e+z+a) (or +b), the cohort of
// Div(1, x)^m and of Div(1, x^m) alike.
func (o *powOperand) powReciprocal(m uint64, e int32, negative bool, budget limits, op string, cnt *powCount) (Decimal, error) {
	var five bool
	switch digit := o.lastDigit(); {
	case o.d == 1 && digit == 1:
	case digit%2 == 0:
	case digit == 5:
		five = true
	default:
		return Decimal{}, conditionError(op, Inexact, powRemedy)
	}
	var stack [powStackLimbs]uint32
	var a uint64
	prior := o.scan
	if o.d > 1 || o.lastDigit() != 1 {
		test, ok1 := powPredicateCharge(o.d, five)
		charge, ok2 := arithmeticAdd(prior, test)
		if !admitted(budget.MaxWork, charge, ok1 && ok2) {
			return arithmeticFailure(op, ErrInsufficientStorage)
		}
		prior = charge
		limbs := digitLimbs(o.d)
		arena, admittedCopy := powScratch(&stack, limbs, 0)
		if !admittedCopy {
			return arithmeticFailure(op, ErrInsufficientStorage)
		}
		v := powTruncate(&o.v, o.z, arena.take(limbs))
		var terminates bool
		if a, terminates = powPredicate(v, five, cnt); !terminates {
			return Decimal{}, conditionError(op, Inexact, powRemedy)
		}
	}
	shift, ok1 := arithmeticAdd(o.z, a)
	scale, ok2 := arithmeticMul(m, shift)
	if !ok1 || !ok2 || scale > math.MaxInt64/2 {
		return arithmeticFailure(op, ErrExponentRange)
	}
	exponent := -int64(m)*int64(e) - int64(scale)
	if exponent < math.MinInt32 || exponent > math.MaxInt32 {
		return arithmeticFailure(op, ErrExponentRange)
	}
	power, ok := arithmeticMul(a, m)
	if !ok {
		return arithmeticFailure(op, ErrInsufficientStorage)
	}
	// c = 2^a gives 5^(a·m), c = 5^b gives 2^(b·m), and c = 1 gives 1.
	base := uint64(5)
	if five {
		base = 2
	}
	if a == 0 {
		base = 1
	}
	bv := coefficientView{inline: [5]uint32{uint32(base)}, count: 1}
	plan := newPowPlan(newPowLog(base*1_000_000_000_000_000_000, true), 1, power)
	charge, ok := arithmeticAdd(prior, plan.charge)
	if !plan.ok || !admitted(budget.MaxDigits, plan.lo, true) || !admitted(budget.MaxWork, charge, ok) {
		return arithmeticFailure(op, ErrInsufficientStorage)
	}
	arena, admittedPlan := powScratch(&stack, 2*(plan.limbs+1), plan.hi)
	if !admittedPlan {
		return arithmeticFailure(op, ErrInsufficientStorage)
	}
	x, y := arena.take(plan.limbs+1), arena.take(plan.limbs+1)
	if cnt != nil {
		cnt.exact = true
	}
	r := x[:1]
	r[0] = 1
	if power != 0 {
		r = powExact(&bv, power, x, y, cnt)
	}
	return powPublish(r, 0, exponent, negative, budget, op, cnt)
}

// powGuard is the guard digit count g = ⌈log10(2m)⌉ + 2.
func powGuard(m uint64) uint64 {
	g := uint64(0)
	for p := uint64(1); p < 2*m; p *= 10 {
		g++
	}
	return g + 2
}

// powDivCharge bounds the Div-kernel charge of 1 divided by a dy-digit
// integer at a numerator of at most dy+p+1 digits (the Div plan's reads +
// dy + 1, the normalization 2(tn+n+1) and the loop 2(tn−n+1)(n+1), with
// tn − n ≤ ⌈(p+1)/9⌉ for every divisor of at most dy digits).
func powDivCharge(dy, p uint64) (uint64, bool) {
	n := digitLimbs(dy)
	tn := digitLimbs(dy + p + 1)
	base, ok1 := checkedSum(dy+p+1, dy, 1)
	loop, ok2 := arithmeticMul((p+9)/9+1, n+1)
	loop, ok3 := arithmeticMul(loop, 2)
	norm, ok4 := arithmeticMul(tn+n+1, 2)
	total, ok5 := checkedSum(base, loop, norm)
	return total, ok1 && ok2 && ok3 && ok4 && ok5 && dy+p+1 > dy
}

// powDivLimbs is the division scratch for such a quotient: the numerator
// with its spare limb, the divisor, and a quotient with its carry limb.
func powDivLimbs(dy, p uint64) (num, den, quot uint64) {
	tn := digitLimbs(dy + p + 1)
	return tn + 1, digitLimbs(dy), tn + 1
}

// powLevelCharge is one truncated level's charge: two
// truncated exponentiations of at most 2⌈log2 m⌉ products each at
// t(w)²+2w, plus two reciprocal divisions for n < 0.
func powLevelCharge(w, m, p uint64, reciprocal bool) (uint64, bool) {
	tw := digitLimbs(w)
	product, ok1 := arithmeticMul(tw, tw)
	product, ok2 := checkedSum(product, w, w)
	steps, ok3 := arithmeticMul(4, uint64(bits.Len64(m-1)))
	charge, ok4 := arithmeticMul(steps, product)
	ok := ok1 && ok2 && ok3 && ok4
	if reciprocal {
		div, ok5 := powDivCharge(w, p)
		div, ok6 := arithmeticMul(div, 2)
		charge, ok = checkedSum(charge, div)
		ok = ok && ok5 && ok6
	}
	return charge, ok
}

// powLevelLimbs is one level's scratch: the two truncated bases and two
// running powers of w digits (each with a spare limb), one product buffer,
// and for n < 0 the division numerator, divisor and two quotients.
func powLevelLimbs(w, p uint64, reciprocal bool) uint64 {
	tw := digitLimbs(w)
	total := 4*(tw+1) + 2*tw + 1
	if reciprocal {
		num, den, quot := powDivLimbs(w, p)
		total += num + den + 2*quot
	}
	return total
}

// powExactLimbs is the context exact path's scratch: the plan's two
// product buffers, the stripped copy of c, the padded result of at most
// pad digits (n > 0) or the reciprocal division (n < 0). The path sizes
// pad by the result it can publish, min(p, Dhi + m·z); the estimator,
// which sees only a shape, passes p.
func powExactLimbs(plan powPlan, strip, pad, p uint64, reciprocal bool) uint64 {
	total := 2*(plan.limbs+1) + strip
	if reciprocal {
		num, den, quot := powDivLimbs(plan.hi, p)
		return total + num + den + quot
	}
	return total + digitLimbs(pad) + 1
}

// powTruncProduct multiplies a and b into prod, truncates the product to
// at most w digits (rounding up when up and a nonzero digit was dropped),
// and writes it into dst (cleared). It returns the result and the number
// of digits dropped.
func powTruncProduct(dst, prod []uint32, a, b *coefficientView, w uint64, up bool, cnt *powCount) ([]uint32, int64) {
	r := powMultiply(prod, a, b, cnt)
	var k uint64
	if dp := limbsDigits(r); dp > w {
		k = dp - w
		v := powView(r)
		guard, sticky, _ := quantizeDiscard(&v, k)
		shiftRightDigits(r, k)
		r = trimLimbs(r)
		if up && (guard != 0 || sticky) {
			// A carry past r's top limb needs r = 10^(9·len(r)) − 1, so
			// w = 9·len(r) < dp and the product's cleared limbs hold it.
			r = incrementLimbs(r)
			if limbsDigits(r) > w { // exactly 10^w
				shiftRightDigits(r, 1)
				r = trimLimbs(r)
				k++
			}
		}
	}
	clear(dst)
	copy(dst, r)
	return dst[:len(r)], int64(k)
}

// powTruncPower brackets base^m at w digits from one side: base holds the
// truncated base at scale s (its value is base·10^s), and the result is
// r·10^scale.
func powTruncPower(base []uint32, s int64, m, w uint64, up bool, cur, prod []uint32, cnt *powCount) ([]uint32, int64) {
	clear(cur)
	r := cur[:copy(cur, base)]
	scale := s
	bv := powView(base)
	for i := bits.Len64(m) - 2; i >= 0; i-- {
		v := powView(r)
		var k int64
		r, k = powTruncProduct(cur, prod, &v, &v, w, up, cnt)
		scale = 2*scale + k
		if m>>uint(i)&1 == 1 {
			v = powView(r)
			r, k = powTruncProduct(cur, prod, &v, &bv, w, up, cnt)
			scale += s + k
		}
	}
	return r, scale
}

// powBounds brackets C^m at width w from both sides (U is a second
// truncated exponentiation, rounded up): lower·10^scaleL ≤ C^m ≤
// upper·10^scaleU, each of at most w digits.
func (o *powOperand) powBounds(m, w uint64, arena *powArena, cnt *powCount) (lower []uint32, scaleL int64, upper []uint32, scaleU int64) {
	tw := digitLimbs(w)
	baseL, baseU := arena.take(tw+1), arena.take(tw+1)
	curL, curU := arena.take(tw+1), arena.take(tw+1)
	prod := arena.take(2*tw + 1)
	// The truncated base: c itself when it has at most w digits, else its
	// leading w digits at scale dfull−w; the dropped part then contains
	// c's nonzero last digit, so the upward base is one unit more.
	var bl, bu []uint32
	var sl, su int64
	if o.d <= w {
		sl, su = int64(o.z), int64(o.z)
		bl = powTruncate(&o.v, o.z, baseL)
		bu = baseU[:copy(baseU, bl)]
		cnt.add(o.d)
	} else {
		s := o.dfull - w
		sl, su = int64(s), int64(s)
		bl = powTruncate(&o.v, s, baseL)
		copy(baseU, bl)
		bu = incrementLimbs(baseU[:len(bl)])
		if limbsDigits(bu) > w { // exactly 10^w
			shiftRightDigits(bu, 1)
			bu = trimLimbs(bu)
			su++
		}
		cnt.add(w)
	}
	lower, scaleL = powTruncPower(bl, sl, m, w, false, curL, prod, cnt)
	upper, scaleU = powTruncPower(bu, su, m, w, true, curU, prod, cnt)
	return lower, scaleL, upper, scaleU
}

// powLevel is one truncated Ziv level at width w. It returns the (p+1)-digit
// prefix Q of the value's magnitude at exponent f (relative to C^m, or to
// 1/C^m for n < 0), with the value strictly inside (Q, Q+1)·10^f, or ok =
// false when the level cannot decide.
func (o *powOperand) powLevel(m, w, p uint64, reciprocal bool, arena *powArena, cnt *powCount) (q []uint32, f int64, ok bool) {
	lower, scaleL, upper, scaleU := o.powBounds(m, w, arena, cnt)
	dl, du := limbsDigits(lower), limbsDigits(upper)
	if !reciprocal {
		// f is the exponent of U's (p+1)th digit.
		f = scaleU + int64(du) - 1 - int64(p)
		dropU, dropL := int64(du)-int64(p)-1, f-scaleL
		if dropU < 1 || dropL < 0 || dropL > int64(dl) {
			return nil, 0, false
		}
		cnt.add(du + dl)
		shiftRightDigits(upper, uint64(dropU))
		shiftRightDigits(lower, uint64(dropL))
		qu, ql := trimLimbs(upper), trimLimbs(lower)
		if sqrtCompare(qu, ql) != 0 || cnt != nil && cnt.escalate {
			return nil, 0, false
		}
		return qu, f, true
	}
	// 1/C^m ∈ [1/U, 1/L]: both quotients at the exponent f of the (p+1)th
	// digit of 1/L.
	num, den, quot := powDivLimbs(w, p)
	nb, db := arena.take(num), arena.take(den)
	qL, qU := arena.take(quot), arena.take(quot)
	one := coefficientView{inline: [5]uint32{1}, count: 1}
	f = -scaleL - int64(dl) - int64(p)
	sL := divSource{x: one, y: powView(lower), dx: 1, dy: dl, ideal: -scaleL}
	pl := sL.plan(f)
	sU := divSource{x: one, y: powView(upper), dx: 1, dy: du, ideal: -scaleU}
	pu := sU.plan(f)
	if !pl.ok || !pu.ok || pl.path != divDivide || pu.path != divDivide || pl.dn > w+p+1 || pu.dn > w+p+1 {
		return nil, 0, false
	}
	rl, _ := sL.divDigits(pl, nb, db, qL, cnt.divCounter())
	ru, classU := sU.divDigits(pu, nb, db, qU, cnt.divCounter())
	if limbsDigits(ru) != p+1 || classU == divExactClass || sqrtCompare(rl, ru) != 0 || cnt != nil && cnt.escalate {
		return nil, 0, false
	}
	return ru, f, true
}

// powContext is PowWithContext: the special cases, then the exact path
// when c^m may have at most p+1 digits, and the Ziv loop otherwise.
func (d Decimal) powContext(n int32, ctx Context, budget limits, op string, cnt *powCount) (Decimal, Conditions, error) {
	if ctx.precision == 0 {
		return d.powUnlimited(n, budget, op, cnt)
	}
	var etiny int64
	if ctx.guarded {
		etiny = int64(ctx.guards.Emin) - (int64(ctx.precision) - 1)
	}
	switch {
	case n == 0:
		one := [2]uint32{1}
		return finishContext(one[:1:2], divExactClass, 0, etiny, 0, false, &ctx, 1, budget, op)
	case d.isZero():
		work, _ := contextFinalCharge(1, 1)
		return powZero(n, d.exponent(), work, budget, op)
	case n == 1:
		return d.roundToPrecision(ctx.withLimits(budget), op)
	case n == -1:
		return One().divContext(d, ctx, budget, op)
	}
	if n > 1 && cnt == nil && budget == (limits{}) && d.slow == nil {
		// The exact power of a short operand, rounded once as MulWithContext
		// rounds an exact product: the same cohort exponent n·e, the same
		// finisher outcomes, and every guard or Exact case deferred.
		if a, b, ok := powInlineFactors(d, n); ok {
			if exact, ok := inlineMul(a, b); ok {
				if contextExactFits(exact, ctx) {
					return exact, 0, nil
				}
				if rounded, events, ok := contextRoundInline(exact, ctx); ok {
					return contextOutcome(rounded, events, ctx.traps, op)
				}
			} else if rounded, events, ok := contextRoundWide(mulWide(a.words, b.words), int64(a.exponent())+int64(b.exponent()), a.negative() != b.negative(), ctx); ok {
				return contextOutcome(rounded, events, ctx.traps, op)
			}
		} else if power, exponent, ok := powWideOdd(d, n); ok {
			// An odd power takes the operand's sign.
			if rounded, events, ok := contextRoundWide(power, exponent, d.negative(), ctx); ok {
				return contextOutcome(rounded, events, ctx.traps, op)
			}
		}
	}
	o := newPowOperand(d)
	cnt.add(o.scan)
	m := powMagnitude(n)
	negative := d.negative() && n&1 != 0
	reciprocal := n < 0
	p := uint64(ctx.precision)
	dlo, dhi, ok := o.log.digits(o.d, m)
	zeros, ok2 := arithmeticMul(m, o.z)
	if !ok || !ok2 || zeros > math.MaxInt64/4 {
		return contextFailure(op, ErrInsufficientStorage)
	}
	me := int64(m) * int64(d.exponent()) // |m·e| ≤ 2⁶²
	mE := me + int64(zeros)              // the exponent of c^m
	if dlo <= p+1 {
		return o.powContextExact(m, me, mE, negative, reciprocal, &ctx, etiny, o.scan, budget, op, cnt)
	}
	// Here c^m has more than p+1 digits and a nonzero last digit: the value
	// needs more than p digits, except that 1/5^(b·m) = 2^(b·m)·10^(−b·m)
	// may be short (so a reciprocal of a c ending in 5 is decided below).
	shortReciprocal := reciprocal && o.lastDigit() == 5
	if ctx.rounding == Exact && !shortReciprocal {
		return contextExactRefusal(op)
	}
	// The value's adjusted exponent lies in [adjLo, adjHi].
	adjLo, adjHi := mE+int64(dlo)-1, mE+int64(dhi)-1
	if reciprocal {
		adjLo, adjHi = -mE-int64(dhi), -mE-int64(dlo)
	}
	precision := int64(p)
	if ctx.guarded {
		if adjLo > int64(ctx.guards.Emax) {
			if ctx.rounding == Exact {
				return contextExactRefusal(op)
			}
			return contextOverflow(o.scan, negative, ctx, budget, op)
		}
		if adjHi < etiny-1 {
			// Below a tenth of the Etiny quantum: 0 or one quantum.
			empty := [1]uint32{}
			return finishContext(empty[:0:1], divBelow, etiny-1, etiny, etiny, negative, &ctx, o.scan, budget, op)
		}
	} else if !shortReciprocal && (adjLo-precision+1 > math.MaxInt32 || adjHi-precision+2 < math.MinInt32) ||
		shortReciprocal && ctx.rounding != Exact && adjLo-precision+1 > math.MaxInt32 {
		// A result exponent certainly outside int32. A short reciprocal may
		// be exact with fewer than p digits, so its exponent can sit above
		// adj − p + 1: only the upper edge is certain. Under Exact it is
		// not pre-decided at all, so an inexact value still reports the
		// Exact refusal first, as for n > 0 and Div.
		return contextFailure(op, ErrExponentRange)
	}
	charge := o.scan
	chargeOK := true
	w := p + 1 + powGuard(m)
	var stack [powStackLimbs]uint32
	for w < dhi {
		level, ok := powLevelCharge(w, m, p, reciprocal)
		charge, ok2 = arithmeticAdd(charge, level)
		chargeOK = chargeOK && ok && ok2
		if !admitted(budget.MaxWork, charge, chargeOK) {
			return contextFailure(op, ErrInsufficientStorage)
		}
		arena, admittedLevel := powScratch(&stack, powLevelLimbs(w, p, reciprocal), p+1)
		if !admittedLevel {
			return contextFailure(op, ErrInsufficientStorage)
		}
		if cnt != nil {
			cnt.levels = append(cnt.levels, w)
		}
		if q, f, accepted := o.powLevel(m, w, p, reciprocal, &arena, cnt); accepted {
			tPrime := f + me // Q is relative to C^m, and the value is C^m·10^(m·e)
			if reciprocal {
				tPrime = f - me
			}
			return finishContext(q, divBelow, tPrime, etiny, tPrime, negative, &ctx, charge, budget, op)
		}
		if w > math.MaxUint64/2 {
			break
		}
		w *= 2
	}
	if !chargeOK {
		charge = math.MaxUint64
	}
	return o.powContextExact(m, me, mE, negative, reciprocal, &ctx, etiny, charge, budget, op, cnt)
}

// powContextExact rounds the exact c^m (or its reciprocal) once. prior is
// the charge of the truncated levels already run.
func (o *powOperand) powContextExact(m uint64, me, mE int64, negative, reciprocal bool, ctx *Context, etiny int64, prior uint64, budget limits, op string, cnt *powCount) (Decimal, Conditions, error) {
	p := uint64(ctx.precision)
	plan := newPowPlan(o.log, o.d, m)
	charge, ok := arithmeticAdd(prior, plan.charge)
	ok = ok && plan.ok && prior != math.MaxUint64
	if reciprocal {
		div, ok2 := powDivCharge(plan.hi, p)
		charge, ok = arithmeticAdd(charge, div)
		ok = ok && ok2
	}
	if !admitted(budget.MaxWork, charge, ok) || !plan.ok {
		return contextFailure(op, ErrInsufficientStorage)
	}
	strip := powStripLimbs(&o.v, o.z, o.d)
	// A guarded overflow is already certain from the exact power's lower
	// digit bound. Apply the same finisher, charge and Exact precedence
	// before restoring any cohort zeros.
	if !reciprocal && ctx.guarded && mE+int64(plan.lo)-1 > int64(ctx.guards.Emax) {
		if ctx.rounding == Exact {
			return contextExactRefusal(op)
		}
		return contextOverflow(charge, negative, *ctx, budget, op)
	}
	// Restore only cohort zeros that survive precision and Etiny. Zeros
	// below Etiny are discarded exactly; finishContext still records
	// Rounded from the original ideal exponent me.
	zeros := uint64(mE - me)
	if !reciprocal && ctx.guarded {
		zeros = min(zeros, uint64(max(int64(0), mE-etiny)))
	}
	pad := p
	if !reciprocal && plan.hi <= p && zeros <= p-plan.hi {
		pad = plan.hi + zeros
	}
	// Only pre-decide the publication cap when every possible power fits
	// exactly, avoids guarded overflow and has a representable cohort
	// exponent. Exact/range refusals stay ahead of publication quotas.
	if !reciprocal && plan.hi <= p && budget.MaxDigits != 0 {
		loExponent := mE - int64(min(zeros, p-plan.lo))
		hiExponent := mE - int64(min(zeros, p-plan.hi))
		exact := !ctx.guarded || mE >= etiny && mE+int64(plan.hi)-1 <= int64(ctx.guards.Emax)
		least := plan.lo + min(zeros, p-plan.lo)
		if exact && loExponent >= math.MinInt32 && hiExponent <= math.MaxInt32 && least > budget.MaxDigits {
			return contextFailure(op, ErrInsufficientStorage)
		}
	}
	var stack [powStackLimbs]uint32
	limbs, resultBound := powExactLimbs(plan, strip, pad, p, reciprocal), p+1
	if reciprocal {
		// Size the power independently of unused quotient precision.
		limbs, resultBound = 2*(plan.limbs+1)+strip, 0
	}
	arena, admittedPlan := powScratch(&stack, limbs, resultBound)
	if !admittedPlan {
		return contextFailure(op, ErrInsufficientStorage)
	}
	x, y := arena.take(plan.limbs+1), arena.take(plan.limbs+1)
	c := powStrip(&o.v, o.z, arena.take(strip))
	if cnt != nil {
		cnt.exact = true
	}
	r := powExact(&c, m, x, y, cnt)
	if !reciprocal {
		// The cohort C^m·10^(m·e) = c^m·10^(mE): pad at most p − D of the
		// m·z zeros back, so an exact power that fits keeps the exponent
		// nearest m·e.
		dr := limbsDigits(r)
		var k uint64
		if dr < p {
			k = min(zeros, p-dr)
		}
		if k > 0 {
			count := digitLimbs(dr + k)
			buf := arena.take(digitLimbs(pad) + 1)
			powShiftLeft(buf[:count], r, k)
			r = buf[:count]
		}
		return finishContext(r, divExactClass, mE-int64(k), etiny, me, negative, ctx, charge, budget, op)
	}
	// 1/(c^m·10^mE) through the Div context kernel; its exact quotient is
	// stripped toward −mE, which leaves the reciprocal cohort.
	dr := limbsDigits(r)
	one := coefficientView{inline: [5]uint32{1}, count: 1}
	s := divSource{x: one, y: powView(r), dx: 1, dy: dr, ideal: -mE, negative: negative}
	tPrime, _ := divContextTarget(1, dr, -mE, *ctx)
	dp := s.plan(tPrime)
	live, ok := divScratchHeap(limbs, powStackLimbs)
	if !ok {
		return contextFailure(op, ErrInsufficientStorage)
	}
	return s.contextQuotient(dp, tPrime, etiny, ctx, charge, budget, op, cnt.divCounter(), live, true)
}
