// SPDX-License-Identifier: Apache-2.0

package decimal

import "math/bits"

// Integer division: q = trunc(x/y) and n = nearestEven(x/y); Quo is q at
// exponent 0, Rem is x − q·y and RemNear is x − n·y, both at exponent
// min(ex, ey). Resources use the Div family's unit: a precharge B before
// any scan, a path charge C before the arena and W = B + C + 2N + 1.

// Quo returns the truncated integer quotient trunc(x/y) at exponent 0,
// exactly. It never rounds and has no precision limit. A zero divisor
// returns ErrDivisionByZero, or ErrDivisionUndefined for 0/0.
func (d Decimal) Quo(other Decimal) (Decimal, error) {
	return d.intDivideBare(other, intDivQuo, limits{}, "Quo")
}

// QuoWithContext is Quo under a context: a finite precision p refuses a
// quotient of more than p digits with ErrDivisionImpossible, and exponent
// guards refuse an out-of-range result with ErrInvalidOperation. The
// integer result never depends on the rounding mode.
func (d Decimal) QuoWithContext(other Decimal, ctx Context) (Decimal, Conditions, error) {
	return d.intDivide(other, intDivQuo, ctx, ctx.arith, "QuoWithContext", nil)
}

// Rem returns the exact remainder x − q·y of the truncated quotient at
// exponent min(ex, ey): 10.5 Rem 3 is 1.5 and 3 Rem 0.29 is 0.10. A nonzero
// remainder has the dividend's sign; zero is unsigned. The quotient is never
// materialized, so a large exponent gap costs O(log gap).
func (d Decimal) Rem(other Decimal) (Decimal, error) {
	return d.intDivideBare(other, intDivRem, limits{}, "Rem")
}

// RemWithContext is Rem under a context: a finite precision refuses a
// truncated quotient of more than p digits with ErrDivisionImpossible, even
// when the remainder is zero; the remainder itself is never rounded.
func (d Decimal) RemWithContext(other Decimal, ctx Context) (Decimal, Conditions, error) {
	return d.intDivide(other, intDivRem, ctx, ctx.arith, "RemWithContext", nil)
}

// RemNear returns the exact x − n·y for the nearest integer n to x/y, a tie
// selecting the even n, at exponent min(ex, ey): 10 RemNear 6 is −2. A
// nonzero result may have either sign; zero is unsigned.
func (d Decimal) RemNear(other Decimal) (Decimal, error) {
	return d.intDivideBare(other, intDivRemNear, limits{}, "RemNear")
}

// RemNearWithContext is RemNear under a context. Its precision limits the
// truncated quotient q, as for Rem; a nearest n of p+1 digits is not a
// failure.
func (d Decimal) RemNearWithContext(other Decimal, ctx Context) (Decimal, Conditions, error) {
	return d.intDivide(other, intDivRemNear, ctx, ctx.arith, "RemNearWithContext", nil)
}

type intDivOp uint8

const (
	intDivQuo intDivOp = iota
	intDivRem
	intDivRemNear
)

// intDivPath names the integer-division paths.
type intDivPath uint8

const (
	intDivZeroDividend intDivPath = iota // x = 0
	intDivQZero                          // q = 0: Quo zero, Rem x, RemNear with δ ≤ −2
	intDivQZeroNear                      // q = 0, RemNear with δ ≥ −1: compare |x| with |y| − |x|
	intDivQuotient                       // q ≠ 0, Quo: the division kernel at exponent 0
	intDivSplit                          // q ≠ 0, remainder, k < 0: kernel on the high part
	intDivStream                         // q ≠ 0, remainder, k ≥ 0: kernel on Cx·10^k
	intDivModular                        // q ≠ 0, remainder, k ≥ 0: Cx·10^k mod 2Cy
)

// intDivForce is the test seam that pins the stream/modular choice
// (TestRemStreamMatchesModular). Production never sets it.
type intDivForce uint8

const (
	intDivForceNone intDivForce = iota
	intDivForceStream
	intDivForceModular
)

// quoRemCount records integer-division work for the tariff tests through
// the division kernel's divCount seam: classification units (covered by B), path units
// including the kernel's own (covered by C), output limb writes (covered
// by 2N+1) and the arena. Production passes nil; it is never package state.
type quoRemCount struct {
	classify divCount
	path     divCount
	out      divCount
	arena    uint64 // limbs of the arena allocated or sliced, 0 if none
	taken    intDivPath
	force    intDivForce
}

func (c *quoRemCount) classifier() *divCount {
	if c == nil {
		return nil
	}
	return &c.classify
}

func (c *quoRemCount) pathCounter() *divCount {
	if c == nil {
		return nil
	}
	return &c.path
}

func (c *quoRemCount) output() *divCount {
	if c == nil {
		return nil
	}
	return &c.out
}

func (c *quoRemCount) forced() intDivForce {
	if c == nil {
		return intDivForceNone
	}
	return c.force
}

// intDivShape is what the planner sees: coefficient digits and exponents of
// two nonzero operands.
type intDivShape struct {
	dx, dy uint64
	ex, ey int32
}

func (s intDivShape) k() int64 { return int64(s.ex) - int64(s.ey) }

// delta is δ = (dx+ex) − (dy+ey): q = 0 when δ < 0, and otherwise a
// nonzero q has δ or δ+1 digits. Digit counts of addressable
// coefficients fit int64.
func (s intDivShape) delta() int64 {
	return int64(s.dx) + int64(s.ex) - int64(s.dy) - int64(s.ey)
}

// intDivPrecharge is B: 1 for a zero dividend, otherwise dx + dy + 1.
func intDivPrecharge(dx, dy uint64, xZero bool) (uint64, bool) {
	if xZero {
		return 1, true
	}
	return checkedSum(dx, dy, 1)
}

// intDivPlan is one path's charge C, result-digit envelope and arena.
type intDivPlan struct {
	path  intDivPath
	c     uint64
	nEnv  uint64
	arena uint64
	ok    bool
}

// kernelPlan is the division kernel's plan K0 at division exponent 0 and its scratch
// S0 (numerator, divisor and quotient limbs).
func (s intDivShape) kernelPlan() (divPlan, uint64, bool) {
	src := divSource{dx: s.dx, dy: s.dy, ideal: s.k()}
	p := src.plan(0)
	if !p.ok || p.path != divDivide {
		return p, 0, false
	}
	num, den, quot := src.divScratch(p)
	arena, ok := checkedSum(num, den, quot)
	return p, arena, ok
}

// divideLimbsCharge is the division kernel's divideLimbs bound D(u, v) =
// 2(u−v+1)(v+1) + 2(u+v+1) for u ≥ v.
func divideLimbsCharge(u, v uint64) (uint64, bool) {
	loop, ok1 := arithmeticMul(u-v+1, v+1)
	loop, ok2 := arithmeticMul(loop, 2)
	norm, ok3 := checkedSum(u, v, 1)
	norm, ok4 := arithmeticMul(norm, 2)
	sum, ok5 := arithmeticAdd(loop, norm)
	return sum, ok1 && ok2 && ok3 && ok4 && ok5
}

// modularCharge is Cm = t(dx)·μH + bitlen(k)·(μS+μH) + μS + 8n′ + 4 with
// μH = 2n′+1+D(n′+1, n′) and μS = n′²+3n′+D(2n′, n′), and the arena 7n′+4.
// n′ = t(dy+1) bounds the limbs of 2·Cy.
func (s intDivShape) modularCharge() (c, arena uint64, ok bool) {
	np := digitLimbs(s.dy + 1)
	dh, ok1 := divideLimbsCharge(np+1, np)
	ds, ok2 := divideLimbsCharge(2*np, np)
	muH, ok3 := checkedSum(2*np, 1, dh)
	sq, ok4 := arithmeticMul(np, np)
	muS, ok5 := checkedSum(sq, 3*np, ds)
	horner, ok6 := arithmeticMul(digitLimbs(s.dx), muH)
	perBit, ok7 := arithmeticAdd(muS, muH)
	bitsTerm, ok8 := arithmeticMul(uint64(bits.Len64(uint64(s.k()))), perBit)
	c, ok9 := checkedSum(horner, bitsTerm, muS, 8*np, 4)
	return c, 7*np + 4, ok1 && ok2 && ok3 && ok4 && ok5 && ok6 && ok7 && ok8 && ok9
}

// planIntDiv selects the path after classification and prices it.
// qZero and Q come from the classifier; the estimators pass the shape's
// worst case. It is the one planner of the operations and estimators.
func planIntDiv(op intDivOp, s intDivShape, qZero bool, q uint64, force intDivForce) intDivPlan {
	k := s.k()
	if qZero {
		if op == intDivQuo {
			return intDivPlan{path: intDivQZero, nEnv: 1, ok: true}
		}
		var pad uint64
		nEnv := s.dx
		if k > 0 {
			pad = s.dx
			nEnv = s.dx + uint64(k) // q = 0 and k > 0 imply dx + k ≤ dy
		}
		if op == intDivRemNear && s.delta() >= -1 {
			var sx, sy uint64
			if k >= 0 {
				sx = uint64(k)
			} else {
				sy = uint64(-k)
			}
			l := max(s.dx+sx, s.dy+sy) // δ ≥ −1 bounds the offset: l ≤ max(dx+1, dy)
			c, ok := checkedSum(4*s.dx, 4*s.dy, pad)
			return intDivPlan{path: intDivQZeroNear, c: c, nEnv: max(l, nEnv), arena: digitLimbs(l), ok: ok}
		}
		return intDivPlan{path: intDivQZero, c: pad, nEnv: nEnv, ok: true}
	}
	kp, s0, ok := s.kernelPlan()
	if op == intDivQuo {
		return intDivPlan{path: intDivQuotient, c: kp.charge, nEnv: q, arena: s0, ok: ok}
	}
	n := digitLimbs(s.dy)
	if k < 0 {
		j := uint64(-k)
		c, okC := checkedSum(kp.charge, 3*j, 6*(n+1))
		return intDivPlan{path: intDivSplit, c: c, nEnv: min(s.dx, s.dy+j), arena: s0 + n + 1, ok: ok && okC}
	}
	cs, okS := arithmeticAdd(kp.charge, 6*(n+1))
	okS = okS && ok
	cm, am, okM := s.modularCharge()
	switch force {
	case intDivForceStream:
		okM = false
	case intDivForceModular:
		okS = false
	}
	switch {
	case okS && (!okM || cs <= cm):
		return intDivPlan{path: intDivStream, c: cs, nEnv: s.dy, arena: s0 + n + 1, ok: true}
	case okM:
		return intDivPlan{path: intDivModular, c: cm, nEnv: s.dy, arena: am, ok: true}
	}
	return intDivPlan{}
}

// intDivWork is W = B + C + 2N + 1, the Div finisher over B + C.
func intDivWork(b, c, n uint64) (uint64, bool) {
	bc, ok := arithmeticAdd(b, c)
	if !ok {
		return 0, false
	}
	return contextFinalCharge(bc, n)
}

func (d Decimal) intDivideBare(other Decimal, op intDivOp, budget limits, name string) (Decimal, error) {
	result, _, err := d.intDivide(other, op, Context{}, budget, name, nil)
	return result, err
}

// intDivide is the family's one kernel. It resolves failures in a fixed
// eight-stage order and allocates at most one arena, after the B and C
// admissions, and one result, after the final caps.
func (d Decimal) intDivide(other Decimal, op intDivOp, ctx Context, budget limits, name string, c *quoRemCount) (Decimal, Conditions, error) {
	// Stage 1: a zero divisor, before any budget.
	if other.isZero() {
		return Decimal{}, 0, divZero(d, name)
	}
	xZero := d.isZero()
	if c == nil && d.slow == nil && other.slow == nil && !xZero {
		// A budget is admitted by the bound of every inline call's charges,
		// or else by the kernel's own charges for this one.
		if result, events, ok := inlineIntDivide(d, other, op, &ctx); ok &&
			(budget.admits(inlineResultDigits, inlineIntDivWork) || intDivInlineAdmitted(d, other, op, result, budget)) {
			return contextOutcome(result, events, ctx.traps, name)
		}
	}
	var s intDivShape
	s.ex, s.ey = d.exponent(), other.exponent()
	x, y := coefficientViewOf(d), coefficientViewOf(other)
	s.dx, _ = arithmeticDigits(&x)
	s.dy, _ = arithmeticDigits(&y)
	// Stage 2: the classification precharge B, before reading a digit.
	b, ok := intDivPrecharge(s.dx, s.dy, xZero)
	if !ok || budget.MaxWork != 0 && b > budget.MaxWork {
		return contextFailure(name, ErrInsufficientStorage)
	}
	qZero, q := true, uint64(1)
	if !xZero {
		qZero, q = classifyIntDiv(&x, &y, s, c.classifier())
	}
	// Stage 3: quotient fit, even when the remainder would be zero.
	if ctx.precision != 0 && q > uint64(ctx.precision) {
		return contextFailure(name, ErrDivisionImpossible)
	}
	// Stage 4: the stored exponent t, and Quo's known adjusted exponent.
	t := int64(min(s.ex, s.ey))
	if op == intDivQuo {
		t = 0
	}
	if !intDivStoredRange(t, ctx) || ctx.guarded && op == intDivQuo && !qZero && int64(q)-1 > int64(ctx.guards.Emax) {
		return contextFailure(name, ErrInvalidOperation)
	}
	// Stage 5: the path charge and the physical admission of the arena
	// with the result envelope, before the arena; Quo also knows N = Q.
	var plan intDivPlan
	if xZero {
		plan = intDivPlan{path: intDivZeroDividend, nEnv: 1, ok: true}
	} else {
		plan = planIntDiv(op, s, qZero, q, c.forced())
	}
	bc, okBC := arithmeticAdd(b, plan.c)
	if !plan.ok || !okBC || budget.MaxWork != 0 && bc > budget.MaxWork {
		return contextFailure(name, ErrInsufficientStorage)
	}
	if op == intDivQuo {
		if w, ok := intDivWork(b, plan.c, plan.nEnv); !admitted(budget.MaxDigits, plan.nEnv, true) || !ok || !admitted(budget.MaxWork, w, true) {
			return contextFailure(name, ErrInsufficientStorage)
		}
	}
	if !divAdmitted(plan.arena, plan.nEnv) {
		return contextFailure(name, ErrInsufficientStorage)
	}
	if c != nil {
		c.taken = plan.path
		c.arena = plan.arena
	}
	var stack [divStackLimbs]uint32
	var arena []uint32
	if plan.arena > 0 {
		if plan.arena <= divStackLimbs {
			arena = stack[:plan.arena]
		} else {
			arena = make([]uint32, plan.arena)
		}
	}
	var r intDivResult
	switch plan.path {
	case intDivZeroDividend:
		r = intDivResult{n: 1, zero: true}
	case intDivQZero:
		r = qZeroResult(op, s, d.negative())
	case intDivQZeroNear:
		r = qZeroNearResult(arena, &x, &y, s, d.negative(), c.pathCounter())
	case intDivQuotient, intDivSplit, intDivStream:
		r = kernelResult(arena, op, &x, &y, s, d.negative(), other.negative(), c.pathCounter())
	case intDivModular:
		r = modularResult(arena, op, &x, &y, s, d.negative(), c.pathCounter())
	}
	// Stage 6: a guarded remainder's adjusted exponent, once N is known.
	if ctx.guarded && op != intDivQuo && !r.zero && t+int64(r.n)-1 > int64(ctx.guards.Emax) {
		return contextFailure(name, ErrInvalidOperation)
	}
	// Stage 7: the remainders' final digit and work caps, before the result.
	if op != intDivQuo {
		if w, ok := intDivWork(b, plan.c, r.n); !admitted(budget.MaxDigits, r.n, true) || !ok || !admitted(budget.MaxWork, w, true) {
			return contextFailure(name, ErrInsufficientStorage)
		}
	}
	// Stage 8: publish; Subnormal alone, which a trap converts.
	result := r.publish(d, &x, int32(t), c)
	var events Conditions
	if ctx.guarded && !r.zero && t+int64(r.n)-1 < int64(ctx.guards.Emin) {
		events = Subnormal
	}
	return contextOutcome(result, events, ctx.traps, name)
}

// inlineIntDivide is intDivide for two nonzero inline operands whose
// coefficients, aligned at t = min(ex, ey), both stay below 2^128: one
// two-word division gives q = trunc(x/y) and the remainder at t. It applies
// the kernel's stages 3, 4, 6 and 8 to the same q, stored exponent and
// result digits, and reports ok=false for every refusal, which the general
// path then owns. It charges nothing: the caller admits a budget.
func inlineIntDivide(d, other Decimal, op intDivOp, ctx *Context) (Decimal, Conditions, bool) {
	ex, ey := d.exponent(), other.exponent()
	t := min(ex, ey)
	x, okx := inlineScale(d.words, uint64(int64(ex)-int64(t)))
	y, oky := inlineScale(other.words, uint64(int64(ey)-int64(t)))
	if !okx || !oky {
		return Decimal{}, 0, false
	}
	q, r := inlineDivMod(x, y)
	if ctx.precision != 0 && inlineDigits(q) > uint64(ctx.precision) {
		return Decimal{}, 0, false
	}
	var result Decimal
	stored := int64(t)
	if op == intDivQuo {
		stored = 0
		result = inlineDecimal(q, 0, d.negative() != other.negative())
	} else {
		negative := d.negative()
		if op == intDivRemNear && r != (uint128{}) {
			// The nearest quotient is q+1 when 2r > y, or on a tie with
			// q odd; the remainder is then r − y, of the opposite sign.
			var rest uint128
			var borrow uint64
			rest.lo, borrow = bits.Sub64(y.lo, r.lo, 0)
			rest.hi, _ = bits.Sub64(y.hi, r.hi, borrow)
			if cmp := inlineCompare(r, rest); cmp > 0 || cmp == 0 && q.lo&1 != 0 {
				r, negative = rest, !negative
			}
		}
		result = inlineDecimal(r, t, negative)
	}
	if !ctx.guarded {
		return result, 0, true
	}
	if !intDivStoredRange(stored, *ctx) {
		return Decimal{}, 0, false
	}
	if result.isZero() {
		return result, 0, true
	}
	adjusted := stored + int64(inlineDigits(result.words)) - 1
	if adjusted > int64(ctx.guards.Emax) {
		return Decimal{}, 0, false
	}
	var events Conditions
	if adjusted < int64(ctx.guards.Emin) {
		events = Subnormal
	}
	return result, events, true
}

// intDivInlineAdmitted reports whether budget admits intDivide's charges
// for two nonzero inline operands whose result inlineIntDivide produced.
// It prices the call as the kernel does: the precharge B, the planner's
// path charge C and arena for the classifier's verdict (q = 0, or q's
// digit count), and the final W = B + C + 2N + 1 over the N digits of the
// result, which for Quo is the planner's envelope. W is at least B + C, so
// the final cap implies the earlier ones. Quo's result is the quotient;
// for a remainder the quotient is divided out again, from the operands
// aligned as inlineIntDivide aligned them.
//
//go:noinline
func intDivInlineAdmitted(d, other Decimal, op intDivOp, result Decimal, budget limits) bool {
	s := intDivShape{dx: inlineDigits(d.words), dy: inlineDigits(other.words), ex: d.exponent(), ey: other.exponent()}
	q := result.words
	if op != intDivQuo {
		t := min(s.ex, s.ey)
		x, _ := inlineScale(d.words, uint64(int64(s.ex)-int64(t)))
		y, _ := inlineScale(other.words, uint64(int64(s.ey)-int64(t)))
		q, _ = inlineDivMod(x, y)
	}
	qZero, qDigits := q == (uint128{}), uint64(1)
	if !qZero {
		qDigits = inlineDigits(q)
	}
	b, okB := intDivPrecharge(s.dx, s.dy, false)
	plan := planIntDiv(op, s, qZero, qDigits, intDivForceNone)
	n := plan.nEnv
	if op != intDivQuo {
		n = 1
		if !result.isZero() {
			n = inlineDigits(result.words)
		}
	}
	w, okW := intDivWork(b, plan.c, n)
	return okB && plan.ok && okW && budget.admits(n, w) && divAdmitted(plan.arena, plan.nEnv)
}

// inlineDivMod is the truncated quotient and remainder of two-word
// magnitudes, y nonzero. A one-word divisor takes two word divisions. A
// two-word divisor has a one-word quotient: the estimate from the top word
// of the normalized divisor is at most two too large (Knuth D), and the
// product q̂·y is walked down to at most x.
func inlineDivMod(x, y uint128) (q, r uint128) {
	if y.hi == 0 {
		if x.hi == 0 {
			return uint128{lo: x.lo / y.lo}, uint128{lo: x.lo % y.lo}
		}
		var rem uint64
		q.hi, rem = bits.Div64(0, x.hi, y.lo)
		q.lo, rem = bits.Div64(rem, x.lo, y.lo)
		return q, uint128{lo: rem}
	}
	if inlineCompare(x, y) < 0 {
		return uint128{}, x
	}
	s := uint(bits.LeadingZeros64(y.hi))
	yh := y.hi<<s | y.lo>>(64-s)
	qhat, _ := bits.Div64(x.hi>>(64-s), x.hi<<s|x.lo>>(64-s), yh)
	ph, pl := bits.Mul64(qhat, y.lo)
	th, tl := bits.Mul64(qhat, y.hi)
	pm, carry := bits.Add64(ph, tl, 0)
	pt := th + carry
	for pt != 0 || pm > x.hi || pm == x.hi && pl > x.lo {
		qhat--
		var borrow uint64
		pl, borrow = bits.Sub64(pl, y.lo, 0)
		pm, borrow = bits.Sub64(pm, y.hi, borrow)
		pt -= borrow
	}
	var borrow uint64
	r.lo, borrow = bits.Sub64(x.lo, pl, 0)
	r.hi, _ = bits.Sub64(x.hi, pm, borrow)
	return uint128{lo: qhat}, r
}

// classifyIntDiv decides q = 0, or q's digit count Q, from the exponents
// and one comparison of the significands aligned at their leading digits.
// It reads at most dx + dy digits and never scans an exponent gap.
func classifyIntDiv(x, y *coefficientView, s intDivShape, c *divCount) (qZero bool, q uint64) {
	c.add(1) // exponent metadata
	delta := s.delta()
	if delta < 0 {
		return true, 1
	}
	cmp := 0
	for i := range max(s.dx, s.dy) {
		if i >= s.dy {
			cmp = 1 // equal prefix and x is longer: x's significand is at least y's
			break
		}
		var a uint32
		if i < s.dx {
			a = quantizeDigit(x, s.dx-1-i)
			c.add(1)
		}
		b := quantizeDigit(y, s.dy-1-i)
		c.add(1)
		if a != b {
			cmp = 1
			if a < b {
				cmp = -1
			}
			break
		}
	}
	if delta == 0 {
		return cmp < 0, 1
	}
	if cmp < 0 {
		return false, uint64(delta)
	}
	return false, uint64(delta) + 1
}

// intDivEmit names how a result's coefficient is produced after the caps.
type intDivEmit uint8

const (
	intDivEmitLimbs   intDivEmit = iota // limbs already hold the coefficient
	intDivEmitOperand                   // the dividend itself (q = 0 Rem, ex ≤ ey)
	intDivEmitShifted                   // Cx·10^k (q = 0 Rem, k > 0)
	intDivEmitSplit                     // high·10^j + L, or high·10^j + (10^j − L)
)

// intDivResult is a finished result before publication: its exact digit
// count N (1 for zero) is known and nothing is allocated yet.
type intDivResult struct {
	emit       intDivEmit
	limbs      []uint32 // intDivEmitLimbs; the split's high part
	n          uint64
	zero       bool
	negative   bool
	shift      uint64 // intDivEmitShifted: k; intDivEmitSplit: j
	complement bool   // intDivEmitSplit: the low part is 10^j − L
}

// publish writes the coefficient once into its single result buffer and
// publishes it at exponent t. A zero is unsigned. The shifted and split
// emitters read the operand here, after the final caps.
func (r *intDivResult) publish(d Decimal, x *coefficientView, t int32, c *quoRemCount) Decimal {
	if r.zero {
		return zeroDecimal(t)
	}
	switch r.emit {
	case intDivEmitOperand:
		return d // the dividend's own coefficient at t = ex (values are immutable)
	case intDivEmitLimbs:
		c.output().add(uint64(len(r.limbs)))
		return publishScratch(r.limbs, t, r.negative)
	}
	count := digitLimbs(r.n)
	if count <= slowSmallLimbs {
		var small [slowSmallLimbs]uint32
		r.fill(small[:count], x, c)
		return publishScratch(small[:count], t, r.negative)
	}
	out := make([]uint32, count)
	r.fill(out, x, c)
	return publishOwned(out, t, r.negative)
}

// fill writes a shifted or split coefficient into out, t(N) zeroed limbs.
func (r *intDivResult) fill(out []uint32, x *coefficientView, c *quoRemCount) {
	if r.emit == intDivEmitShifted {
		for i := range out {
			out[i] = shiftedLimb(x, r.shift, i)
		}
		dx, _ := arithmeticDigits(x)
		c.pathCounter().add(dx) // the dividend's digit reads
		c.output().add(uint64(len(out)))
	} else {
		emitSplit(out, x, r.shift, r.limbs, r.complement, c)
	}
	c.output().add(uint64(len(out))) // publication
}

// shiftedLimb is limb i of C·10^shift.
func shiftedLimb(v *coefficientView, shift uint64, i int) uint32 {
	whole, part := shift/9, shift%9
	if uint64(i) < whole {
		return 0
	}
	j := uint64(i) - whole
	var r uint64
	if j < uint64(v.count) {
		r = uint64(v.limb(int(j))) * uint64(decimalPowers[part]) % decimalLimbBase
	}
	if part != 0 && j >= 1 && j-1 < uint64(v.count) {
		r += uint64(v.limb(int(j-1))) / uint64(decimalPowers[9-part])
	}
	return uint32(r)
}

// qZeroResult is q = 0 without a comparison: Quo zero, and Rem (and
// RemNear with δ ≤ −2, where 2|x| < |y|) the dividend at min(ex, ey).
func qZeroResult(op intDivOp, s intDivShape, negative bool) intDivResult {
	if op == intDivQuo {
		return intDivResult{n: 1, zero: true}
	}
	k := s.k()
	if k <= 0 {
		return intDivResult{emit: intDivEmitOperand, n: s.dx, negative: negative}
	}
	return intDivResult{emit: intDivEmitShifted, n: s.dx + uint64(k), negative: negative, shift: uint64(k)}
}

// qZeroNearResult is RemNear with q = 0 and δ ≥ −1: D = |y| − |x| at
// min(ex, ey) is formed in the arena, and n = ±1 iff |x| > D, when the
// result is D with the sign opposite to x's. The tie 2|x| = |y|
// keeps the even n = 0.
func qZeroNearResult(arena []uint32, x, y *coefficientView, s intDivShape, negative bool, c *divCount) intDivResult {
	k := s.k()
	var sx, sy uint64
	if k >= 0 {
		sx = uint64(k)
	} else {
		sy = uint64(-k)
	}
	var borrow uint64
	for i := range arena {
		a, b := uint64(shiftedLimb(x, sx, i)), uint64(shiftedLimb(y, sy, i))
		v := b + decimalLimbBase - a - borrow
		borrow = 1 - v/decimalLimbBase
		arena[i] = uint32(v % decimalLimbBase)
	}
	c.add(3 * uint64(len(arena)))
	cmp := 0
	for i := len(arena) - 1; i >= 0 && cmp == 0; i-- {
		a := shiftedLimb(x, sx, i)
		c.add(2)
		switch {
		case a > arena[i]:
			cmp = 1
		case a < arena[i]:
			cmp = -1
		}
	}
	if cmp > 0 {
		dl := trimLimbs(arena)
		return intDivResult{limbs: dl, n: limbsDigits(dl), negative: !negative}
	}
	return qZeroResult(intDivRem, s, negative)
}

// kernelResult runs the division kernel at division exponent 0:
// Quo publishes R; the split divides the high part and reads the low part
// in place; the stream divides Cx·10^k. The extra n+1 arena limbs hold
// twice the remainder and Cy minus it.
func kernelResult(arena []uint32, op intDivOp, x, y *coefficientView, s intDivShape, xNeg, yNeg bool, c *divCount) intDivResult {
	src := divSource{x: *x, y: *y, dx: s.dx, dy: s.dy, ideal: s.k()}
	p := src.plan(0)
	nl, dl, ql := src.divScratch(p)
	num, den, quot, extra := arena[:nl], arena[nl:nl+dl], arena[nl+dl:nl+dl+ql], arena[nl+dl+ql:]
	un := src.buildNumerator(p, num, c)
	vn := y.count
	for i := range vn {
		den[i] = y.limb(i)
	}
	c.add(s.dy)
	q, _ := divideLimbs(num[:max(un, vn)+1], un, den[:vn], quot, c)
	if op == intDivQuo {
		return intDivResult{limbs: q, n: limbsDigits(q), negative: xNeg != yNeg}
	}
	odd := len(q) > 0 && q[0]&1 == 1
	rem := trimLimbs(num[:vn])
	if p.k >= 0 {
		// Stream: r at exponent ey.
		if op == intDivRemNear && nearUp(rem, y, extra, odd, 0, c) {
			up := subtractFromCoefficient(y, rem, extra, c)
			return intDivResult{limbs: up, n: limbsDigits(up), negative: !xNeg}
		}
		return remainderLimbs(rem, xNeg)
	}
	return splitResult(op, x, y, uint64(-p.k), rem, extra, odd, xNeg, c)
}

func remainderLimbs(r []uint32, negative bool) intDivResult {
	r = trimLimbs(r)
	if len(r) == 0 {
		return intDivResult{n: 1, zero: true}
	}
	return intDivResult{limbs: r, n: limbsDigits(r), negative: negative}
}

// nearUp decides whether nearest-even n is one step further from zero than
// q from D = Cy − 2·rem and, for the split, the low part's sign relative to
// half of 10^j (the division half classes): D < 0 up; D = 0 up iff L ≠ 0
// or q is odd; D = 1 up iff 2L > 10^j, or q is odd at 2L = 10^j; D ≥ 2
// stays. low is 0 when there is no low part (L = 0), otherwise
// splitLowClass(L).
func nearUp(rem []uint32, y *coefficientView, x2 []uint32, odd bool, low lowClass, c *divCount) bool {
	vn := y.count
	var carry uint64
	for i := range vn {
		var v uint64
		if i < len(rem) {
			v = uint64(rem[i])
		}
		v = v*2 + carry
		x2[i] = uint32(v % decimalLimbBase)
		carry = v / decimalLimbBase
	}
	x2[vn] = uint32(carry)
	c.add(uint64(2*vn + 2))
	switch compareLimbs(x2[:vn+1], y) {
	case 1:
		return true
	case 0:
		return low.nonzero() || odd
	}
	if !incrementCompareEqual(x2[:vn+1], vn, y) {
		return false
	}
	c.add(uint64(vn + 1))
	switch low.sign() {
	case 1:
		return true
	case 0:
		return odd
	}
	return false
}

// lowClass is the split's low part L against half of 10^j: bit 2 marks
// L ≠ 0, and the low two bits hold sign(2L − 10^j) + 1.
type lowClass uint8

func (l lowClass) nonzero() bool { return l&4 != 0 }
func (l lowClass) sign() int     { return int(l&3) - 1 }

// splitLowClass reads L = Cx mod 10^j in place: its top digit and whether
// any lower digit is nonzero.
func splitLowClass(x *coefficientView, j uint64, c *divCount) lowClass {
	top, sticky, _ := quantizeDiscard(x, j)
	c.add(j)
	var l lowClass
	if top != 0 || sticky {
		l = 4
	}
	switch {
	case top > 5 || top == 5 && sticky:
		return l | 2
	case top == 5:
		return l | 1
	}
	return l
}

// subtractFromCoefficient writes Cy − r (Cy > r) into dst and returns it
// trimmed.
func subtractFromCoefficient(y *coefficientView, r, dst []uint32, c *divCount) []uint32 {
	var borrow uint64
	for i := range y.count {
		var ri uint64
		if i < len(r) {
			ri = uint64(r[i])
		}
		v := uint64(y.limb(i)) + decimalLimbBase - ri - borrow
		borrow = 1 - v/decimalLimbBase
		dst[i] = uint32(v % decimalLimbBase)
	}
	c.add(uint64(y.count))
	return trimLimbs(dst[:y.count])
}

// splitResult is the split path's result: Rem is Hrem·10^j + L at exponent ex;
// RemNear's up is (Cy − Hrem)·10^j when L = 0 and
// (Cy − Hrem − 1)·10^j + (10^j − L) otherwise, with the sign opposite to x's. The exact N comes from a
// read-only length pass; nothing is written until publication.
func splitResult(op intDivOp, x, y *coefficientView, j uint64, hrem, extra []uint32, odd, xNeg bool, c *divCount) intDivResult {
	var low lowClass
	up := false
	if op == intDivRemNear {
		low = splitLowClass(x, j, c)
		up = nearUp(hrem, y, extra, odd, low, c)
	}
	high := hrem
	complement := false
	if up {
		high = subtractFromCoefficient(y, hrem, extra, c)
		if low.nonzero() {
			complement = true
			for i := range high {
				if high[i] > 0 {
					high[i]--
					break
				}
				high[i] = uint32(decimalLimbBase - 1)
			}
			c.add(uint64(len(high)))
			high = trimLimbs(high)
		}
	}
	high = trimLimbs(high)
	var n uint64
	switch {
	case len(high) > 0:
		n = j + limbsDigits(high)
	case complement:
		n = complementDigits(x, j, c)
	default:
		n = lowDigits(x, j, c)
		if n == 0 {
			return intDivResult{n: 1, zero: true}
		}
	}
	return intDivResult{emit: intDivEmitSplit, limbs: high, n: n, negative: xNeg != up, shift: j, complement: complement}
}

// lowLimb is limb i of L = Cx mod 10^j (i < t(j)); lowBase is that limb's
// radix, 10^9 or 10^w for the partial top limb of w digits.
func lowLimb(x *coefficientView, j uint64, i uint64) uint32 {
	limb := x.limb(int(i))
	if i == j/9 {
		return limb % decimalPowers[j%9] // j%9 != 0 here: i < t(j)
	}
	return limb
}

// lowWidth is the digit width of L's limb i: 9, or j%9 for a partial top.
func lowWidth(j, i uint64) uint64 {
	if i == j/9 {
		return j % 9
	}
	return 9
}

func lowBase(j, i uint64) uint64 {
	if i == j/9 {
		return uint64(decimalPowers[j%9])
	}
	return decimalLimbBase
}

// lowDigits is the digit count of L, 0 when L = 0: its top nonzero limb.
func lowDigits(x *coefficientView, j uint64, c *divCount) uint64 {
	for i := digitLimbs(j); i > 0; i-- {
		c.add(lowWidth(j, i-1))
		if v := lowLimb(x, j, i-1); v != 0 {
			return 9*(i-1) + uint64(limbDigits(v))
		}
	}
	return 0
}

// complementDigits is the digit count of 10^j − L for L ≠ 0:
// past L's top run of all-nines limbs, the first other limb i holds the
// top, base_i − 1 − L_i, unless every limb below it is zero, when the +1
// reaches it and the top is base_i − L_i. For L_i = 0 that is a full
// limb's 10^9, whose ten digits are the 1 left in the lowest nines limb.
func complementDigits(x *coefficientView, j uint64, c *divCount) uint64 {
	lj := digitLimbs(j)
	i := lj
	for i > 0 {
		c.add(lowWidth(j, i-1))
		if uint64(lowLimb(x, j, i-1)) != lowBase(j, i-1)-1 {
			break
		}
		i--
	}
	if i == 0 {
		return 1 // L = 10^j − 1
	}
	i-- // the first limb that is not all nines
	li := uint64(lowLimb(x, j, i))
	below := false
	for m := i; m > 0 && !below; m-- {
		c.add(lowWidth(j, m-1))
		below = lowLimb(x, j, m-1) != 0
	}
	if below {
		return 9*i + uint64(limbDigits(uint32(lowBase(j, i)-1-li)))
	}
	return 9*i + uint64(limbDigits(uint32(lowBase(j, i)-li)))
}

// emitSplit writes high·10^j + L, or high·10^j + (10^j − L), into out,
// which holds exactly t(N) zeroed limbs: at most min(t(j), t(N)) low
// writes and the high part's shifted limbs.
func emitSplit(out []uint32, x *coefficientView, j uint64, high []uint32, complement bool, c *quoRemCount) {
	nl := min(digitLimbs(j), uint64(len(out)))
	carry := uint64(1)
	for i := range nl {
		v := uint64(lowLimb(x, j, i))
		if complement {
			base := lowBase(j, i)
			v = base - 1 - v + carry
			carry = 0
			if v == base {
				v, carry = 0, 1
			}
		}
		out[i] = uint32(v)
		c.pathCounter().add(lowWidth(j, i))
	}
	c.output().add(nl)
	whole, part := j/9, j%9
	factor := uint64(decimalPowers[part])
	for i, h := range high {
		v := uint64(h) * factor
		out[whole+uint64(i)] += uint32(v % decimalLimbBase)
		c.output().add(1)
		if hi := v / decimalLimbBase; hi != 0 {
			out[whole+uint64(i)+1] += uint32(hi)
			c.output().add(1)
		}
	}
}

// modularResult is the modular remainder: z = Cx·10^k mod 2Cy by a
// Horner reduction of Cx and left-to-right square-and-multiply over the
// bits of k, every product reduced by divideLimbs; then r = z mod Cy and q
// is odd iff z ≥ Cy. The arena is 7n′+4 limbs: the modulus, the Horner
// accumulator and the power (n′ each), the product (2n′+1), the quotient
// (n′+2) and the doubling slot (n′+1).
func modularResult(arena []uint32, op intDivOp, x, y *coefficientView, s intDivShape, xNeg bool, c *divCount) intDivResult {
	np := int(digitLimbs(s.dy + 1))
	ms, acc, pw := arena[:np], arena[np:2*np], arena[2*np:3*np]
	tt := arena[3*np : 5*np+1]
	qs := arena[5*np+1 : 6*np+3]
	x2 := arena[6*np+3 : 7*np+4]
	// M = 2·Cy.
	var carry uint64
	for i := range y.count {
		w := uint64(y.limb(i))*2 + carry
		ms[i] = uint32(w % decimalLimbBase)
		carry = w / decimalLimbBase
	}
	mn := y.count
	if carry != 0 {
		ms[mn] = uint32(carry)
		mn++
	}
	c.add(uint64(y.count))
	m := ms[:mn]
	reduce := func(un int, dst []uint32) {
		for un > 0 && tt[un-1] == 0 {
			un--
			c.add(1)
		}
		if un >= mn {
			divideLimbs(tt[:un+1], un, m, qs, c)
		}
		copy(dst[:mn], tt[:mn])
		clear(dst[mn:])
		c.add(uint64(mn))
	}
	for i := x.count - 1; i >= 0; i-- {
		clear(tt)
		copy(tt[1:], acc[:mn])
		tt[0] = x.limb(i)
		c.add(uint64(mn) + 1)
		reduce(mn+1, acc)
	}
	mulMod := func(u, v, dst []uint32) {
		clear(tt)
		c.add(uint64(2 * mn))
		for i := range mn {
			var cr uint64
			for jj := range mn {
				w := uint64(u[i])*uint64(v[jj]) + uint64(tt[i+jj]) + cr
				tt[i+jj] = uint32(w % decimalLimbBase)
				cr = w / decimalLimbBase
			}
			tt[i+mn] = uint32(cr)
			c.add(uint64(mn))
		}
		reduce(2*mn, dst)
	}
	clear(pw)
	pw[0] = 1
	c.add(uint64(mn))
	k := uint64(s.k())
	for bit := bits.Len64(k) - 1; bit >= 0; bit-- {
		mulMod(pw, pw, pw)
		if k>>uint(bit)&1 == 1 {
			clear(tt)
			var cr uint64
			for i := range mn {
				w := uint64(pw[i])*10 + cr
				tt[i] = uint32(w % decimalLimbBase)
				cr = w / decimalLimbBase
			}
			tt[mn] = uint32(cr)
			c.add(uint64(mn) + 1)
			reduce(mn+1, pw)
		}
	}
	mulMod(acc, pw, acc) // z
	z := trimLimbs(acc[:mn])
	odd := compareLimbs(z, y) >= 0
	c.add(uint64(mn))
	r := z
	if odd {
		// r = z − Cy, in place.
		var borrow uint64
		for i := range z {
			var yi uint64
			if i < y.count {
				yi = uint64(y.limb(i))
			}
			v := uint64(z[i]) + decimalLimbBase - yi - borrow
			borrow = 1 - v/decimalLimbBase
			z[i] = uint32(v % decimalLimbBase)
		}
		c.add(uint64(len(z)))
		r = trimLimbs(z)
	}
	if op == intDivRemNear && nearUp(r, y, x2, odd, 0, c) {
		up := subtractFromCoefficient(y, r, pw, c)
		return intDivResult{limbs: up, n: limbsDigits(up), negative: !xNeg}
	}
	return remainderLimbs(r, xNeg)
}

// intDivStoredRange reports whether the stored exponent t fits the guards.
func intDivStoredRange(t int64, ctx Context) bool {
	if !ctx.guarded {
		return true
	}
	etiny := int64(ctx.guards.Emin) - (int64(ctx.precision) - 1)
	return t >= etiny && t <= int64(ctx.guards.Emax)
}
