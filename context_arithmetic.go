// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"math"
	"math/bits"
)

// AddWithContext applies an explicit arithmetic context to addition.
func (d Decimal) AddWithContext(other Decimal, ctx Context) (Decimal, Conditions, error) {
	return d.contextAddSub(other, ctx, "AddWithContext", false, true, nil)
}

// SubWithContext applies an explicit arithmetic context to subtraction.
func (d Decimal) SubWithContext(other Decimal, ctx Context) (Decimal, Conditions, error) {
	return d.contextAddSub(other, ctx, "SubWithContext", true, true, nil)
}

// MulWithContext applies an explicit arithmetic context to multiplication.
func (d Decimal) MulWithContext(other Decimal, ctx Context) (Decimal, Conditions, error) {
	return d.contextMul(other, ctx, ctx.arith, "MulWithContext")
}

// contextAddSub is the context Add/Sub kernel. Public entry points pass
// reduce=true: at p > 0 the operands are first reduced by
// contextReduceShapes, budgeted or not, and every charge and stream then
// works on the reduced operands. reduce=false keeps the unreduced logical
// plan over the full aligned span; only tests take it, as the general
// reference path the reduction is pinned against. A non-nil charge receives
// the base charge B of the p > 0 plan, budgeted or not, so tests can pin the
// work of unbudgeted calls without timing them; public entry points pass nil.
func (d Decimal) contextAddSub(other Decimal, ctx Context, op string, subtract, reduce bool, charge *uint64) (Decimal, Conditions, error) {
	budget := ctx.arith
	if ctx.precision == 0 {
		result, err := d.addSub(other, budget, op, subtract)
		return result, 0, err
	}
	if budget.admits(inlineResultDigits, inlineContextAddSubWork) && d.slow == nil && other.slow == nil {
		if exact, ok := inlineAddSub(d, other, subtract); ok {
			if contextExactFits(exact, ctx) {
				return exact, 0, nil
			}
			if rounded, events, ok := contextRoundInline(exact, ctx); ok {
				return contextOutcome(rounded, events, ctx.traps, op)
			}
		} else if sum, exponent, negative, ok := wideAddSub(d, other, subtract); ok {
			if rounded, events, ok := contextRoundWide(sum, exponent, negative, ctx); ok {
				return contextOutcome(rounded, events, ctx.traps, op)
			}
		}
	}
	return d.contextAddSubGeneral(other, ctx, op, subtract, reduce, charge)
}

// contextAddSubInline is the inline part of contextAddSub at p > 0 without
// its budget gate, for a caller that has admitted the call by its own
// bound: the exact inline sum when it already fits the context, or that sum
// or the 256-bit sum rounded once. served is false when neither applies;
// nothing is charged or refused here, and the caller then takes its
// general path.
func (d Decimal) contextAddSubInline(other Decimal, ctx Context, op string, subtract bool) (result Decimal, events Conditions, served bool, err error) {
	if d.slow != nil || other.slow != nil {
		return Decimal{}, 0, false, nil
	}
	if exact, ok := inlineAddSub(d, other, subtract); ok {
		if contextExactFits(exact, ctx) {
			return exact, 0, true, nil
		}
		if rounded, events, ok := contextRoundInline(exact, ctx); ok {
			result, events, err = contextOutcome(rounded, events, ctx.traps, op)
			return result, events, true, err
		}
	} else if sum, exponent, negative, ok := wideAddSub(d, other, subtract); ok {
		if rounded, events, ok := contextRoundWide(sum, exponent, negative, ctx); ok {
			result, events, err = contextOutcome(rounded, events, ctx.traps, op)
			return result, events, true, err
		}
	}
	return Decimal{}, 0, false, nil
}

// contextAddSubGeneral is the planned, charged stream path of contextAddSub
// at p > 0; it owns every budget charge and refusal.
func (d Decimal) contextAddSubGeneral(other Decimal, ctx Context, op string, subtract, reduce bool, charge *uint64) (Decimal, Conditions, error) {
	budget := ctx.arith
	p := contextPlan{a: coefficientViewOf(d), b: coefficientViewOf(other), ideal: int64(min(d.exponent(), other.exponent())), greaterA: true}
	aZero, bZero := p.a.count == 0, p.b.count == 0
	if aZero && bZero {
		p.zero, p.base = true, 1
		if !admitted(budget.MaxWork, 1, true) {
			return contextFailure(op, ErrInsufficientStorage)
		}
		if charge != nil {
			*charge = p.base
		}
		return contextRun(p, ctx, budget, op)
	}
	da, validA := arithmeticDigits(&p.a)
	db, validB := arithmeticDigits(&p.b)
	if !validA || !validB {
		return contextFailure(op, ErrInsufficientStorage)
	}
	if reduce && contextMayReduce(nonzeroDigits(da, aZero), d.exponent(), nonzeroDigits(db, bZero), other.exponent(), int64(ctx.precision), contextFloor(ctx)) {
		d, other = contextReduceKernel(d, other, &p.a, &p.b, &da, &db, aZero, bZero, ctx)
		p.ideal = int64(min(d.exponent(), other.exponent()))
	}
	e := int32(p.ideal)
	p.sa = uint64(int64(d.exponent()) - int64(e))
	p.sb = uint64(int64(other.exponent()) - int64(e))
	var spanA, spanB uint64
	var valid bool
	if !aZero {
		spanA, valid = arithmeticAdd(da, p.sa)
		if !valid {
			return contextFailure(op, ErrInsufficientStorage)
		}
	}
	if !bZero {
		spanB, valid = arithmeticAdd(db, p.sb)
		if !valid {
			return contextFailure(op, ErrInsufficientStorage)
		}
	}
	length := max(spanA, spanB)
	bSign := other.negative()
	if subtract && !bZero {
		bSign = !bSign
	}
	p.add = d.negative() == bSign
	p.negative = d.negative()
	if aZero != bZero {
		p.add = true
		if aZero {
			p.negative = bSign
		}
		p.base = length
		if !admitted(budget.MaxWork, p.base, true) {
			return contextFailure(op, ErrInsufficientStorage)
		}
		p.groups = digitLimbs(length)
		if charge != nil {
			*charge = p.base
		}
		return contextRun(p, ctx, budget, op)
	}
	inputs, valid := arithmeticAdd(da, db)
	if !p.add {
		if !admitted(budget.MaxWork, inputs, valid) {
			return contextFailure(op, ErrInsufficientStorage)
		}
		cmp := compareMagnitude(&p.a, int64(d.exponent()), &p.b, int64(other.exponent()))
		if cmp == 0 {
			p.zero, p.base = true, inputs
			if charge != nil {
				*charge = p.base
			}
			return contextRun(p, ctx, budget, op)
		}
		p.greaterA = cmp > 0
		if cmp < 0 {
			p.negative = bSign
		}
		twice, ok1 := arithmeticMul(inputs, 2)
		p.base, valid = arithmeticAdd(twice, length)
		valid = valid && ok1
		p.groups = digitLimbs(length)
	} else {
		planned, ok1 := arithmeticAdd(length, 1)
		if !ok1 {
			return contextFailure(op, ErrInsufficientStorage)
		}
		p.base, valid = arithmeticAdd(inputs, planned)
		p.groups = digitLimbs(planned)
	}
	if !admitted(budget.MaxWork, p.base, valid) {
		return contextFailure(op, ErrInsufficientStorage)
	}
	if charge != nil {
		*charge = p.base
	}
	return contextRun(p, ctx, budget, op)
}

// contextAddSubPlan is contextAddSub's plan in term form, for FMA's
// unpublished product: the stream plan, and for opposite signs the full
// charge B that applies once the comparison finds the magnitudes unequal. Its
// admission follows the kernel's paths and charges exactly
// (TestFMAReductionMatchesUnreduced pins the two). The Decimal kernel keeps
// its inline form, which keeps term construction off its exact-fit path.
type contextAddSubPlan struct {
	contextPlan
	opposite  bool
	full      uint64
	fullValid bool
}

// admit plans a context Add/Sub at p > 0 and makes every refusal the
// operand shapes decide, before either coefficient is read. Every charge
// adds pre, the work the caller has already admitted (FMA's Mul charge).
// Only the opposite-sign comparison remains for finish, so FMA can build
// its product between the stages.
func (p *contextAddSubPlan) admit(a, b *addTerm, budget limits, pre uint64, op string) error {
	p.ideal, p.greaterA = min(a.exponent, b.exponent), true
	if a.zero && b.zero {
		var valid bool
		p.zero = true
		p.base, valid = arithmeticAdd(pre, 1)
		if !admitted(budget.MaxWork, p.base, valid) {
			return newError(op, ErrInsufficientStorage)
		}
		return nil
	}
	p.sa = uint64(a.exponent - p.ideal)
	p.sb = uint64(b.exponent - p.ideal)
	var spanA, spanB uint64
	var valid bool
	if !a.zero {
		if spanA, valid = arithmeticAdd(a.digits, p.sa); !valid {
			return newError(op, ErrInsufficientStorage)
		}
	}
	if !b.zero {
		if spanB, valid = arithmeticAdd(b.digits, p.sb); !valid {
			return newError(op, ErrInsufficientStorage)
		}
	}
	length := max(spanA, spanB)
	p.add = a.negative == b.negative
	p.negative = a.negative
	if a.zero != b.zero {
		p.add = true
		if a.zero {
			p.negative = b.negative
		}
		p.base, valid = arithmeticAdd(pre, length)
		if !admitted(budget.MaxWork, p.base, valid) {
			return newError(op, ErrInsufficientStorage)
		}
		p.groups = digitLimbs(length)
		return nil
	}
	inputs, valid1 := arithmeticAdd(a.digits, b.digits)
	if !p.add {
		// The comparison precharge; an equal magnitude publishes zero
		// with this base, and an unequal one charges the full B.
		p.opposite = true
		var valid2 bool
		p.base, valid2 = arithmeticAdd(pre, inputs)
		if !admitted(budget.MaxWork, p.base, valid1 && valid2) {
			return newError(op, ErrInsufficientStorage)
		}
		twice, valid3 := arithmeticMul(inputs, 2)
		charge, valid4 := arithmeticAdd(twice, length)
		p.full, valid = arithmeticAdd(pre, charge)
		p.fullValid = valid && valid1 && valid3 && valid4
		p.groups = digitLimbs(length)
		return nil
	}
	planned, valid2 := arithmeticAdd(length, 1)
	if !valid2 {
		return newError(op, ErrInsufficientStorage)
	}
	charge, valid3 := arithmeticAdd(inputs, planned)
	p.base, valid = arithmeticAdd(pre, charge)
	p.groups = digitLimbs(planned)
	if !admitted(budget.MaxWork, p.base, valid && valid1 && valid3) {
		return newError(op, ErrInsufficientStorage)
	}
	return nil
}

// finish runs an admitted plan over the terms' coefficients: the
// opposite-sign comparison and its full charge, then the finisher. The
// views are copied into a local stream plan, so a caller's stack scratch
// never escapes through the plan pointer.
func (p *contextAddSubPlan) finish(a, b *addTerm, ctx Context, budget limits, op string) (Decimal, Conditions, error) {
	plan := p.contextPlan
	plan.a, plan.b = a.v, b.v
	if p.opposite {
		cmp := compareMagnitude(&a.v, a.exponent, &b.v, b.exponent)
		if cmp == 0 {
			plan.zero = true
			return contextRun(plan, ctx, budget, op)
		}
		plan.greaterA = cmp > 0
		if cmp < 0 {
			plan.negative = b.negative
		}
		plan.base = p.full
		if !admitted(budget.MaxWork, plan.base, p.fullValid) {
			return contextFailure(op, ErrInsufficientStorage)
		}
	}
	return contextRun(plan, ctx, budget, op)
}

// contextReduceKernel applies contextReduceShapes to the kernel's operands,
// returning values while updating views and digit counts in place: a reduced
// operand is 1·10^P or a zero, one digit either way. It stays out of line so
// the kernel, which also holds the exact-fit shortcut, keeps its frame.
//
//go:noinline
func contextReduceKernel(x, y Decimal, a, b *coefficientView, da, db *uint64, aZero, bZero bool, ctx Context) (Decimal, Decimal) {
	sx := Shape{Digits: nonzeroDigits(*da, aZero), Exponent: x.exponent(), Negative: x.negative()}
	sy := Shape{Digits: nonzeroDigits(*db, bZero), Exponent: y.exponent(), Negative: y.negative()}
	rx, ry := contextReduceShapes(sx, sy, ctx)
	if rx != sx {
		x = reducedOperand(x, sx, rx)
		*a, *da = coefficientViewOf(x), 1
	}
	if ry != sy {
		y = reducedOperand(y, sy, ry)
		*b, *db = coefficientViewOf(y), 1
	}
	return x, y
}

// contextMayReduce is a necessary condition for contextReduceShapes to change
// either shape, from the digit counts the kernel has already computed (0 for
// zero), the exponents, the precision p and the floor etiny (contextFloor),
// in a few integer comparisons; it is small enough to inline into the kernel.
// The planner then runs only where a reduction is possible:
//
//   - one zero: exactly when the clamp moves it, below both e_nz and pos−1,
//     pos = e_nz+d_nz−p, raised to Etiny under guards;
//   - two nonzero operands: the sticky substitution replaces only the
//     operand lo with the lower exponent, and only when the exponent gap is
//     at least d_lo+1 and at least d_lo−d_hi+p+3;
//   - a zero at or above the other operand's exponent, two zeros, or equal
//     exponents: never.
func contextMayReduce(dx uint64, ex int32, dy uint64, ey int32, p, etiny int64) bool {
	if ey > ex {
		dx, ex, dy, ey = dy, ey, dx, ex
	}
	gap := int64(ex) - int64(ey)
	if gap == 0 || dx == 0 {
		return false
	}
	if dy != 0 {
		return gap > int64(dy) && gap >= int64(dy)-int64(dx)+p+3
	}
	return int64(ey) < max(int64(ex)+int64(dx)-p, etiny)-1
}

// contextFloor is Etiny under guards, and otherwise below every position.
func contextFloor(ctx Context) int64 {
	if ctx.guarded {
		return int64(ctx.guards.Emin) - int64(ctx.precision) + 1
	}
	return math.MinInt64
}

// nonzeroDigits is digits, or 0 for a zero coefficient.
func nonzeroDigits(digits uint64, zero bool) uint64 {
	if zero {
		return 0
	}
	return digits
}

// contextReduceShapes is the shape planner for context Add/Sub at p > 0. It
// maps operand shapes to reduced shapes that round identically in every mode,
// with and without guards and traps (same result, exponent, Conditions,
// direction and error), so that charges and streams depend on the precision
// and the operands' digits, not on their exponent gap:
//
//   - (a) Both nonzero: an operand lying entirely below
//     P = min(e_large, adj_large−p−1)−1 is replaced by the single digit 1
//     at exponent P, keeping its sign (the sticky substitution;
//     stickyRemoteShape).
//   - (b) Exactly one zero: its exponent is clamped to
//     e_zero' = max(e_zero, min(e_nz, pos−1)), where pos is the lowest kept
//     digit position adj_nz−p+1, raised to Etiny under guards
//     (clampZeroShape).
//   - (c) Otherwise (both zero) the shapes are unchanged; a zero at or
//     above the nonzero's exponent is unchanged by the clamp.
//
// The reduction never raises the aligned span or a digit count, so the
// reduced base charge B never exceeds the unreduced one.
func contextReduceShapes(x, y Shape, ctx Context) (Shape, Shape) {
	switch xZero, yZero := x.Digits == 0, y.Digits == 0; {
	case xZero && yZero:
		return x, y
	case xZero:
		x.Exponent = clampZeroShape(x.Exponent, y, ctx)
		return x, y
	case yZero:
		y.Exponent = clampZeroShape(y.Exponent, x, ctx)
		return x, y
	}
	return stickyRemoteShape(x, y, ctx.precision)
}

// stickyRemoteShape replaces a nonzero shape lying entirely below the
// rounding position of a finite-precision sum of two nonzero shapes with the
// single digit 1 (same sign) just below that position. Both operands then
// round identically in every mode: the result's top digit, rounding position
// and final exponent (at most one lower after a borrow, or Etiny) are
// unchanged, the substitute stays strictly below the guard digit, and the
// discarded tail remains nonzero. The exact sum would need work proportional
// to the exponent gap; the substitute needs O(precision), and budgeted calls
// charge the substitute's span.
func stickyRemoteShape(x, y Shape, precision uint32) (Shape, Shape) {
	adjustedX := int64(x.Exponent) + int64(x.Digits) - 1
	adjustedY := int64(y.Exponent) + int64(y.Digits) - 1
	swapped := adjustedY > adjustedX
	large, small, adjustedLarge, adjustedSmall := x, y, adjustedX, adjustedY
	if swapped {
		large, small, adjustedLarge, adjustedSmall = y, x, adjustedY, adjustedX
	}
	// Below the large operand's last digit and two places below the lowest
	// possible final rounding position (adjusted-precision after a borrow).
	position := min(int64(large.Exponent), adjustedLarge-int64(precision)-1) - 1
	if adjustedSmall >= position || position < math.MinInt32 {
		return x, y
	}
	small = Shape{Digits: 1, Exponent: int32(position), Negative: small.Negative}
	if swapped {
		return small, large
	}
	return large, small
}

// clampZeroShape returns the reduced exponent of a zero added to the nonzero
// shape nz: max(e_zero, min(e_nz, pos−1)). A zero at or above pos−1 keeps its
// exponent, including every case whose exact result is published unrounded at
// e_zero. Below it the padded zeros are discarded wherever they start: the
// clamp keeps a zero-only discard below pos, so Rounded, the cut, Subnormal
// and the final exponent are unchanged, and when e_nz < pos the nonzero's own
// digits force the same rounding.
func clampZeroShape(zero int32, nz Shape, ctx Context) int32 {
	position := int64(nz.Exponent) + int64(nz.Digits) - int64(ctx.precision)
	if ctx.guarded {
		position = max(position, int64(ctx.guards.Emin)-int64(ctx.precision)+1)
	}
	return int32(max(int64(zero), min(int64(nz.Exponent), position-1)))
}

// reduceSpan is an operand for the context planner with an int64 exponent and
// a digit bracket lo ≤ digits ≤ hi: lo = hi for a Decimal, while FMA's
// product, reduced before it is built, has dx+dy−1 or dx+dy digits. A zero
// has lo = hi = 0.
type reduceSpan struct {
	lo, hi   uint64
	exponent int64
	negative bool
}

func spanOf(s Shape) reduceSpan {
	return reduceSpan{lo: s.Digits, hi: s.Digits, exponent: int64(s.Exponent), negative: s.Negative}
}

// contextReduceSpans is contextReduceShapes over spans, for FMA's product
// and addend; Add and Sub keep the Shape planner, and
// TestReduceSpansMatchShapes pins the two with lo = hi. A bracket is read
// on its safe side: a zero is clamped against the nonzero's lowest
// possible rounding position, and the sticky rule takes the large operand's
// least and the small operand's greatest adjusted exponent, so every
// reduction it makes is one the exact digit counts also permit.
func contextReduceSpans(x, y reduceSpan, ctx Context) (reduceSpan, reduceSpan) {
	switch xZero, yZero := x.hi == 0, y.hi == 0; {
	case xZero && yZero:
		return x, y
	case xZero:
		x.exponent = clampZeroSpan(x.exponent, y, ctx)
		return x, y
	case yZero:
		y.exponent = clampZeroSpan(y.exponent, x, ctx)
		return x, y
	}
	return stickyRemoteSpan(x, y, ctx.precision)
}

// stickyRemoteSpan is stickyRemoteShape over spans: it replaces a nonzero
// span lying entirely below the rounding position of a finite-precision sum
// of two nonzero spans with the single digit 1 (same sign) just below that
// position. Both operands then round identically in every mode: the result's
// top digit, rounding position and final exponent (at most one lower after a
// borrow, or Etiny) are unchanged, the substitute stays strictly below the
// guard digit, and the discarded tail remains nonzero. The exact sum would
// need work proportional to the exponent gap; the substitute needs
// O(precision), and budgeted calls charge the substitute's span. For int32
// inputs the substitute's exponent P fits: P ≤ e_large−1, and an operand is
// substituted only when it lies below P, so P > MinInt32.
func stickyRemoteSpan(x, y reduceSpan, precision uint32) (reduceSpan, reduceSpan) {
	xLo, xHi := x.exponent+int64(x.lo)-1, x.exponent+int64(x.hi)-1
	yLo, yHi := y.exponent+int64(y.lo)-1, y.exponent+int64(y.hi)-1
	large, small := &x, &y
	largeLo, smallHi := xLo, yHi
	switch {
	case xLo > yHi:
	case yLo > xHi:
		large, small, largeLo, smallHi = &y, &x, yLo, xHi
	default:
		return x, y
	}
	// Below the large operand's last digit and two places below the lowest
	// possible final rounding position (adjusted-precision after a borrow).
	position := min(large.exponent, largeLo-int64(precision)-1) - 1
	if smallHi >= position {
		return x, y
	}
	*small = reduceSpan{lo: 1, hi: 1, exponent: position, negative: small.negative}
	return x, y
}

// clampZeroSpan is clampZeroShape over spans: the reduced exponent of a zero
// added to the nonzero span nz: max(e_zero, min(e_nz, pos−1)). A zero at or
// above pos−1 keeps its exponent, including every case whose exact result is
// published unrounded at e_zero. Below it the padded zeros are discarded
// wherever they start: the clamp keeps a zero-only discard below pos, so
// Rounded, the cut, Subnormal and the final exponent are unchanged, and when
// e_nz < pos the nonzero's own digits force the same rounding. pos uses nz's
// least digit count, the safe side of a bracket.
func clampZeroSpan(zero int64, nz reduceSpan, ctx Context) int64 {
	position := nz.exponent + int64(nz.lo) - int64(ctx.precision)
	if ctx.guarded {
		position = max(position, int64(ctx.guards.Emin)-int64(ctx.precision)+1)
	}
	return max(zero, min(nz.exponent, position-1))
}

// reduce applies a reduction of FMA's terms (contextReduceSpans) to t: an
// unchanged span keeps the term, a zero moves to the clamped exponent, and
// a remote term becomes 1·10^P at its sign.
func (t *addTerm) reduce(was, now reduceSpan) {
	switch {
	case now == was:
	case now.hi == 0:
		t.exponent = now.exponent
	default:
		*t = addTerm{v: coefficientView{inline: [5]uint32{1}, count: 1}, exponent: now.exponent, digits: 1, negative: now.negative}
	}
}

// reducedOperand is d reduced from shape was to shape now: unchanged, a
// zero at the clamped exponent, or 1·10^P at the reduced sign.
func reducedOperand(d Decimal, was, now Shape) Decimal {
	switch {
	case now == was:
		return d
	case now.Digits == 0:
		return zeroDecimal(now.Exponent)
	}
	return inlineDecimal(uint128{lo: 1}, now.Exponent, now.Negative)
}

// contextExactFits reports whether an exact inline result at its ideal
// exponent is already the context result with no condition: zero (which the
// context path returns unconditionally), or at most precision digits with
// an adjusted exponent inside any guards.
func contextExactFits(exact Decimal, ctx Context) bool {
	if exact.isZero() {
		return true
	}
	n := inlineDigits(exact.words)
	if n > uint64(ctx.precision) {
		return false
	}
	if !ctx.guarded {
		return true
	}
	adjusted := int64(exact.exponent()) + int64(n) - 1
	return adjusted >= int64(ctx.guards.Emin) && adjusted <= int64(ctx.guards.Emax)
}

// contextRoundInline rounds an exact inline result at its ideal exponent,
// longer than the precision, once to the precision: the context result
// whenever no guard intervenes. The inline quantize kernel drops the excess
// digits; a carry out of all nines keeps the precision and raises the
// exponent. ok is false, deferring to the general
// path, for the Exact mode's refusal, an exponent leaving int32, and under
// guards a tiny exact value or a result above Emax.
func contextRoundInline(exact Decimal, ctx Context) (rounded Decimal, events Conditions, ok bool) {
	n, p := inlineDigits(exact.words), uint64(ctx.precision)
	if n <= p {
		return Decimal{}, 0, false
	}
	cut := n - p
	target := int64(exact.exponent()) + int64(cut)
	if target > math.MaxInt32 || ctx.guarded && int64(exact.exponent())+int64(n)-1 < int64(ctx.guards.Emin) {
		return Decimal{}, 0, false
	}
	negative := exact.negative()
	var refused bool
	if rounded, events, refused, ok = inlineQuantize(exact, int32(target), ctx.rounding); !ok || refused {
		return Decimal{}, 0, false
	}
	if inlineCompare(rounded.words, pow10Wide[p]) == 0 {
		if target++; target > math.MaxInt32 {
			return Decimal{}, 0, false
		}
		rounded = inlineDecimal(pow10Wide[p-1], int32(target), negative)
	}
	if ctx.guarded && target+int64(p)-1 > int64(ctx.guards.Emax) {
		return Decimal{}, 0, false
	}
	return rounded, events, true
}

// wideAddSub is the exact sum or difference of two nonzero inline operands
// whose exponents differ by at most 38, at the smaller exponent: the shape
// addSubExact declines because the aligned operand leaves 128 bits. ok is
// false for a zero operand, a wider gap and an exact zero, which the
// general path owns.
func wideAddSub(d, other Decimal, subtract bool) (sum wide256, exponent int64, negative, ok bool) {
	if d.isZero() || other.isZero() {
		return sum, 0, false, false
	}
	a, b := wide256{d.words.lo, d.words.hi}, wide256{other.words.lo, other.words.hi}
	ae, be := int64(d.exponent()), int64(other.exponent())
	exponent = min(ae, be)
	if gap := max(ae, be) - exponent; gap > 38 {
		return sum, 0, false, false
	} else if ae > be {
		a = mulWide(d.words, pow10Wide[gap])
	} else {
		b = mulWide(other.words, pow10Wide[gap])
	}
	negative = d.negative()
	if negative == (other.negative() != subtract) {
		return addWide(a, b), exponent, negative, true
	}
	switch a.cmp(b) {
	case 0:
		return sum, 0, false, false
	case 1:
		return subWide(a, b), exponent, negative, true
	}
	return subWide(b, a), exponent, !negative, true
}

// contextRoundWide is contextRoundInline for an exact nonzero 256-bit
// result at an exponent that may lie outside int32: it returns the result
// as it is when it fits the precision and any guards, and otherwise drops
// the excess digits in word divisions, the last of which leaves the guard
// digit. The precision must leave the rounded coefficient inline. ok is
// false wherever contextRoundInline defers.
func contextRoundWide(w wide256, exponent int64, negative bool, ctx Context) (rounded Decimal, events Conditions, ok bool) {
	p := uint64(ctx.precision)
	if p > 38 {
		return Decimal{}, 0, false
	}
	n := w.digits()
	if n <= p {
		if exponent < math.MinInt32 || exponent > math.MaxInt32 {
			return Decimal{}, 0, false
		}
		exact := inlineDecimal(uint128{w[0], w[1]}, int32(exponent), negative)
		return exact, 0, contextExactFits(exact, ctx)
	}
	cut := n - p
	target := exponent + int64(cut)
	if target < math.MinInt32 || target > math.MaxInt32 || ctx.guarded && exponent+int64(n)-1 < int64(ctx.guards.Emin) {
		return Decimal{}, 0, false
	}
	sticky := false
	for cut--; cut > 0; {
		step := min(cut, 19)
		sticky = w.divSmall(pow10Words[step]) != 0 || sticky
		cut -= step
	}
	guard := uint32(w.divSmall(10))
	inexact := guard != 0 || sticky
	if inexact && ctx.rounding == Exact {
		return Decimal{}, 0, false
	}
	events = Rounded
	q := uint128{w[0], w[1]} // below 10^p ≤ 10^38
	up := contextRoundUp(ctx.rounding, negative, guard, sticky, uint32(q.lo&1))
	if inexact {
		events |= Inexact | roundingDirection(up, negative)
	}
	if up {
		var carry uint64
		q.lo, carry = bits.Add64(q.lo, 1, 0)
		q.hi += carry
	}
	if inlineCompare(q, pow10Wide[p]) == 0 {
		if target++; target > math.MaxInt32 {
			return Decimal{}, 0, false
		}
		q = pow10Wide[p-1]
	}
	if ctx.guarded && target+int64(p)-1 > int64(ctx.guards.Emax) {
		return Decimal{}, 0, false
	}
	return inlineDecimal(q, int32(target), negative), events, true
}

// inlineMulAdmitted evaluates the Mul admissions of two inline operands
// from their digit counts alone, as the general path does: the planned
// da+db digits against the digit cap (the exact form), and the work
// t(da)·t(db)+da+db, plus the finisher's 2N+1 with N ≤ da+db for the
// context form at precision p > 0, whose result has N ≤ min(da+db, p)
// digits.
func inlineMulAdmitted(d, other Decimal, budget limits, precision uint64) bool {
	da, db := inlineDigits(d.words), inlineDigits(other.words)
	digits := da + db
	work := digitLimbs(da)*digitLimbs(db) + digits
	if precision != 0 {
		digits = min(digits, precision)
		work += 2*digits + 1
	}
	return budget.admits(digits, work)
}

// contextProductLimbs bounds the operands, in limbs taken together, whose
// exact product MulWithContext builds on the stack and rounds once. Longer
// operands stream the product instead, so that no call holds more than its
// result.
const contextProductLimbs = 128

func (d Decimal) contextMul(other Decimal, ctx Context, budget limits, op string) (Decimal, Conditions, error) {
	return d.contextMulPath(other, ctx, budget, op, false)
}

// contextMulPath is the context Mul kernel. Public entry points pass
// stream=false. stream=true takes neither the inline paths nor the stack
// product: only tests pass it, as the reference those paths are pinned
// against.
func (d Decimal) contextMulPath(other Decimal, ctx Context, budget limits, op string, stream bool) (Decimal, Conditions, error) {
	if ctx.precision == 0 {
		result, err := d.multiply(other, budget, op)
		return result, 0, err
	}
	// The exponent sum may leave int32: rounding, or a guard's overflow or
	// underflow, can still publish a result. The finisher refuses the ones
	// that cannot be stored.
	e := int64(d.exponent()) + int64(other.exponent())
	if !stream && d.slow == nil && other.slow == nil && (budget.MaxDigits|budget.MaxWork == 0 || inlineMulAdmitted(d, other, budget, uint64(ctx.precision))) {
		if exact, ok := inlineMul(d, other); ok {
			if contextExactFits(exact, ctx) {
				return exact, 0, nil
			}
			if rounded, events, ok := contextRoundInline(exact, ctx); ok {
				return contextOutcome(rounded, events, ctx.traps, op)
			}
		} else if !d.isZero() && !other.isZero() {
			if rounded, events, ok := contextRoundWide(mulWide(d.words, other.words), e, d.negative() != other.negative(), ctx); ok {
				return contextOutcome(rounded, events, ctx.traps, op)
			}
		}
	}
	a, b := coefficientViewOf(d), coefficientViewOf(other)
	p := contextPlan{a: a, b: b, ideal: e, negative: d.negative() != other.negative(), mul: true}
	if a.count == 0 || b.count == 0 {
		p.zero, p.base = true, 1
		if !admitted(budget.MaxWork, 1, true) {
			return contextFailure(op, ErrInsufficientStorage)
		}
		return contextRun(p, ctx, budget, op)
	}
	da, validA := arithmeticDigits(&a)
	db, validB := arithmeticDigits(&b)
	if !validA || !validB {
		return contextFailure(op, ErrInsufficientStorage)
	}
	digits, valid := arithmeticAdd(da, db)
	if !valid {
		return contextFailure(op, ErrInsufficientStorage)
	}
	p.base, valid = mulWorkCharge(da, db, digits)
	if !admitted(budget.MaxWork, p.base, valid) {
		return contextFailure(op, ErrInsufficientStorage)
	}
	p.groups, valid = arithmeticAdd(uint64(a.count), uint64(b.count))
	if !valid {
		return contextFailure(op, ErrInsufficientStorage)
	}
	if !stream && p.groups <= contextProductLimbs {
		return contextRunProduct(&p, &ctx, budget, op)
	}
	return contextRun(p, ctx, budget, op)
}

// contextRunProduct is contextRun for a planned, admitted product short
// enough for the stack: one pass of the multiplication kernel, then the
// shared finisher rounds the exact product once.
func contextRunProduct(p *contextPlan, ctx *Context, budget limits, op string) (Decimal, Conditions, error) {
	var stack [contextProductLimbs + 1]uint32 // a spare limb for the rounding carry
	if !fillMultiply(stack[:p.groups], &p.a, &p.b) {
		return contextRun(*p, *ctx, budget, op)
	}
	var etiny int64
	if ctx.guarded {
		etiny = int64(ctx.guards.Emin) - (int64(ctx.precision) - 1)
	}
	return finishContext(trimLimbs(stack[:p.groups]), divExactClass, p.ideal, etiny, p.ideal, p.negative, ctx, p.base, budget, op)
}
