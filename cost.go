// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"math"
	"math/big"
	"math/bits"
	"reflect"
)

// Shape is what a cost estimator needs of a Decimal operand: its coefficient
// digit count, exponent and sign. Digits is 0 exactly for zero, whose
// operations take cheaper paths; a refusal an estimator predicts for a
// nonzero shape (Digits ≥ 1) holds for every nonzero value of it. A caller
// that cannot rule out zero takes the Max of both estimates.
type Shape struct {
	// Digits is the coefficient digit count, 0 exactly for zero.
	Digits uint64
	// Exponent is the stored exponent.
	Exponent int32
	// Negative is the sign.
	Negative bool
}

// Shape returns d's shape in O(1) without allocating.
func (d Decimal) Shape() Shape {
	if d.isZero() {
		return Shape{Exponent: d.exponent()}
	}
	return Shape{Digits: d.CoefficientDigits(), Exponent: d.exponent(), Negative: d.negative()}
}

// Cost bounds one budgeted call before it is made. Each field is an upper
// bound on what the call can need of the matching budget axis for every input
// of the estimated shape, attained by that shape's worst case within the
// family's documented slack, or zero when the family does not consult that
// axis. HeapBytes bounds the cumulative bytes the call allocates, garbage
// included, as the Go allocator rounds them.
//
// The Budget of a Cost always admits the call. A
// refusal the shape cannot decide may still occur and is not predicted: a
// division by zero is predicted only for a zero-divisor shape, while a
// non-integral or non-terminating value, an invalid rounding mode, an
// Exact-mode refusal, and an exponent that leaves int32 only after
// rounding or stripping are not. Such a refusal never does more work than
// the estimate.
type Cost struct {
	WorkUnits   uint64 // Budget.MaxWork
	Digits      uint64 // Budget.MaxDigits
	InputDigits uint64 // Budget.MaxInputDigits
	InputBytes  uint64 // Budget.MaxInputBytes
	OutputBytes uint64 // Budget.MaxOutputBytes
	HeapBytes   uint64 // cumulative allocated bytes, allocator-rounded
}

// Budget returns the Budget that always admits the estimated call.
func (c Cost) Budget() Budget {
	return Budget{MaxInputBytes: c.InputBytes, MaxInputDigits: c.InputDigits, MaxDigits: c.Digits, MaxOutputBytes: c.OutputBytes, MaxWork: c.WorkUnits}
}

// Budget caps the resources of one call; each Estimate function returns
// the Cost whose Budget admits it. Operations that round to a precision
// read it from their Context (Context.WithBudget); operations with an
// explicit target exponent or no rounding take it as a parameter. Zero on
// an axis means no caller limit on that axis, and a family ignores the axes
// it does not read:
//
//   - Context arithmetic, FromRat, FromFloat64, Sum and the target forms
//     DivToExponent, RoundToMultiple, FromRatToExponent and
//     FromFloat64ToExponent read MaxDigits (result coefficient digits) and
//     MaxWork.
//   - Parse, ParseToExponent and ParseJSON read MaxInputBytes and
//     MaxDigits; parsing has no work axis, its time being linear in input
//     bytes plus result digits.
//   - Scan reads MaxInputBytes, MaxDigits and MaxWork.
//   - Display (Fixed, Scientific, Engineering and their Append forms,
//     AppendEngineering among them) reads MaxOutputBytes and MaxWork
//     (source digits plus output bytes).
//   - Integer conversion (FromBigInt, BigInt, Rat, Compose,
//     NewTwosComplement) reads MaxInputDigits, MaxDigits (result digits)
//     and MaxWork.
//   - The elementary functions read MaxDigits and MaxWork in evaluation
//     units; see BoundEvaluation.
//
// Work units differ by family: a digit visit for Add, Sub and Quantize; a
// nine-digit tile interaction plus one per input digit for Mul; a base-10⁹
// limb operation or digit read for the Div family; a 64-bit word operation
// for the FromRat family; 87 per exact-expansion pass for binary64
// conversion; one base-10⁹ limb step of the radix conversion for integer
// conversion; and the dispatch, envelope and allocation charges of
// BoundEvaluation for the elementary functions. Context forms add 2N+1 for an
// N-digit result. Within a family, time is at most affine in charged units,
// a + b·W, so a work cap also bounds latency; a call served in machine words
// takes less time and is admitted or refused as the general path decides. A
// refusal of byte input for resources never copies the input.
//
// The Estimate documentation writes each family's tariff, its formula for
// work units, in one notation: B is the base charge admitted before any work
// (the precharge), C a path charge, N the result digits, W the total (context
// forms: W = B + 2N + 1), t(d) = 1+(d−1)/9 the base-10⁹ limbs of d digits,
// and L the aligned digit span. The adaptive functions (Exp, Ln, Log10,
// PowDecimal and the trigonometric and hyperbolic functions) charge the
// evaluation units described above, over every stage of one call.
type Budget struct {
	// MaxInputBytes caps the source bytes of text, JSON and Scan input.
	MaxInputBytes uint64
	// MaxInputDigits caps the source digits of an integer conversion.
	MaxInputDigits uint64
	// MaxDigits caps the result coefficient digits.
	MaxDigits uint64
	// MaxOutputBytes caps rendered text.
	MaxOutputBytes uint64
	// MaxWork caps the family's work units.
	MaxWork uint64
}

// costTally accumulates checked uint64 sums and products; any overflow makes
// the estimate "no finite positive budget".
type costTally struct{ overflow bool }

func (t *costTally) add(values ...uint64) uint64 {
	var sum uint64
	for _, v := range values {
		var carry uint64
		sum, carry = bits.Add64(sum, v, 0)
		if carry != 0 {
			t.overflow = true
		}
	}
	return sum
}

func (t *costTally) mul(x, y uint64) uint64 {
	hi, lo := bits.Mul64(x, y)
	if hi != 0 {
		t.overflow = true
	}
	return lo
}

// allocBound bounds the bytes the Go allocator charges TotalAlloc for one
// n-byte object: n + n/4 + 16 rounded up to 16 below 32 KiB, the size-class
// envelope checked against Go 1.27.1 with and without the malloc header, and
// 8 KiB pages above. TestAllocBoundCoversSizeClasses pins it on the running
// toolchain.
func allocBound(t *costTally, n uint64) uint64 {
	switch {
	case n == 0:
		return 0
	case n <= 32<<10:
		return (n + n/4 + 16 + 15) &^ 15
	default:
		return t.add(n, 8191) &^ 8191
	}
}

// holderBytes is the size of a slowCoefficient: a slice header (three
// words) and the nine-limb fused array.
const holderBytes = 3*bits.UintSize/8 + 4*slowSmallLimbs

// publishBytes bounds the allocation of publishing a result of at most
// count limbs: nothing inline (digits ≤ 38), one fused holder up to slowSmallLimbs
// limbs, and otherwise a holder plus one slice. That slice is either the
// exact copy publishScratch makes of stack scratch, or the heap buffer a
// producer beyond its scratch hands to publishOwned without copying.
func publishBytes(t *costTally, digits, count uint64) uint64 {
	if digits <= 38 {
		return 0
	}
	bytes := allocBound(t, holderBytes)
	if count > slowSmallLimbs {
		bytes = t.add(bytes, allocBound(t, t.mul(4, count)))
	}
	return bytes
}

// estimateError is the estimators' refusal: the ErrorCode itself, which
// allocates nothing. It names the operation's own shape-determined refusal,
// or ErrInsufficientStorage for "no finite positive budget admits this
// shape".
func estimateError(code ErrorCode) (Cost, error) {
	return Cost{}, code
}

// finishCost is the Cost of a tally, or the "no finite budget" refusal.
func finishCost(t *costTally, c Cost) (Cost, error) {
	if t.overflow {
		return estimateError(ErrInsufficientStorage)
	}
	return c, nil
}

// Max returns the per-axis maximum of two estimates, for a caller that does
// not know which of several shapes (for example which sign relation) it will
// meet.
func (c Cost) Max(o Cost) Cost {
	return Cost{
		WorkUnits: max(c.WorkUnits, o.WorkUnits), Digits: max(c.Digits, o.Digits),
		InputDigits: max(c.InputDigits, o.InputDigits), InputBytes: max(c.InputBytes, o.InputBytes),
		OutputBytes: max(c.OutputBytes, o.OutputBytes), HeapBytes: max(c.HeapBytes, o.HeapBytes),
	}
}

func estimateAddSub(x, y Shape, subtract bool, op string) (Cost, error) {
	var t costTally
	work, digits := addSubTariff(&t, x, y, subtract)
	count := 1 + (digits-1)/9
	if t.overflow {
		return estimateError(ErrInsufficientStorage)
	}
	if _, err := arithmeticLimbCount(digits, op); err != nil {
		return estimateError(ErrInsufficientStorage)
	}
	heap := publishBytes(&t, digits, count)
	return finishCost(&t, Cost{WorkUnits: work, Digits: digits, HeapBytes: heap})
}

// addSubTariff is the exact Add/Sub work charge and exact result digit bound
// over the aligned span L, with a zero shape counted as one digit.
func addSubTariff(t *costTally, x, y Shape, subtract bool) (work, digits uint64) {
	e := min(x.Exponent, y.Exponent)
	sa, sb := uint64(int64(x.Exponent)-int64(e)), uint64(int64(y.Exponent)-int64(e))
	dx, dy := max(x.Digits, 1), max(y.Digits, 1)
	spanX, spanY := t.add(dx, sa), t.add(dy, sb)
	L := max(spanX, spanY)
	var ok bool
	if x.Negative == (y.Negative != subtract) {
		// Same effective signs: a carry adds a digit only where the aligned
		// spans overlap.
		work, ok = addSubSameCharge(dx, dy, L)
		digits = L
		if sa < spanY && sb < spanX {
			digits = t.add(L, 1)
		}
	} else {
		work, ok = addSubOppositeCharge(dx, dy, L)
		digits = L
	}
	if !ok {
		t.overflow = true
	}
	return work, digits
}

// estimateMul is EstimateMul at precision 0.
func estimateMul(x, y Shape) (Cost, error) {
	if e := int64(x.Exponent) + int64(y.Exponent); e < -1<<31 || e > 1<<31-1 {
		return estimateError(ErrExponentRange)
	}
	return estimateMulWork(x, y)
}

// estimateMulWork is the exact product's cost whatever its exponent.
func estimateMulWork(x, y Shape) (Cost, error) {
	const op = "EstimateMul"
	var t costTally
	dx, dy := max(x.Digits, 1), max(y.Digits, 1)
	digits := t.add(dx, dy)
	work, ok := mulWorkCharge(dx, dy, digits)
	if !ok || t.overflow {
		return estimateError(ErrInsufficientStorage)
	}
	count := t.add(1+(dx-1)/9, 1+(dy-1)/9)
	if _, err := arithmeticPhysicalLimbCount(count, op); err != nil {
		return estimateError(ErrInsufficientStorage)
	}
	return finishCost(&t, Cost{WorkUnits: work, Digits: digits, HeapBytes: publishBytes(&t, digits, count)})
}

// EstimateAdd bounds AddWithContext: the base charge B over the shapes as the
// context planner reduces them (a remote nonzero operand becomes one sticky
// digit, and a zero's exponent is clamped just below the rounding position),
// the finisher 2N+1, and N result digits. B is 1 for two zeros, the nonzero's
// aligned span for one zero (a zero is not part of that span), and the Add
// tariff for two nonzero shapes. N is min(p, the reduced exact sum's digits),
// or p when guards make an overflow reachable for these shapes (the overflow
// publishes p nines).
//
// At precision 0 it bounds the exact Add for operands of shapes x and y. The
// relation of the signs decides the tariff; a caller that does not know the
// signs takes the Max of the estimates for equal and opposite signs. A shape
// of one digit covers zero.
func EstimateAdd(x, y Shape, ctx Context) (Cost, error) {
	return estimateContextAddSub(x, y, ctx, false, "EstimateAdd")
}

// EstimateSub bounds SubWithContext.
//
// At precision 0 it bounds the exact Sub; the effective sign relation is
// that of x + (−y).
func EstimateSub(x, y Shape, ctx Context) (Cost, error) {
	return estimateContextAddSub(x, y, ctx, true, "EstimateSub")
}

func estimateContextAddSub(x, y Shape, ctx Context, subtract bool, op string) (Cost, error) {
	if ctx.precision == 0 {
		return estimateAddSub(x, y, subtract, op)
	}
	// The context path streams the reduced operands and never materializes
	// the exact sum, so the bare estimator's physical refusal over the
	// unreduced span does not apply.
	x, y = contextReduceShapes(x, y, ctx)
	switch {
	case x.Digits == 0 && y.Digits == 0:
		// A zero result is never checked against the guards.
		return contextEstimate(1, 1, math.MinInt64, ctx, op)
	case x.Digits == 0 || y.Digits == 0:
		nonzero, zero := x, y
		if x.Digits == 0 {
			nonzero, zero = y, x
		}
		var t costTally
		span := t.add(nonzero.Digits, uint64(int64(nonzero.Exponent)-int64(min(nonzero.Exponent, zero.Exponent))))
		if t.overflow {
			return estimateError(ErrInsufficientStorage)
		}
		// Only a rounding carry raises the nonzero's adjusted exponent.
		return contextEstimate(span, span, int64(nonzero.Exponent)+int64(nonzero.Digits), ctx, op)
	}
	var t costTally
	base, digits := addSubTariff(&t, x, y, subtract)
	if t.overflow {
		return estimateError(ErrInsufficientStorage)
	}
	// B is the bare tariff without its planned result digit; the context path
	// charges the same base.
	adjusted := max(int64(x.Exponent)+int64(x.Digits)-1, int64(y.Exponent)+int64(y.Digits)-1)
	return contextEstimate(base, digits, adjusted+2, ctx, op)
}

// EstimateMul bounds MulWithContext: base t(d1)·t(d2) + d1 + d2, the finisher 2N+1,
// N = min(p, d1+d2), or p when guards make an overflow reachable.
//
// At precision 0 it bounds the exact Mul: digits d1+d2, work t(d1)·t(d2)
// nine-digit tile interactions plus d1+d2, and the publication of a physical
// buffer of t(d1)+t(d2) limbs. There an exponent sum outside int32 is the
// operation's ErrExponentRange; at a finite precision the rounded result
// decides, which the shapes alone do not determine.
func EstimateMul(x, y Shape, ctx Context) (Cost, error) {
	const op = "EstimateMul"
	if ctx.precision == 0 {
		return estimateMul(x, y)
	}
	exact, err := estimateMulWork(x, y)
	if err != nil {
		return exact, err
	}
	adjusted := int64(x.Exponent) + int64(max(x.Digits, 1)) - 1 + int64(y.Exponent) + int64(max(y.Digits, 1)) - 1
	return contextEstimate(exact.WorkUnits, exact.Digits, adjusted+2, ctx, op)
}

// contextEstimate completes a context estimate from the base charge, the
// exact result's digit bound and a bound on the result's adjusted exponent
// (after a carry and a rounding carry).
func contextEstimate(base, exactDigits uint64, maxAdjusted int64, ctx Context, op string) (Cost, error) {
	var t costTally
	p := uint64(ctx.precision)
	n := min(p, exactDigits)
	if ctx.guarded && maxAdjusted > int64(ctx.guards.Emax) {
		n = p
	}
	work, ok := contextFinalCharge(base, n)
	if !ok {
		return estimateError(ErrInsufficientStorage)
	}
	if _, err := arithmeticLimbCount(n, op); err != nil {
		return estimateError(ErrInsufficientStorage)
	}
	count := 1 + (n-1)/9
	return finishCost(&t, Cost{WorkUnits: work, Digits: n, HeapBytes: publishBytes(&t, n, count)})
}

// EstimateQuantize bounds QuantizeWithContext (and, with a zero or unguarded
// precision-0 Context carrying the mode, Quantize) through the Quantize
// tariff. The all-nines carry digit is counted only when
// ctx's rounding can raise the magnitude for the operand's sign. A target
// outside a guarded context's [Etiny, Emax], or a result that cannot fit the
// precision or Emax even without that carry, is the operation's
// ErrInvalidOperation.
func EstimateQuantize(x Shape, target int32, ctx Context) (Cost, error) {
	return estimateQuantize(x, target, ctx, "EstimateQuantize")
}

// EstimateRoundToIntegral bounds RoundToIntegralWithContext, a
// quantization to exponent 0.
func EstimateRoundToIntegral(x Shape, ctx Context) (Cost, error) {
	return estimateQuantize(x, 0, ctx, "EstimateRoundToIntegral")
}

func estimateQuantize(x Shape, target int32, ctx Context, op string) (Cost, error) {
	if ctx.guarded {
		etiny := int64(ctx.guards.Emin) - int64(ctx.precision-1)
		if int64(target) < etiny || target > ctx.guards.Emax {
			return estimateError(ErrInvalidOperation)
		}
	}
	digits := quantizeCount{lo: max(x.Digits, 1)}
	difference := int64(x.Exponent) - int64(target)
	carry := difference < 0 && digits.cmpUint(uint64(-difference)) > 0 && quantizeMayRoundUp(ctx.rounding, x.Negative)
	_, work, length := quantizeTariff(digits, difference, carry)
	_, _, exact := quantizeTariff(digits, difference, false)
	// A zero takes its own path, and in Exact mode an inexact shrink is
	// refused first as an *Error: neither refusal is shape-decided.
	predict := x.Digits != 0 && !(ctx.rounding == Exact && difference < 0)
	if predict && (ctx.precision != 0 && exact.cmpUint(uint64(ctx.precision)) > 0 ||
		ctx.guarded && exact.cmpUint(uint64(int64(ctx.guards.Emax)-int64(target)+1)) > 0) {
		return estimateError(ErrInvalidOperation)
	}
	if work.hi != 0 || length.hi != 0 {
		return estimateError(ErrInsufficientStorage)
	}
	var t costTally
	var heap uint64
	if difference != 0 {
		if _, err := quantizePhysicalCount(length, op); err != nil {
			return estimateError(ErrInsufficientStorage)
		}
		heap = publishBytes(&t, length.lo, 1+(length.lo-1)/9)
	}
	return finishCost(&t, Cost{WorkUnits: work.lo, Digits: length.lo, HeapBytes: heap})
}

// quantizeMayRoundUp reports whether mode can round a discarded nonzero
// tail up in magnitude for an operand of the given sign.
func quantizeMayRoundUp(mode RoundingMode, negative bool) bool {
	switch mode {
	case TowardZero, Exact:
		return false
	case TowardPositiveInfinity:
		return !negative
	case TowardNegativeInfinity:
		return negative
	}
	return true
}

// divEstimate completes a Div-family estimate from the shared plan at
// division exponent t: work B + 2N + 1 for N result digits (nmax), heap for
// the scratch above the 48-limb stack plus the published result; a plan
// that overflows or cannot be physically admitted is ErrInsufficientStorage.
func divEstimate(dx, dy uint64, ideal, t int64, admitDigits, nmax uint64) (Cost, error) {
	return divEstimateWithProbe(dx, dy, ideal, t, admitDigits, nmax, nil)
}

func divEstimateWithProbe(dx, dy uint64, ideal, target int64, admitDigits, nmax uint64, ctx *Context) (Cost, error) {
	t := target
	s := divSource{dx: dx, dy: dy, ideal: ideal}
	p := s.plan(t)
	if !p.ok {
		return estimateError(ErrInsufficientStorage)
	}
	var t2 costTally
	n, d, q := uint64(0), uint64(0), uint64(2)
	if p.path == divDivide {
		n, d, q = s.divScratch(p)
	}
	total := t2.add(n, d, q)
	var probeHeap uint64
	probeAdmitted := false
	if ctx != nil {
		if trial, _, ok := s.exactProbe(p, target); ok {
			probeTotal := s.scratchTotal(trial)
			probeAdmitted = divAdmitted(probeTotal, s.probeResultDigits(trial, ctx))
			if probeAdmitted && probeTotal > divStackLimbs {
				probeHeap = allocBound(&t2, t2.mul(4, probeTotal))
			}
		}
	}
	if t2.overflow || !divAdmitted(total, admitDigits) && !probeAdmitted {
		return estimateError(ErrInsufficientStorage)
	}
	work, ok := contextFinalCharge(p.charge, nmax)
	if !ok {
		return estimateError(ErrInsufficientStorage)
	}
	var heap uint64
	if total > divStackLimbs {
		heap = allocBound(&t2, t2.mul(4, total))
	}
	count := 1 + (nmax-1)/9
	heap = t2.add(probeHeap, heap, publishBytes(&t2, nmax, count))
	return finishCost(&t2, Cost{WorkUnits: work, Digits: nmax, HeapBytes: heap})
}

// divZeroEstimate handles zero shapes for the Div family: a zero divisor is
// the operation's ErrDivisionByZero (ErrDivisionUndefined for 0/0), and a
// zero dividend publishes zero at the ideal exponent (one digit, W = 4),
// refusing only an ideal exponent outside int32.
func divZeroEstimate(x, y Shape) (Cost, error, bool) {
	switch {
	case y.Digits == 0 && x.Digits == 0:
		c, err := estimateError(ErrDivisionUndefined)
		return c, err, true
	case y.Digits == 0:
		c, err := estimateError(ErrDivisionByZero)
		return c, err, true
	case x.Digits == 0:
		if ideal := int64(x.Exponent) - int64(y.Exponent); ideal < -1<<31 || ideal > 1<<31-1 {
			c, err := estimateError(ErrExponentRange)
			return c, err, true
		}
		return Cost{WorkUnits: 4, Digits: 1}, nil, true
	}
	return Cost{}, nil, false
}

// estimateDiv is EstimateDiv at precision 0.
func estimateDiv(x, y Shape) (Cost, error) {
	if c, err, zero := divZeroEstimate(x, y); zero {
		return c, err
	}
	dx, dy := max(x.Digits, 1), max(y.Digits, 1)
	ideal := int64(x.Exponent) - int64(y.Exponent)
	t, kMax, code := divUnlimitedTarget(dy, ideal)
	if code != 0 {
		return estimateError(code)
	}
	var tally costTally
	dn := tally.add(dx, kMax)
	if tally.overflow {
		return estimateError(ErrInsufficientStorage)
	}
	nmax := uint64(1)
	if dn >= dy {
		nmax = dn - dy + 1
	}
	return divEstimate(dx, dy, ideal, t, dn, nmax)
}

// EstimateDivToExponent bounds DivToExponentWithBudget at target: the
// quotient at the target has at most dn − dy + 2 digits (one for a
// rounding carry, whatever the mode), or 1 when the plan shows without
// dividing that the quotient is below one unit of the target.
func EstimateDivToExponent(x, y Shape, target int32) (Cost, error) {
	if y.Digits == 0 {
		c, err, _ := divZeroEstimate(x, y)
		return c, err
	}
	if x.Digits == 0 {
		return Cost{WorkUnits: 4, Digits: 1}, nil // zero at the target
	}
	dx, dy := max(x.Digits, 1), max(y.Digits, 1)
	ideal := int64(x.Exponent) - int64(y.Exponent)
	s := divSource{dx: dx, dy: dy, ideal: ideal}
	p := s.plan(int64(target))
	nmax := uint64(1)
	if p.path == divDivide && p.dn >= dy {
		nmax = p.dn - dy + 2
	}
	return divEstimate(dx, dy, ideal, int64(target), nmax, nmax)
}

// EstimateDiv bounds DivWithContext: the division runs at t′ =
// (dx−dy)+ideal−p (raised to Etiny under guards) and the result has at most
// p digits.
//
// At precision 0 it bounds the exact Div: the exact quotient is divided at
// ideal − ⌈3.322·dy⌉ and has at most dn − dy + 1 digits there before
// trailing zeros are stripped (a non-terminating quotient is refused, which
// the estimate does not predict). Exponents that leave int32 are
// ErrExponentRange.
func EstimateDiv(x, y Shape, ctx Context) (Cost, error) {
	if ctx.precision == 0 {
		return estimateDiv(x, y)
	}
	if c, err, zero := divZeroEstimate(x, y); zero {
		return c, err
	}
	dx, dy := max(x.Digits, 1), max(y.Digits, 1)
	ideal := int64(x.Exponent) - int64(y.Exponent)
	tPrime, _ := divContextTarget(dx, dy, ideal, ctx)
	p := uint64(ctx.precision)
	return divEstimateWithProbe(dx, dy, ideal, tPrime, p+1, p, &ctx)
}

// ratZeroCost is the zero rational's charge: one digit, W = 1 + 2·1 + 1.
func ratZeroCost() Cost { return Cost{WorkUnits: 4, Digits: 1} }

// ratCost completes a FromRat estimate: work B + 2N + 1 for N ≤ nmax
// digits, and heap bytes of the measured math/big scratch envelope for each
// planned phase plus the published result.
func ratCost(charge uint64, operandWords []uint64, nmax uint64) (Cost, error) {
	var t costTally
	work, ok := contextFinalCharge(charge, nmax)
	if !ok {
		return estimateError(ErrInsufficientStorage)
	}
	var heap uint64
	for _, w := range operandWords {
		scratch, ok := ratScratchBytes(w)
		if !ok {
			return estimateError(ErrInsufficientStorage)
		}
		heap = t.add(heap, scratch)
	}
	count := 1 + (nmax-1)/9
	heap = t.add(heap, allocBound(&t, t.mul(4, count)), allocBound(&t, holderBytes))
	return finishCost(&t, Cost{WorkUnits: work, Digits: nmax, HeapBytes: heap})
}

// estimateFromRat is EstimateFromRat at precision 0.
func estimateFromRat(numBits, denBits uint64) (Cost, error) {
	if numBits == 0 {
		return ratZeroCost(), nil
	}
	if denBits == 0 {
		return estimateError(ErrConversionSyntax)
	}
	charge, words, uc, ok := ratExactWorst(numBits, denBits)
	if !ok || !ratAdmitted(words, uc+1) {
		return estimateError(ErrInsufficientStorage)
	}
	return ratCost(charge, []uint64{words}, uc)
}

// EstimateFromRatToExponent bounds FromRatToExponentWithBudget at target:
// the shared division plan, and a result of at most Uq + 1 digits (one for
// a rounding carry), or one digit when the value lies far below the target.
func EstimateFromRatToExponent(numBits, denBits uint64, target int32) (Cost, error) {
	if numBits == 0 {
		return ratZeroCost(), nil
	}
	if denBits == 0 {
		return estimateError(ErrConversionSyntax)
	}
	s := ratSource{bn: numBits, bd: denBits}
	p := s.plan(int64(target))
	if !p.ok || !p.tiny && !ratAdmitted(p.operandWords, p.quotientBound+1) {
		return estimateError(ErrInsufficientStorage)
	}
	if p.tiny {
		return ratCost(p.charge, nil, 1)
	}
	return ratCost(p.charge, []uint64{p.operandWords}, p.quotientBound+1)
}

// EstimateFromRat bounds FromRatWithContext: when the precision exceeds
// numBits+denBits, the exact attempt (its worst case) and then the division
// for a non-terminating value, else the division alone, at t′ = a_lo − p + 1
// raised to Etiny; the result has at most p digits.
//
// At precision 0 it bounds the exact FromRat for a numerator of numBits and
// a denominator of denBits bits (numBits 0 is zero). The tariff's maximum
// over every denominator of that size is used; a non-terminating value, or
// one whose twos exceed 2^31, is refused and not estimated.
func EstimateFromRat(numBits, denBits uint64, ctx Context) (Cost, error) {
	if ctx.precision == 0 {
		return estimateFromRat(numBits, denBits)
	}
	if numBits == 0 {
		return ratZeroCost(), nil
	}
	if denBits == 0 {
		return estimateError(ErrConversionSyntax)
	}
	aLow, ok := ratAdjustedLow(numBits, denBits)
	if !ok {
		return estimateError(ErrInsufficientStorage)
	}
	precision := int64(ctx.precision)
	tPrime := aLow - precision + 1
	if ctx.guarded {
		tPrime = max(tPrime, int64(ctx.guards.Emin)-(precision-1))
	}
	var t costTally
	var spent uint64
	var wordsBuf [2]uint64
	words := wordsBuf[:0]
	if uint64(ctx.precision) > t.add(numBits, denBits) && !t.overflow {
		charge, w, uc, ok := ratExactWorst(numBits, denBits)
		if !ok || !ratAdmitted(w, uc+1) {
			return estimateError(ErrInsufficientStorage)
		}
		spent, words = charge, append(words, w)
	}
	s := ratSource{bn: numBits, bd: denBits}
	p := s.plan(tPrime)
	charge := t.add(spent, p.charge)
	if !p.ok || t.overflow || !p.tiny && !ratAdmitted(p.operandWords, p.quotientBound+1) {
		return estimateError(ErrInsufficientStorage)
	}
	if !p.tiny {
		words = append(words, p.operandWords)
	}
	return ratCost(charge, words, uint64(ctx.precision))
}

// EstimateFromFloat64ToExponent bounds FromFloat64ToExponentWithBudget for
// the float f at target: 87 work units per exact-expansion pass plus one
// per padded limb, and the finisher 2N+1. The expansion runs on the stack
// without allocating, so N is exact when the target pads it (D + pad) and
// at most D − drop + 1 when it rounds (one for a carry, whatever the
// mode). A non-finite f is ErrConversionSyntax.
func EstimateFromFloat64ToExponent(f float64, target int32) (Cost, error) {
	if float64Nonfinite(f) {
		return estimateError(ErrConversionSyntax)
	}
	_, m, e := binary64Parts(f)
	if m == 0 {
		return ratZeroCost(), nil
	}
	t := int64(target)
	x := min(e, 0)
	var pad uint64
	if t < x {
		pad = uint64(x - t)
	}
	var tally costTally
	charge := tally.add(binary64Passes(e)*binary64Limbs, (pad+8)/9)
	var buf [binary64Limbs]uint32
	limbs, x := expandDyadic(&buf, m, e)
	d := limbsDigits(limbs)
	var n uint64
	var heap uint64
	switch {
	case pad != 0:
		n = tally.add(d, pad)
		count := 1 + (n-1)/9
		if count >= binary64Limbs {
			if !ratAdmitted(0, tally.mul(n, 2)) {
				return estimateError(ErrInsufficientStorage)
			}
			heap = allocBound(&tally, tally.mul(4, count+1))
		}
		heap = tally.add(heap, publishBytes(&tally, n, count))
	default:
		drop := uint64(t - x)
		n = 1
		if d > drop {
			n = d - drop + 1
		}
		heap = publishBytes(&tally, n, 1+(n-1)/9)
	}
	work, ok := contextFinalCharge(charge, n)
	if !ok {
		return estimateError(ErrInsufficientStorage)
	}
	return finishCost(&tally, Cost{WorkUnits: work, Digits: n, HeapBytes: heap})
}

// EstimateFromFloat64 bounds FromFloat64WithContext
// for the float f: 87 work units per exact-expansion pass and the finisher
// 2N+1, where N is the expansion's D digits at precision 0, else at most
// min(D, p), or p when a guarded overflow substitutes the context's largest
// value. A non-finite f is ErrConversionSyntax.
func EstimateFromFloat64(f float64, ctx Context) (Cost, error) {
	if float64Nonfinite(f) {
		return estimateError(ErrConversionSyntax)
	}
	_, m, e := binary64Parts(f)
	if m == 0 {
		return ratZeroCost(), nil
	}
	var buf [binary64Limbs]uint32
	limbs, x := expandDyadic(&buf, m, e)
	d := limbsDigits(limbs)
	n := d
	if p := uint64(ctx.precision); p != 0 {
		n = min(d, p)
		// Overflow needs an adjusted exponent x+D−1 above Emax, or at Emax
		// with a rounding carry, which needs D > p.
		if a := x + int64(d) - 1; ctx.guarded && (a > int64(ctx.guards.Emax) || d > p && a == int64(ctx.guards.Emax)) {
			n = p
		}
	}
	return ratCost(binary64Passes(e)*binary64Limbs, nil, n)
}

// Object sizes the integer-conversion estimators charge (Go 1.27.1).
var (
	bigIntBytes = uint64(reflect.TypeFor[big.Int]().Size())
	bigRatBytes = uint64(reflect.TypeFor[big.Rat]().Size())
)

// EstimateFromBigInt bounds FromBigIntWithBudget for a value of bitLen
// bits (0 is zero): the digit envelope U = ⌊n·log10 2⌋ + 1 on both digit
// axes, work (2⌈U/9⌉)² + 2⌈U/9⌉, and the published result.
func EstimateFromBigInt(bitLen uint64) (Cost, error) {
	if bitLen == 0 {
		return Cost{WorkUnits: 1, Digits: 1, InputDigits: 1}, nil
	}
	plan, ok := bigIntIngressPreflight(bitLen, Budget{MaxWork: 1<<64 - 1}, bigIntIngressRuntimeTarget())
	if !ok {
		return estimateError(ErrInsufficientStorage)
	}
	var t costTally
	return finishCost(&t, Cost{WorkUnits: plan.w, Digits: plan.u, InputDigits: plan.u,
		HeapBytes: publishBytes(&t, plan.u, plan.limbs)})
}

// EstimateBigInt bounds BigIntWithBudget for x: an integral result of
// d−drop digits (exponent −drop) or d+e digits (exponent e ≥ 0), work
// T² + T with T = t(d) + t(result), and the result's words and header. A
// negative exponent that drops every digit is the operation's
// ErrNonIntegral.
func EstimateBigInt(x Shape) (Cost, error) {
	return estimateBigInt(x)
}

func estimateBigInt(x Shape) (Cost, error) {
	var t costTally
	if x.Digits == 0 {
		return finishCost(&t, Cost{HeapBytes: allocBound(&t, bigIntBytes)}) // new(big.Int), no budget check
	}
	d := x.Digits
	var result uint64
	if x.Exponent < 0 {
		drop := uint64(-int64(x.Exponent))
		if drop >= d {
			return estimateError(ErrNonIntegral)
		}
		result = d - drop
	} else {
		result = t.add(d, uint64(x.Exponent))
	}
	work, ok := bigIntEgressWork(d, result)
	if !ok || t.overflow {
		return estimateError(ErrInsufficientStorage)
	}
	words, ok := bigIntEgressWords(result)
	if !ok {
		return estimateError(ErrInsufficientStorage)
	}
	heap := t.add(allocBound(&t, t.mul(uint64(words), bits.UintSize/8)), allocBound(&t, bigIntBytes))
	return finishCost(&t, Cost{WorkUnits: work, Digits: result, InputDigits: d, HeapBytes: heap})
}

// EstimateRat bounds RatWithBudget for x. An integral x is BigInt plus the
// Rat header. Otherwise the tariff is the maximum over the coefficient's
// stripped trailing zeros z: every term decreases in z except the limb strip
// d added for any z > 0, so the maximum is at z = 0 or z = 1; the heap covers
// the math/big scratch envelope, the numerator conversion, the loop's two
// reused integers, 10^j, the Rat and the strip's published coefficient.
func EstimateRat(x Shape) (Cost, error) {
	if x.Digits == 0 {
		var t costTally
		return finishCost(&t, Cost{HeapBytes: allocBound(&t, bigRatBytes)}) // new(big.Rat), no budget check
	}
	d := x.Digits
	if x.Exponent >= 0 {
		c, err := estimateBigInt(x)
		if err != nil {
			return c, err
		}
		var t costTally
		c.HeapBytes = t.add(c.HeapBytes, allocBound(&t, bigRatBytes))
		return finishCost(&t, c)
	}
	j := uint64(-int64(x.Exponent))
	var t costTally
	var c Cost
	c.InputDigits = d
	c.Digits = max(d, t.add(j, 1))
	for z := uint64(0); z <= min(1, d-1, j); z++ {
		work, wc, wj, ok := ratEgressCharge(d, j-z, z)
		if !ok || !ratAdmitted(wc+wj, d-z) {
			return estimateError(ErrInsufficientStorage)
		}
		scratch, ok := ratScratchBytes(wc + wj)
		if !ok {
			return estimateError(ErrInsufficientStorage)
		}
		word := uint64(bits.UintSize / 8)
		integer := t.add(allocBound(&t, t.mul(wc, word)), allocBound(&t, bigIntBytes))
		heap := t.add(scratch, t.mul(3, integer), allocBound(&t, t.mul(wj, word)), allocBound(&t, bigIntBytes),
			allocBound(&t, bigRatBytes), t.mul(2, allocBound(&t, word)))
		if z > 0 {
			heap = t.add(heap, publishBytes(&t, d, 1+(d-1)/9))
		}
		c.WorkUnits, c.HeapBytes = max(c.WorkUnits, work), max(c.HeapBytes, heap)
	}
	return finishCost(&t, c)
}

// EstimateCompose bounds ComposeWithBudget for a coefficient of n bytes
// (0 is zero, which consults no budget): the envelope U and work W over the
// raw bits on every axis, and the published result.
func EstimateCompose(coefficientBytes uint64) (Cost, error) {
	return estimateBinary(coefficientBytes, true)
}

// EstimateNewTwosComplement bounds NewTwosComplementWithBudget for an input
// of the given byte length;
// empty input is the operation's ErrConversionSyntax.
func EstimateNewTwosComplement(bytes uint64) (Cost, error) {
	return estimateBinary(bytes, false)
}

func estimateBinary(n uint64, emptyIsZero bool) (Cost, error) {
	if n == 0 {
		if emptyIsZero {
			return Cost{}, nil
		}
		return estimateError(ErrConversionSyntax)
	}
	var t costTally
	u, w, ok := binaryEnvelope(t.mul(n, 8))
	if !ok || t.overflow || !binaryAdmitted(n, u) {
		return estimateError(ErrInsufficientStorage)
	}
	count := 1 + (u-1)/9 + 1 // Horner's buffer: the envelope's limbs plus one
	return finishCost(&t, Cost{WorkUnits: w, Digits: u, InputDigits: u,
		HeapBytes: publishBytes(&t, u, count)})
}

// EstimateFixed bounds FixedWithOptions and AppendFixed for x with
// fractionalDigits places under the rounding mode: the output bytes
// of the worst layout (the sign kept and a rounding carry wherever the mode
// can raise the magnitude), work = source digits + output bytes, and the
// string's allocation.
func EstimateFixed(x Shape, fractionalDigits uint64, mode RoundingMode) (Cost, error) {
	return estimateDisplay(displayFixed, x, fractionalDigits, mode, "EstimateFixed")
}

// EstimateScientific bounds ScientificWithOptions and AppendScientific for
// significantDigits under the rounding mode.
func EstimateScientific(x Shape, significantDigits uint64, mode RoundingMode) (Cost, error) {
	return estimateDisplay(displayScientific, x, significantDigits, mode, "EstimateScientific")
}

// EstimateEngineering bounds EngineeringWithBudget and AppendEngineering.
func EstimateEngineering(x Shape) (Cost, error) {
	return estimateDisplay(displayEngineering, x, 0, TiesToEven, "EstimateEngineering")
}

func estimateDisplay(kind displayKind, x Shape, places uint64, mode RoundingMode, op string) (Cost, error) {
	if mode > Exact || kind == displayScientific && places == 0 {
		return estimateError(ErrInvalidContext)
	}
	n := max(x.Digits, 1)
	up := mode != Exact && quantizeMayRoundUp(mode, x.Negative)
	// Past every digit only the sticky bit is left, and only a mode that
	// rounds up on it alone can carry; otherwise the result is an unsigned
	// zero.
	stickyUp := mode == AwayFromZero || mode == TowardPositiveInfinity && !x.Negative || mode == TowardNegativeInfinity && x.Negative
	// A carry is not always the longer layout: in Scientific it can raise an
	// exponent of −10 to −9 (one byte shorter), so both outcomes of a
	// possible carry are laid out and the larger is kept.
	size := func(carry bool) (uint64, bool) {
		// A zero renders as a zero at any exponent.
		p := displayPlan{kind: kind, n: n, negative: x.Negative && x.Digits != 0, zero: x.Digits == 0}
		round := func(cut uint64) error {
			if cut >= n {
				p.count = 1
				if carry && (cut == n && up || stickyUp) {
					p.carry = true
				} else {
					p.zero, p.negative = true, false
				}
				return nil
			}
			p.keep, p.count = n-cut, n-cut
			if carry && up {
				p.carry, p.count = true, n-cut+1
			}
			return nil
		}
		if err := p.layout(x.Exponent, places, Budget{}, op, round); err != nil {
			return 0, false
		}
		return p.size, true
	}
	carried, ok1 := size(true)
	plain, ok2 := size(false)
	if !ok1 || !ok2 {
		return estimateError(ErrInsufficientStorage)
	}
	var t costTally
	out := max(carried, plain)
	return finishCost(&t, Cost{WorkUnits: t.add(n, out), OutputBytes: out, HeapBytes: allocBound(&t, out)})
}

var (
	// errorBytes is the one *Error object a refusal allocates.
	errorBytes = uint64(reflect.TypeFor[Error]().Size())
)

// textErrorBytes bounds a text refusal's allocation: a *Error with a
// copy of up to n input bytes (a syntax or range error of byte input), or
// an *Error.
func textErrorBytes(t *costTally, n uint64) uint64 {
	return t.add(allocBound(t, errorBytes), allocBound(t, n))
}

// textCap applies a budget's digit cap to a digit bound: beyond the cap
// the call refuses before allocating, so the cap bounds what it consumes.
func textCap(digits, limit uint64) uint64 {
	if limit != 0 {
		return min(digits, limit)
	}
	return digits
}

// estimateParse is EstimateParse at precision 0.
func estimateParse(inputBytes uint64, budget textLimits) (Cost, error) {
	var t costTally
	n := inputBytes
	digits := textCap(max(n, 1), budget.MaxDigits)
	count := 1 + (digits-1)/9
	heap := max(publishBytes(&t, digits, count), textErrorBytes(&t, n))
	return finishCost(&t, Cost{Digits: digits, InputBytes: n, HeapBytes: heap})
}

// EstimateParseToExponent bounds ParseToExponentWithBudget at target. The
// text decides the pad, so the retained digits are bounded by the input
// (inputBytes) plus the largest pad an int32 exponent allows (MaxInt32 −
// target), or by the budget's digit cap; a rounding carry adds one digit.
// HeapBytes covers the retained scratch above the 48-limb stack and the
// published copy.
func EstimateParseToExponent(inputBytes uint64, target int32, budget Budget) (Cost, error) {
	var t costTally
	n := uint64(max(inputBytes, 0))
	total := t.add(n, uint64(int64(1<<31-1)-int64(target)))
	total = textCap(total, budget.MaxDigits)
	digits := textCap(t.add(total, 1), budget.MaxDigits)
	return parseRoundingCost(&t, n, total, digits)
}

// EstimateParse bounds ParseWithContext for inputBytes of text under the
// context's budget. At precision 0 (Parse) every byte may be a significant
// digit, so the result has at most inputBytes digits, or the budget's digit
// cap, beyond which the call refuses before allocating; parsing has no work
// axis, its time being O(input bytes + result digits). At precision p the
// result has at most min(p, inputBytes) digits from at most that many
// retained digits, or p digits under guards, whose overflow publishes p
// nines. HeapBytes also covers a refusal's error value, including the copy
// a syntax error of byte input makes.
func EstimateParse(inputBytes uint64, ctx Context) (Cost, error) {
	budget := ctx.Budget()
	if ctx.precision == 0 {
		return estimateParse(inputBytes, budget.text())
	}
	var t costTally
	n := inputBytes
	// A guarded overflow publishes p nines whatever the literal's length, as
	// contextEstimate assumes for the arithmetic forms.
	result := min(uint64(ctx.precision), max(n, 1))
	if ctx.guarded {
		result = uint64(ctx.precision)
	}
	retained := textCap(min(uint64(ctx.precision), max(n, 1)), budget.MaxDigits)
	digits := textCap(result, budget.MaxDigits)
	c, err := parseRoundingCost(&t, n, retained, digits)
	if err != nil {
		return c, err
	}
	// A zero literal takes the Parse path.
	bare, _ := estimateParse(inputBytes, budget.text())
	c.HeapBytes = max(c.HeapBytes, bare.HeapBytes)
	return c, nil
}

// parseRoundingCost is the parse-to-target cost of retaining total digits
// and publishing at most digits.
func parseRoundingCost(t *costTally, n, total, digits uint64) (Cost, error) {
	count := 1 + (max(total, 1)-1)/9
	var heap uint64
	if count+1 > divStackLimbs {
		heap = allocBound(t, t.mul(4, count+1))
	}
	resultCount := 1 + (max(digits, 1)-1)/9
	heap = t.add(heap, publishBytes(t, digits, resultCount))
	heap = max(heap, textErrorBytes(t, n))
	return finishCost(t, Cost{Digits: digits, InputBytes: n, HeapBytes: heap})
}

// EstimateParseJSON bounds ParseJSONWithBudget for rawBytes of JSON: the
// quoted form's decode buffer (only when it has escapes), at most rawBytes
// digits, and a refusal's error value.
func EstimateParseJSON(rawBytes uint64, budget Budget) (Cost, error) {
	var t costTally
	c, err := estimateParse(rawBytes, budget.text())
	if err != nil {
		return c, err
	}
	c.HeapBytes = t.add(c.HeapBytes, allocBound(&t, rawBytes))
	return finishCost(&t, c)
}

// EstimateScan bounds ScanWithBudget for src, which the caller already holds
// (src does not escape): text by its length (work = bytes, as text parsing
// charges), any integer kind by its digits, float64 and float32 by their
// exact expansion, math/big integers and rationals by their existing
// conversion plans and minimal magnitude-byte counts, and a decompose source
// by budget.MaxInputBytes; a decompose source without a byte cap has no
// finite bound, because its own Decompose decides the length, and foreign
// Decompose work and allocation are outside every Decimal bound. SQL NULL
// costs nothing; an unsupported kind or a non-finite float is
// ErrConversionSyntax.
func EstimateScan(src any, budget Budget) (Cost, error) {
	parse := textLimits{MaxDigits: budget.MaxDigits}
	var n uint64
	switch s := src.(type) {
	case big.Int:
		return estimateScanBigInt(&s)
	case *big.Int:
		return estimateScanBigInt(s)
	case big.Rat:
		return estimateScanBigRat(&s)
	case *big.Rat:
		return estimateScanBigRat(s)
	case big.Float, *big.Float:
		return estimateError(ErrConversionSyntax)
	case nil:
		return Cost{}, nil
	case string:
		n = uint64(len(s))
	case []byte:
		n = uint64(len(s))
	case float64:
		return estimateScanFloat64(s)
	case float32:
		return estimateScanFloat64(float64(s))
	case decimalDecomposer:
		if budget.MaxInputBytes == 0 {
			return estimateError(ErrInsufficientStorage)
		}
		c, err := EstimateCompose(budget.MaxInputBytes)
		if err != nil {
			return c, err
		}
		c.InputBytes = budget.MaxInputBytes
		return c, nil
	default:
		if _, magnitude, ok := integerSource(src); ok {
			return Cost{WorkUnits: 1, Digits: uint64(wordDigits(magnitude))}, nil
		}
		return estimateError(ErrConversionSyntax)
	}
	c, err := estimateParse(n, parse)
	if err != nil {
		return c, err
	}
	c.WorkUnits = n
	return c, nil
}

// estimateScanFloat64 bounds a binary64 source by its exact expansion.
func estimateScanFloat64(f float64) (Cost, error) {
	if float64Nonfinite(f) {
		return estimateError(ErrConversionSyntax)
	}
	_, m, e := binary64Parts(f)
	if m == 0 {
		return Cost{}, nil
	}
	var buf [binary64Limbs]uint32
	limbs, _ := expandDyadic(&buf, m, e)
	digits := limbsDigits(limbs)
	var t costTally
	count := 1 + (digits-1)/9
	return finishCost(&t, Cost{WorkUnits: binary64Passes(e) * binary64Limbs, Digits: digits, HeapBytes: publishBytes(&t, digits, count)})
}

// EstimateRoundToPrecision bounds RoundToPrecisionWithContext, which is
// context addition of a zero at the value's exponent: the one-nonzero Add
// base B = d with the finisher's 2N + 1, N = min(p, d) (or p when guards make
// an overflow reachable). A zero value charges as one digit.
func EstimateRoundToPrecision(x Shape, ctx Context) (Cost, error) {
	const op = "EstimateRoundToPrecision"
	d := max(x.Digits, 1)
	if ctx.precision == 0 {
		// The identity: an exact Add of a zero at the same exponent, B = W =
		// d.
		return finishCost(new(costTally), Cost{WorkUnits: d, Digits: d, HeapBytes: 0})
	}
	adjusted := int64(x.Exponent) + int64(d) - 1
	return contextEstimate(d, d, adjusted+1, ctx, op)
}

// EstimateRoundToMultiple bounds RoundToMultipleWithBudget of x to the
// multiple m: the DivToExponent estimate of x by m's coefficient at m's
// exponent, completed with N_r quotient digits, plus the Mul charge of r·m
// over the digit envelope N_r + digits(m). A zero, negative or zero-digit m
// is the operation's ErrInvalidOperation.
func EstimateRoundToMultiple(x, m Shape) (Cost, error) {
	const op = "EstimateRoundToMultiple"
	if m.Digits == 0 || m.Negative {
		return estimateError(ErrInvalidOperation)
	}
	if x.Digits == 0 {
		return Cost{WorkUnits: 4, Digits: 1}, nil // zero at m's exponent
	}
	quotient, err := EstimateDivToExponent(x, Shape{Digits: m.Digits}, m.Exponent)
	if err != nil {
		return Cost{}, err
	}
	var t costTally
	digits := t.add(quotient.Digits, m.Digits)
	mul, ok := mulWorkCharge(quotient.Digits, m.Digits, digits)
	if !ok {
		t.overflow = true
	}
	work := t.add(quotient.WorkUnits, mul)
	if _, err := arithmeticLimbCount(digits, op); err != nil {
		return estimateError(ErrInsufficientStorage)
	}
	count := 1 + (digits-1)/9
	heap := t.add(quotient.HeapBytes, publishBytes(&t, digits, count))
	return finishCost(&t, Cost{WorkUnits: work, Digits: digits, HeapBytes: heap})
}

// EstimateSum bounds SumWithBudget over operands of the given aggregate shape
// (ShapeOfSum builds it in one pass): W = k + Σdᵢ + 2·t(L) and N = L, the
// digit envelope amax − emin + 1 + ⌈log10 k⌉ (1 when every operand is zero),
// with the accumulators' scratch beyond the stack and the published result in
// HeapBytes. It is O(1).
func EstimateSum(s SumShape) (Cost, error) {
	const op = "EstimateSum"
	if s.Count <= 0 {
		return Cost{}, nil
	}
	envelope, ok := sumEnvelope(s, true)
	if !ok {
		return estimateError(ErrInsufficientStorage)
	}
	work, ok := sumCharges(s, envelope)
	if !ok {
		return estimateError(ErrInsufficientStorage)
	}
	width, _, err := sumScratch(envelope, op)
	if err != nil {
		return estimateError(ErrInsufficientStorage)
	}
	var t costTally
	var heap uint64
	count := 1 + (envelope-1)/9
	if width > sumStackLimbs {
		// Beyond the stack: the accumulators, and the result slice that
		// publishOwned adopts (counted once, in publishBytes).
		heap = allocBound(&t, t.mul(16, width))
		count = width
	}
	heap = t.add(heap, publishBytes(&t, envelope, count))
	return finishCost(&t, Cost{WorkUnits: work, Digits: envelope, HeapBytes: heap})
}

// estimateSqrt is EstimateSqrt at precision 0.
func estimateSqrt(x Shape) (Cost, error) {
	const op = "EstimateSqrt"
	if x.Digits != 0 && x.Negative {
		return estimateError(ErrInvalidOperation)
	}
	if x.Digits == 0 {
		return Cost{WorkUnits: 1, Digits: 1}, nil
	}
	d := x.Digits
	if x.Exponent%2 != 0 {
		d++
	}
	p := newSqrtPlan(d, 0)
	charge, ok := sqrtCharge(p.s, p.r)
	if d < x.Digits || !ok {
		return estimateError(ErrInsufficientStorage)
	}
	return sqrtEstimate(charge, p.s, p.r, p.r, p.r, op)
}

// EstimateSqrt bounds SqrtWithContext: the precharge B = d + I·D + t(p+1)²
// (I Newton iterations, each one division of charge D) with W = B + 2p + 1
// and N = p, attained by every inexact root; HeapBytes
// covers the Newton scratch of the call's own plan beyond the stack and a
// p-digit result. zero costs one digit and W = 4.
//
// At precision 0 it bounds the exact Sqrt: with d′ the digits of the
// parity-adjusted coefficient (one more than x's for an odd exponent) and R =
// ⌈d′/2⌉, W = B = d′ + I·D + t(R)² and N = R, attained by every perfect
// square of the shape; HeapBytes covers the Newton scratch beyond the stack
// and the published root. A negative nonzero shape is the operation's
// ErrInvalidOperation, and zero costs one digit and one unit.
func EstimateSqrt(x Shape, ctx Context) (Cost, error) {
	const op = "EstimateSqrt"
	if ctx.precision == 0 {
		return estimateSqrt(x)
	}
	if x.Digits != 0 && x.Negative {
		return estimateError(ErrInvalidOperation)
	}
	if x.Digits == 0 {
		return Cost{WorkUnits: 4, Digits: 1}, nil
	}
	p := uint64(ctx.precision)
	charge, ok := sqrtCharge(x.Digits, p+1)
	if !ok {
		return estimateError(ErrInsufficientStorage)
	}
	work, ok := contextFinalCharge(charge, p)
	if !ok {
		return estimateError(ErrInsufficientStorage)
	}
	tPrime, _ := sqrtContextTarget(x.Digits, x.Exponent, &ctx)
	plan := newSqrtPlan(x.Digits, int64(x.Exponent)-2*tPrime)
	if plan.s == 0 {
		// Every digit lies below Etiny: no scratch. The result has at most
		// one digit, so the p-digit publication bound is slack.
		var t costTally
		return finishCost(&t, Cost{WorkUnits: work, Digits: p, HeapBytes: publishBytes(&t, p, 1+(p-1)/9)})
	}
	return sqrtEstimate(work, plan.s, plan.r, p, p+1, op)
}

// sqrtEstimate completes a Sqrt estimate from its work and the planned
// s-digit N with an r-digit root publishing n digits, admitted physically
// as the operation admits it (admit result digits).
func sqrtEstimate(work, s, r, n, admit uint64, op string) (Cost, error) {
	var t costTally
	total, ok := newSqrtLayout(s, r).total()
	if !ok || !divAdmitted(total, admit) {
		return estimateError(ErrInsufficientStorage)
	}
	var heap uint64
	if total > sqrtStackLimbs {
		heap = allocBound(&t, t.mul(4, total))
	}
	if _, err := arithmeticLimbCount(n, op); err != nil {
		return estimateError(ErrInsufficientStorage)
	}
	heap = t.add(heap, publishBytes(&t, n, 1+(n-1)/9))
	return finishCost(&t, Cost{WorkUnits: work, Digits: n, HeapBytes: heap})
}

// estimatePow is EstimatePow at precision 0.
func estimatePow(x Shape, n int32) (Cost, error) {
	switch {
	case n == 0:
		return Cost{WorkUnits: 1, Digits: 1}, nil
	case x.Digits == 0:
		return powZeroEstimate(x, n, 1)
	case n == 1:
		return EstimateRoundToPrecision(x, Context{})
	case n == -1:
		return estimateDiv(Shape{Digits: 1}, x)
	}
	m, d := powMagnitude(n), x.Digits
	var t costTally
	if n > 0 {
		if e := int64(m) * int64(x.Exponent); e < math.MinInt32 || e > math.MaxInt32 {
			return estimateError(ErrExponentRange)
		}
		plan := newPowPlan(powLogFull, d, m)
		total := t.add(t.mul(2, plan.limbs+1), digitLimbs(d))
		if !plan.ok || t.overflow || !divAdmitted(total, plan.hi) {
			return estimateError(ErrInsufficientStorage)
		}
		heap := powScratchBytes(&t, total)
		heap = t.add(heap, publishBytes(&t, plan.hi, digitLimbs(plan.hi)))
		return finishCost(&t, Cost{WorkUnits: t.add(plan.charge, digitLimbs(d)), Digits: plan.hi, HeapBytes: heap})
	}
	var worst Cost
	for _, five := range []bool{false, true} {
		test, ok1 := powPredicateCharge(d, five)
		exponent, ok2 := arithmeticMul(powPredicateMax(d, five), m)
		base := uint64(5) // c = 2^a gives 5^(a·m)
		if five {
			base = 2
		}
		plan := newPowPlanBound(newPowLog(base*1_000_000_000_000_000_000, true), 1, exponent)
		copyLimbs := digitLimbs(d)
		total := t.mul(2, plan.limbs+1)
		if !ok1 || !ok2 || !plan.ok || t.overflow || !divAdmitted(total, plan.hi) || !divAdmitted(copyLimbs, 0) {
			return estimateError(ErrInsufficientStorage)
		}
		heap := t.add(powScratchBytes(&t, copyLimbs), powScratchBytes(&t, total), publishBytes(&t, plan.hi, digitLimbs(plan.hi)))
		worst = worst.Max(Cost{WorkUnits: t.add(digitLimbs(d), test, plan.charge), Digits: plan.hi, HeapBytes: heap})
	}
	return finishCost(&t, worst)
}

// EstimatePow bounds PowWithContext: the worst case is the scan to find z
// (t(d)), every truncated level from w = p+1+⌈log10(2|n|)⌉+2, doubling while
// w < |n|·d, then the exact fallback (the plan at k·d digits per partial
// power, plus one reciprocal division for n < 0) and the finisher's 2p+1,
// with N = p. It is attained by the all-nines coefficient of the shape when
// every level fails to decide, but for the scan's slack t(d) − 1; a typical
// call decides at the first level. A zero x costs one digit and W = 4, as does n = 0 unless guards with Emax <
// 0 make 1 overflow to the largest finite value, which costs p digits and W
// = 2p + 2; |n| = 1 is EstimateRoundToPrecision or EstimateDiv.
//
// At precision 0 it bounds the exact Pow. For n ≥ 2 the digits are bounded by
// n·d, d the shape's full digit count (trailing zeros included), which is at
// least Dhi + n·z; the work is the exact plan with every partial power c^k at
// k·d digits, which covers the n·z zeros because the last step alone grows by
// n·z; t(d) more bounds the ⌊z/9⌋+1 limbs read to find z. The digits are
// attained by the all-nines coefficient of the shape, and so is the work but
// for its one-limb scan (slack t(d) − 1). For n ≤ −2 the value is 5^(a·|n|)
// or 2^(b·|n|) when the reciprocal terminates, so the bound is the test's
// charge plus the plan of 5^(a_max·|n|), a_max = ⌊d·3.322⌋, whose digits
// exceed |n|·d (8⁻² = 0.015625); a non-terminating value is refused, which
// the estimate does not predict; the scan adds t(d). |n| ≤ 1 is
// EstimateRoundToPrecision with Context{} (n = 1) or EstimateDiv of one by x
// (n = −1), n = 0 costs one digit and one unit, and a zero x is
// ErrDivisionByZero for n < 0.
func EstimatePow(x Shape, n int32, ctx Context) (Cost, error) {
	switch {
	case ctx.precision == 0:
		return estimatePow(x, n)
	case n == 0:
		if ctx.guarded && ctx.guards.Emax < 0 {
			// 1 overflows: the finisher publishes Bmax of p digits.
			var t costTally
			work, ok := contextFinalCharge(1, uint64(ctx.precision))
			if !ok {
				return estimateError(ErrInsufficientStorage)
			}
			p := uint64(ctx.precision)
			return finishCost(&t, Cost{WorkUnits: work, Digits: p, HeapBytes: publishBytes(&t, p, digitLimbs(p))})
		}
		return Cost{WorkUnits: 4, Digits: 1}, nil
	case x.Digits == 0:
		return powZeroEstimate(x, n, 4)
	case n == 1:
		return EstimateRoundToPrecision(x, ctx)
	case n == -1:
		return EstimateDiv(Shape{Digits: 1}, x, ctx)
	}
	m, d, p := powMagnitude(n), x.Digits, uint64(ctx.precision)
	reciprocal := n < 0
	var t costTally
	top := t.mul(m, d)
	work, heap := digitLimbs(d), uint64(0) // the trailing-zero scan
	for w := p + 1 + powGuard(m); w < top && !t.overflow; w = t.mul(w, 2) {
		level, ok := powLevelCharge(w, m, p, reciprocal)
		limbs := powLevelLimbs(w, p, reciprocal)
		if !ok || !reciprocal && !divAdmitted(limbs, p+1) {
			return estimateError(ErrInsufficientStorage)
		}
		work = t.add(work, level)
		heap = t.add(heap, powScratchBytes(&t, limbs))
	}
	plan := newPowPlan(powLogFull, d, m)
	work = t.add(work, plan.charge)
	if reciprocal {
		div, ok := powDivCharge(plan.hi, p)
		if !ok {
			t.overflow = true
		}
		work = t.add(work, div)
	}
	limbs := powExactLimbs(plan, digitLimbs(d), p, p, reciprocal)
	if !plan.ok || t.overflow {
		return estimateError(ErrInsufficientStorage)
	}
	if reciprocal {
		// Power, optional exact-first probe and full division are separate
		// objects. Count cumulative allocations even when probe scratch is
		// no longer live at fallback. A shape alone cannot declare every
		// value refused because a worst-case power, level or division is
		// huge: trailing-zero stripping can skip those arenas entirely.
		power := t.add(t.mul(2, plan.limbs+1), digitLimbs(d))
		num, den, quot := powDivLimbs(plan.hi, p)
		division := t.add(num, den, quot)
		k := t.add(t.mul(plan.hi, 3322), 999) / 1000
		probeSource := divSource{dx: 1, dy: plan.hi}
		var probe uint64
		if k <= math.MaxInt64 {
			probePlan := probeSource.plan(-int64(k))
			if probePlan.ok {
				probe = probeSource.scratchTotal(probePlan)
			}
		}
		heap = t.add(heap, powScratchBytes(&t, power), divScratchCost(&t, division), divScratchCost(&t, probe))
	} else {
		if !divAdmitted(limbs, p+1) {
			return estimateError(ErrInsufficientStorage)
		}
		heap = t.add(heap, powScratchBytes(&t, limbs))
	}
	heap = t.add(heap, publishBytes(&t, p, digitLimbs(p)))
	work, ok := contextFinalCharge(work, p)
	if !ok {
		return estimateError(ErrInsufficientStorage)
	}
	return finishCost(&t, Cost{WorkUnits: work, Digits: p, HeapBytes: heap})
}

// powZeroEstimate is a zero base: ErrDivisionByZero for n < 0, the
// exponent n·e checked, and otherwise one digit at W = work.
func powZeroEstimate(x Shape, n int32, work uint64) (Cost, error) {
	if n < 0 {
		return estimateError(ErrDivisionByZero)
	}
	if e := int64(n) * int64(x.Exponent); e < math.MinInt32 || e > math.MaxInt32 {
		return estimateError(ErrExponentRange)
	}
	return Cost{WorkUnits: work, Digits: 1}, nil
}

// divScratchCost includes each separately allocated division arena.
func divScratchCost(t *costTally, limbs uint64) uint64 {
	if limbs <= divStackLimbs {
		return 0
	}
	return allocBound(t, t.mul(4, limbs))
}

// powScratchBytes is the heap of one Pow scratch buffer of limbs limbs:
// nothing when it fits the stack array.
func powScratchBytes(t *costTally, limbs uint64) uint64 {
	if limbs <= powStackLimbs {
		return 0
	}
	return allocBound(t, t.mul(4, limbs))
}

// estimateScanBigInt uses the same checked source metadata as Scan.
func estimateScanBigInt(x *big.Int) (Cost, error) {
	n, code := scanBigIntBits(x)
	if code != 0 {
		return estimateError(code)
	}
	c, err := EstimateFromBigInt(n)
	c.InputBytes = (n + 7) / 8
	return c, err
}

// estimateScanBigRat uses the held source's exact plan, so source twos
// and definite exponent-domain refusals match Scan before the factor loop.
func estimateScanBigRat(r *big.Rat) (Cost, error) {
	bn, bd, code := scanBigRatBits(r)
	if code != 0 {
		return estimateError(code)
	}
	inputBytes := (bn+7)/8 + (bd+7)/8
	if bn == 0 {
		c := ratZeroCost()
		c.InputBytes = inputBytes
		return c, nil
	}
	s, _ := readRat(r)
	e := s.exactPlan()
	if e.a-e.shared > 1<<31 {
		return estimateError(ErrExponentRange)
	}
	if !e.ok || !ratAdmitted(e.operandWords, e.quotientBound+1) {
		return estimateError(ErrInsufficientStorage)
	}
	c, err := ratCost(e.charge, []uint64{e.operandWords}, e.quotientBound)
	c.InputBytes = inputBytes
	return c, err
}

// EstimateQuo bounds QuoWithContext. It predicts ErrDivisionImpossible when
// δ exceeds the precision and ErrInvalidOperation for a guard that every
// such quotient fails.
//
// At precision 0 it bounds the exact Quo: W = B + C + 2Q + 1 with Q = δ+1 for
// δ = (dx+ex) − (dy+ey) ≥ 0, where the quotient has δ or δ+1 digits.
func EstimateQuo(x, y Shape, ctx Context) (Cost, error) {
	return estimateIntDiv(x, y, ctx, intDivQuo)
}

// EstimateRem bounds RemWithContext.
//
// At precision 0 it bounds the exact Rem: its N is the path's result-digit
// envelope, since the remainder's length depends on its value.
func EstimateRem(x, y Shape, ctx Context) (Cost, error) {
	return estimateIntDiv(x, y, ctx, intDivRem)
}

// EstimateRemNear bounds RemNearWithContext.
//
// At precision 0 it bounds the exact RemNear.
func EstimateRemNear(x, y Shape, ctx Context) (Cost, error) {
	return estimateIntDiv(x, y, ctx, intDivRemNear)
}

// estimateIntDiv runs the operations' planner over shapes. Only δ = 0 needs
// both zero- and nonzero-quotient paths; there the estimate is their per-axis
// maximum. At δ = p, refusal identity can also depend on the values.
// Predicted refusals follow the operation's stage order: quotient fit,
// guards, then resources.
func estimateIntDiv(x, y Shape, ctx Context, op intDivOp) (Cost, error) {
	switch {
	case y.Digits == 0 && x.Digits == 0:
		return estimateError(ErrDivisionUndefined)
	case y.Digits == 0:
		return estimateError(ErrDivisionByZero)
	}
	t := int64(min(x.Exponent, y.Exponent))
	if op == intDivQuo {
		t = 0
	}
	if x.Digits == 0 {
		if !intDivStoredRange(t, ctx) {
			return estimateError(ErrInvalidOperation)
		}
		return Cost{WorkUnits: 4, Digits: 1}, nil
	}
	if x.Digits > 1<<62 || y.Digits > 1<<62 {
		return estimateError(ErrInsufficientStorage) // beyond any address space; keeps δ in int64
	}
	s := intDivShape{dx: x.Digits, dy: y.Digits, ex: x.Exponent, ey: y.Exponent}
	delta := s.delta()
	p := int64(ctx.precision)
	if p != 0 && delta > p {
		return estimateError(ErrDivisionImpossible)
	}
	b, ok := intDivPrecharge(s.dx, s.dy, false)
	if !ok {
		return estimateError(ErrInsufficientStorage)
	}
	if !intDivStoredRange(t, ctx) || ctx.guarded && op == intDivQuo && delta >= 1 && delta-1 > int64(ctx.guards.Emax) {
		if p == 0 || delta < p {
			return estimateError(ErrInvalidOperation)
		}
		// At δ = p every value refuses at quotient fit or at this guard,
		// with value-dependent error identity. Only B and one error are
		// reachable; do not plan an arena or predict its physical refusal.
		var tally costTally
		return Cost{WorkUnits: b, HeapBytes: allocBound(&tally, errorBytes)}, nil
	}
	var zeroCost, quotientCost Cost
	var zeroErr, quotientErr error = ErrInsufficientStorage, ErrInsufficientStorage
	if delta <= 0 {
		zeroCost, zeroErr = intDivPathCost(planIntDiv(op, s, true, 1, intDivForceNone), b)
	}
	if delta >= 0 {
		q := uint64(delta) + 1
		if p != 0 {
			q = min(q, uint64(p)) // Q = p+1 is refused at B
		}
		plan := planIntDiv(op, s, false, q, intDivForceNone)
		if p != 0 && delta == p && (!plan.ok || !divAdmitted(plan.arena, plan.nEnv)) {
			// Fitting quotients have exactly p digits here. They refuse
			// before allocation, while larger quotients fail earlier with
			// DivisionImpossible. The error identity depends on the value.
			var tally costTally
			return Cost{WorkUnits: b, HeapBytes: allocBound(&tally, errorBytes)}, nil
		}
		quotientCost, quotientErr = intDivPathCost(plan, b)
	}
	switch {
	case zeroErr == nil && quotientErr == nil:
		return zeroCost.Max(quotientCost), nil
	case zeroErr == nil:
		return zeroCost, nil
	case quotientErr == nil:
		return quotientCost, nil
	}
	return estimateError(ErrInsufficientStorage)
}

// intDivPathCost is one path's W, N envelope and heap: the arena above the
// 48-limb stack and the published result. A q = 0 Rem with ex ≤ ey returns
// the operand and publishes nothing.
func intDivPathCost(plan intDivPlan, b uint64) (Cost, error) {
	if !plan.ok || !divAdmitted(plan.arena, plan.nEnv) {
		return Cost{}, ErrInsufficientStorage
	}
	w, ok := intDivWork(b, plan.c, plan.nEnv)
	if !ok {
		return Cost{}, ErrInsufficientStorage
	}
	var t costTally
	var heap uint64
	if plan.arena > divStackLimbs {
		heap = allocBound(&t, t.mul(4, plan.arena))
	}
	heap = t.add(heap, publishBytes(&t, plan.nEnv, digitLimbs(plan.nEnv)))
	if t.overflow {
		return Cost{}, ErrInsufficientStorage
	}
	return Cost{WorkUnits: w, Digits: plan.nEnv, HeapBytes: heap}, nil
}

// estimateFMA bounds FMAWithContext at precision 0, the exact x·y + z: Mul's
// charge t(dx)·t(dy)+dx+dy (1 for a zero factor) plus EstimateAdd's charge
// and digit bound with the product as a (dx+dy)-digit operand at ex+ey, and
// HeapBytes for the product scratch beyond the stack and the published sum.
// The work is attained by every product of dx+dy digits that does not cancel
// z. An exponent sum outside int32 is the operation's ErrExponentRange.
func estimateFMA(x, y, z Shape) (Cost, error) {
	const op = "EstimateFMA"
	e := int64(x.Exponent) + int64(y.Exponent)
	if e < math.MinInt32 || e > math.MaxInt32 {
		return estimateError(ErrExponentRange)
	}
	var t costTally
	digits, pre, scratch, ok := fmaEstimateProduct(&t, x, y, op)
	if !ok {
		return estimateError(ErrInsufficientStorage)
	}
	product := reduceSpan{lo: digits, hi: digits, exponent: e, negative: x.Negative != y.Negative}
	sum, err := estimateAddSubSpans(product, spanOf(z), op)
	if err != nil {
		return sum, err
	}
	sum.WorkUnits = t.add(sum.WorkUnits, pre)
	sum.HeapBytes = t.add(sum.HeapBytes, scratch)
	return finishCost(&t, sum)
}

// EstimateFMA bounds FMAWithContext: Mul's charge plus the context Add/Sub
// estimate over the product and addend as the context planner reduces them,
// the product being a span of dx+dy−1 or dx+dy digits at the int64 exponent
// ex+ey and planned at dx+dy; the finisher 2N+1; and HeapBytes for the
// product scratch (unless the planner replaces the product, which is then
// never built) and an N-digit result. Precision 0 is the exact x·y + z. An
// exact zero whose exponent min(ex+ey, ez) leaves int32 is the operation's
// ErrExponentRange.
func EstimateFMA(x, y, z Shape, ctx Context) (Cost, error) {
	const op = "EstimateFMA"
	if ctx.precision == 0 {
		return estimateFMA(x, y, z)
	}
	e := int64(x.Exponent) + int64(y.Exponent)
	if (x.Digits == 0 || y.Digits == 0) && z.Digits == 0 {
		if ideal := min(e, int64(z.Exponent)); ideal < math.MinInt32 || ideal > math.MaxInt32 {
			return estimateError(ErrExponentRange)
		}
	}
	var t costTally
	digits, pre, scratch, ok := fmaEstimateProduct(&t, x, y, op)
	if !ok {
		return estimateError(ErrInsufficientStorage)
	}
	product := reduceSpan{exponent: e, negative: x.Negative != y.Negative}
	if x.Digits != 0 && y.Digits != 0 {
		product.lo, product.hi = digits-1, digits
	}
	rp, rz := contextReduceSpans(product, spanOf(z), ctx)
	if rp != product {
		scratch = 0
	}
	c, err := contextAddSubEstimate(rp, rz, pre, ctx, op)
	if err != nil {
		return c, err
	}
	c.HeapBytes = t.add(c.HeapBytes, scratch)
	return finishCost(&t, c)
}

// fmaEstimateProduct is fmaProductPlan over shapes, with the heap bytes of
// the product scratch the kernel allocates beyond fmaStackLimbs.
func fmaEstimateProduct(t *costTally, x, y Shape, op string) (digits, pre, heap uint64, ok bool) {
	digits, pre, ok = fmaProductPlan(x.Digits, y.Digits)
	if !ok || x.Digits == 0 || y.Digits == 0 {
		return digits, pre, 0, ok
	}
	count := t.add(1+(x.Digits-1)/9, 1+(y.Digits-1)/9)
	if _, err := arithmeticPhysicalLimbCount(count, op); err != nil || t.overflow {
		return 0, 0, 0, false
	}
	if count > fmaStackLimbs {
		heap = allocBound(t, t.mul(4, count))
	}
	return digits, pre, heap, true
}

// estimateAddSubSpans is the Add/Sub estimate over spans with int64 exponents
// and effective signs, so FMA can pass its product.
func estimateAddSubSpans(x, y reduceSpan, op string) (Cost, error) {
	var t costTally
	work, digits := addSubTariffSpan(&t, x, y)
	count := 1 + (digits-1)/9
	if t.overflow {
		return estimateError(ErrInsufficientStorage)
	}
	if _, err := arithmeticLimbCount(digits, op); err != nil {
		return estimateError(ErrInsufficientStorage)
	}
	heap := publishBytes(&t, digits, count)
	return finishCost(&t, Cost{WorkUnits: work, Digits: digits, HeapBytes: heap})
}

// addSubTariffSpan is addSubTariff over spans with int64 exponents and
// effective signs, each planned at its greatest digit count (hi), for FMA's
// product; TestReduceSpansMatchShapes pins it to addSubTariff.
func addSubTariffSpan(t *costTally, x, y reduceSpan) (work, digits uint64) {
	e := min(x.exponent, y.exponent)
	sa, sb := uint64(x.exponent-e), uint64(y.exponent-e)
	dx, dy := max(x.hi, 1), max(y.hi, 1)
	spanX, spanY := t.add(dx, sa), t.add(dy, sb)
	L := max(spanX, spanY)
	var ok bool
	if x.negative == y.negative {
		// Same effective signs: a carry adds a digit only where the aligned
		// spans overlap.
		work, ok = addSubSameCharge(dx, dy, L)
		digits = L
		if sa < spanY && sb < spanX {
			digits = t.add(L, 1)
		}
	} else {
		work, ok = addSubOppositeCharge(dx, dy, L)
		digits = L
	}
	if !ok {
		t.overflow = true
	}
	return work, digits
}

// contextAddSubEstimate is estimateContextAddSub's completion over reduced
// spans with effective signs, for FMA (TestReduceSpansMatchShapes pins it),
// after pre units of prior work (FMA's Mul charge): B is 1 for two zeros, the
// nonzero's aligned span for one zero (a zero is not part of that span), and
// the Add tariff for two nonzero spans.
func contextAddSubEstimate(x, y reduceSpan, pre uint64, ctx Context, op string) (Cost, error) {
	var t costTally
	switch {
	case x.hi == 0 && y.hi == 0:
		// A zero result is never checked against the guards.
		return contextEstimate(t.add(pre, 1), 1, math.MinInt64, ctx, op)
	case x.hi == 0 || y.hi == 0:
		nonzero, zero := x, y
		if x.hi == 0 {
			nonzero, zero = y, x
		}
		span := t.add(nonzero.hi, uint64(nonzero.exponent-min(nonzero.exponent, zero.exponent)))
		base := t.add(pre, span)
		if t.overflow {
			return estimateError(ErrInsufficientStorage)
		}
		// Only a rounding carry raises the nonzero's adjusted exponent.
		return contextEstimate(base, span, nonzero.exponent+int64(nonzero.hi), ctx, op)
	}
	base, digits := addSubTariffSpan(&t, x, y)
	base = t.add(base, pre)
	if t.overflow {
		return estimateError(ErrInsufficientStorage)
	}
	// B is the bare tariff without its planned result digit; the context path
	// charges the same base.
	adjusted := max(x.exponent+int64(x.hi)-1, y.exponent+int64(y.hi)-1)
	return contextEstimate(base, digits, adjusted+2, ctx, op)
}

// EvaluationBound bounds one adaptive attempt under a supplied finite unit
// quota. It bounds success or refusal, not the cost of convergence. It has no
// attainment guarantee or admitting-budget helper and is not Cost. HeapBytes
// bounds cumulative library allocation, including discarded scratch and one
// outer error object, not RSS or later caller formatting of the error.
type EvaluationBound struct {
	// Units bounds the evaluation units the attempt can charge.
	Units uint64
	// HeapBytes bounds the attempt's cumulative library allocation.
	HeapBytes uint64
}

// BoundEvaluation bounds one attempt of any adaptive function (Exp, Ln, Log10,
// PowDecimal and the trigonometric and hyperbolic functions) under budget.
// For positive W=budget.MaxWork it returns Units W and HeapBytes W+E, where E
// bounds the one *Error a refusal allocates on this target/toolchain. Result storage, nested calls and all retries belong in W.
// A digit cap without a positive unit quota supplies no finite attempt bound.
//
// The query allocates nothing. Zero units returns ErrEvaluationBudgetRequired;
// unrepresentable W+E returns ErrEvaluationBoundOverflow. Neither error predicts
// an operand's outcome or invalidates a supplied operation budget.
func BoundEvaluation(budget Budget) (EvaluationBound, error) {
	if budget.MaxWork == 0 {
		return EvaluationBound{}, ErrEvaluationBudgetRequired
	}
	var tally costTally
	e := allocBound(&tally, errorBytes)
	heap := tally.add(budget.MaxWork, e)
	if tally.overflow {
		return EvaluationBound{}, ErrEvaluationBoundOverflow
	}
	return EvaluationBound{Units: budget.MaxWork, HeapBytes: heap}, nil
}

// limits is the arithmetic families' view of a Budget: the result-digit and
// work axes, small enough to travel in registers through the hot kernels.
type limits struct {
	MaxDigits uint64
	MaxWork   uint64
}

// admits reports whether l certainly admits a call that the general path
// charges at most work units and at most digits digits at every admission:
// no cap, or a cap at or above the bound, on each axis. A fast path that
// proves such bounds for its shape may then serve a budgeted call, since an
// admitted budget never changes a result.
func (l limits) admits(digits, work uint64) bool {
	return (l.MaxDigits == 0 || l.MaxDigits >= digits) && (l.MaxWork == 0 || l.MaxWork >= work)
}

// admitsConversion is admits for the integer conversions, which also cap
// the input digits: b certainly admits a conversion whose input and result
// have at most digits digits and whose tariff is at most work.
func (b *Budget) admitsConversion(digits, work uint64) bool {
	return (b.MaxInputDigits == 0 || b.MaxInputDigits >= digits) && (b.MaxDigits == 0 || b.MaxDigits >= digits) && (b.MaxWork == 0 || b.MaxWork >= work)
}

// Bounds of the general charges for operands that fit two machine words, at
// most 39 digits each, which the machine-word paths pass to admits and
// admitsConversion. Each is the largest value the general path tests
// against a budget for the shapes its machine-word path serves. A path
// whose budget falls below its bound may still serve the call by pricing
// it as the general path does.
const (
	// Exact Add/Sub served by inlineAddSub: the aligned span L has at most
	// 39 digits, so a sum plans at most L+1 digits, and the dearest charge
	// is the opposite-sign 2(d1+d2)+L.
	inlineAddSubDigits = 39 + 1
	inlineAddSubWork   = 2*(39+39) + 39

	// A rounded or quantized result, or a quotient, held in two words.
	inlineResultDigits = 39

	// Context Add/Sub: the exponent gap is at most 38, so L is at most 77;
	// the dearest charge is the opposite-sign base 2(d1+d2)+L plus the
	// finisher's 2N+1 for a result of N digits. Operand reduction only
	// shortens an operand and the span.
	inlineContextAddSubWork = 2*(39+39) + 77 + 2*inlineResultDigits + 1

	// Quantize: growing charges the result length; shrinking by fewer
	// digits than the coefficient's d charges d plus a length of at most d.
	inlineQuantizeWork = 39 + 39

	// Division: the numerator has at most 39+38 digits in tn ≤ 9 limbs and
	// the divisor at most 39 digits in n ≤ 5 limbs. The plan charges at
	// most 2(tn−n+1)(n+1) ≤ 60 for the loop, 2(tn+n+1) ≤ 30 for the
	// normalization and 77+39+5 for the reads; publication adds 2N+1.
	inlineDivWork = 60 + 30 + (77 + 39 + 5) + 2*inlineResultDigits + 1

	// Exact division by a one-word divisor: the divisor has at most 20
	// digits in n ≤ 3 limbs, and the plan divides, at ⌈3.322·20⌉ = 67
	// fraction digits, a numerator of at most 39+67 digits in tn ≤ 12
	// limbs. It charges at most 2(tn−n+1)(n+1) = 80 for the loop,
	// 2(tn+n+1) = 32 for the normalization and 106+20+3 for the reads;
	// publication adds 2N+1.
	inlineDivExactWork = 80 + 32 + (106 + 20 + 3) + 2*inlineResultDigits + 1

	// Integer division of operands that align in two words charges
	// B = dx+dy+1, a path charge C and 2N+1. The dearest path is RemNear's
	// comparison of |x| with |y|−|x| under a zero quotient, C = 4(dx+dy)+dx
	// for a dividend padded by at least one digit below a divisor of at
	// most 39, so dx ≤ 38. Every dividing path charges less: at most 42
	// for the kernel's loop and normalization (tn, n ≤ 5), 39+39+5 for its
	// reads, and 3j+6(n+1) ≤ 150 for a split at j ≤ 38 digits.
	inlineIntDivWork = (38 + 39 + 1) + (4*(38+39) + 38) + 2*inlineResultDigits + 1

	// FromRatToExponent of a one-word numerator over a one-word denominator
	// at up to 38 fraction digits: 10^k has at most two 64-bit words, so
	// the scaled numerator has three and the quotient three. The plan
	// charges ⌈4·2²/3⌉+2 for the power, 2 for the scaling, 2(3−1+2)(1+1)
	// for the division, U·⌈U/9⌉ with U = 58 digits for converting the
	// quotient, and 3+1 operand words; publication adds 2N+1. Scaling the
	// denominator instead charges less.
	inlineRatWork = (6 + 2) + 2 + 16 + 58*7 + (3 + 1) + 2*inlineResultDigits + 1

	// BigInt of an inline coefficient whose integer stays inline: at most 39
	// digits in five limbs on each side, and the tariff (a+b)² + (a+b) over
	// the two limb counts.
	inlineBigIntWork = (5+5)*(5+5) + (5 + 5)

	// A binary coefficient of at most 16 bytes: the envelope of 128 bits is
	// U = ⌊128·0.30103⌋+1 digits in five limbs and W = (2·5)² + 2·5.
	inlineBinaryDigits = 39
	inlineBinaryWork   = (2*5)*(2*5) + 2*5

	// Rat of a one-word coefficient of at most 20 digits at −19 ≤ e < 0:
	// the numerator and the denominator 10^j, j ≤ 19, have at most 20
	// digits each. A 20-digit numerator has two 64-bit words and 10^j one,
	// so the tariff is at most (3+3)²+(3+3) for converting three limbs,
	// (19+1)·2 for the factor-5 loop, and ⌈4/3⌉+1 and 1 for the power and
	// its word. A strip of trailing zeros adds 20 but leaves a one-word
	// numerator and j ≤ 18, a loop of at most 19: one unit less in all.
	inlineRatEgressDigits = 20
	inlineRatEgressWork   = (6*6 + 6) + 20*2 + (2 + 1) + 1
)

// arith is b's arithmetic axes.
func (b Budget) arith() limits { return limits{MaxDigits: b.MaxDigits, MaxWork: b.MaxWork} }

// textLimits is the parse family's view of a Budget: input bytes and
// result digits.
type textLimits struct {
	MaxInputBytes uint64
	MaxDigits     uint64
}

// text is b's parse axes.
func (b Budget) text() textLimits {
	return textLimits{MaxInputBytes: b.MaxInputBytes, MaxDigits: b.MaxDigits}
}
