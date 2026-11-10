// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"math"
	"math/bits"
)

// contextPlan describes the exact ideal-exponent result without a result
// coefficient. Its streams can be restarted for read-only preflight and the
// sole admitted publication pass.
type contextPlan struct {
	a, b               coefficientView
	ideal              int64
	sa, sb, groups     uint64
	base               uint64
	add, greaterA, mul bool
	negative, zero     bool
}

type contextGroupStream struct {
	plan             *contextPlan
	index            uint64
	carryLo, carryHi uint64
}

func (s *contextGroupStream) next() (uint32, bool) {
	p := s.plan
	index := s.index
	s.index++
	if !p.mul {
		ad := uint64(alignedLimb(&p.a, p.sa, index))
		bd := uint64(alignedLimb(&p.b, p.sb, index))
		if p.add {
			sum := ad + bd + s.carryLo
			s.carryLo = sum / decimalLimbBase
			return uint32(sum % decimalLimbBase), true
		}
		high, low := ad, bd
		if !p.greaterA {
			high, low = low, high
		}
		if high < low+s.carryLo {
			borrow := s.carryLo
			s.carryLo = 1
			return uint32(high + decimalLimbBase - low - borrow), true
		}
		result := high - low - s.carryLo
		s.carryLo = 0
		return uint32(result), true
	}
	lo, hi := s.carryLo, s.carryHi
	na, nb := uint64(p.a.count), uint64(p.b.count)
	if index < na+nb-1 {
		start := uint64(0)
		if index >= nb {
			start = index - (nb - 1)
		}
		end := min(index, na-1)
		for i := start; i <= end; i++ {
			product := uint64(p.a.limb(int(i))) * uint64(p.b.limb(int(index-i)))
			var carry uint64
			lo, carry = bits.Add64(lo, product, 0)
			hi, carry = bits.Add64(hi, 0, carry)
			if carry != 0 {
				return 0, false
			}
		}
	}
	if hi == 0 {
		// A constant division compiles to a multiply-high.
		s.carryHi, s.carryLo = 0, lo/decimalLimbBase
		return uint32(lo % decimalLimbBase), true
	}
	qhi, remainder := hi/decimalLimbBase, hi%decimalLimbBase
	qlo, digit := bits.Div64(remainder, lo, decimalLimbBase)
	s.carryHi, s.carryLo = qhi, qlo
	return uint32(digit), true
}

func contextFailure(op string, code ErrorCode) (Decimal, Conditions, error) {
	return Decimal{}, 0, newError(op, code)
}

func contextExactRefusal(op string) (Decimal, Conditions, error) {
	return Decimal{}, 0, conditionError(op, Inexact, "")
}

// contextFinalWork checks W=B+2N+1 only when the caller imposed a work cap.
func contextFinalWork(base, n, limit uint64) bool {
	if limit == 0 {
		return true
	}
	work, ok := contextFinalCharge(base, n)
	return admitted(limit, work, ok)
}

// contextFinalCharge is the context finisher tariff W = B + 2N + 1, shared
// with the estimators.
func contextFinalCharge(base, n uint64) (uint64, bool) {
	twice, ok1 := arithmeticMul(n, 2)
	increment, ok2 := arithmeticAdd(twice, 1)
	work, ok3 := arithmeticAdd(base, increment)
	return work, ok1 && ok2 && ok3
}

func contextExponentAdd(ideal int64, shift uint64) (int64, bool) {
	var maximum uint64
	if ideal < 0 {
		maximum = uint64(math.MaxInt64) + uint64(-ideal)
	} else {
		maximum = uint64(math.MaxInt64 - ideal)
	}
	if shift > maximum {
		return 0, false
	}
	return ideal + int64(shift), true
}

func contextRoundUp(mode RoundingMode, negative bool, guard uint32, sticky bool, retainedLow uint32) bool {
	inexact := guard != 0 || sticky
	switch mode {
	case TowardZero, Exact:
		return false
	case AwayFromZero:
		return inexact
	case TowardPositiveInfinity:
		return inexact && !negative
	case TowardNegativeInfinity:
		return inexact && negative
	case TiesToEven, TiesAwayFromZero, TiesTowardZero:
		if guard > 5 || guard == 5 && sticky {
			return true
		}
		if guard < 5 {
			return false
		}
		if mode == TiesAwayFromZero {
			return true
		}
		return mode == TiesToEven && retainedLow%2 == 1
	default:
		return false // Context construction excludes unknown modes.
	}
}

func contextOutcome(result Decimal, events Conditions, traps Conditions, op string) (Decimal, Conditions, error) {
	selected := events & traps
	if selected != 0 {
		return result, events &^ selected, conditionError(op, selected, "")
	}
	return result, events, nil
}

// contextRun performs constant-space preflight before allocating one final
// coefficient. B has already been checked against a positive work cap.
func contextRun(p contextPlan, ctx Context, budget limits, op string) (Decimal, Conditions, error) {
	if p.zero {
		return contextExactZero(&p, budget, op)
	}
	if !p.mul && p.groups <= contextSumLimbs {
		return contextRunSum(&p, &ctx, budget, op)
	}
	return contextRunStream(p, ctx, budget, op)
}

// contextSumLimbs bounds the planned limbs of an exact sum or difference
// that contextRunSum builds on the stack and rounds once, as
// contextRunProduct does for a product. Longer spans stream, so that no
// call holds more than its result.
const contextSumLimbs = 128

// contextRunSum is contextRun for a planned, admitted sum or difference
// short enough for the stack: one pass of the Add/Sub kernel, then the
// shared finisher rounds the exact result once.
func contextRunSum(p *contextPlan, ctx *Context, budget limits, op string) (Decimal, Conditions, error) {
	var stack [contextSumLimbs + 1]uint32 // a spare limb for the rounding carry
	fillAddSub(stack[:p.groups], &p.a, p.sa, &p.b, p.sb, p.add, p.greaterA)
	r := trimLimbs(stack[:p.groups])
	if len(r) == 0 {
		return contextExactZero(p, budget, op)
	}
	var etiny int64
	if ctx.guarded {
		etiny = int64(ctx.guards.Emin) - (int64(ctx.precision) - 1)
	}
	return finishContext(r, divExactClass, p.ideal, etiny, p.ideal, p.negative, ctx, p.base, budget, op)
}

// contextRunStream is contextRun over restartable streams: three passes
// that hold nothing but the result.
func contextRunStream(p contextPlan, ctx Context, budget limits, op string) (Decimal, Conditions, error) {
	stream := contextGroupStream{plan: &p}
	var top uint32
	var topIndex uint64
	for i := uint64(0); i < p.groups; i++ {
		limb, ok := stream.next()
		if !ok {
			return contextFailure(op, ErrInsufficientStorage)
		}
		if limb != 0 {
			top, topIndex = limb, i
		}
	}
	if top == 0 {
		// Opposite-sign cancellation and zero operands are normally caught in
		// the path plan; this preserves the same exact-zero cohort if a stream
		// exposes one without a coefficient allocation.
		return contextExactZero(&p, budget, op)
	}
	length, valid := arithmeticMul(topIndex, 9)
	if valid {
		length, valid = arithmeticAdd(length, uint64(limbDigits(top)))
	}
	if !valid {
		return contextFailure(op, ErrInsufficientStorage)
	}
	precision := uint64(ctx.precision)
	cut := uint64(0)
	if length > precision {
		cut = length - precision
	}
	var tiny bool
	if ctx.guarded {
		maxLength := int64(ctx.guards.Emax) - p.ideal + 1
		if maxLength <= 0 || length > uint64(maxLength) {
			if ctx.rounding == Exact {
				return contextExactRefusal(op)
			}
			return contextOverflow(p.base, p.negative, ctx, budget, op)
		}
		minLength := int64(ctx.guards.Emin) - p.ideal + 1
		tiny = minLength > 0 && length < uint64(minLength)
		if tiny {
			etiny := int64(ctx.guards.Emin) - int64(ctx.precision-1)
			quantum := etiny - p.ideal
			if quantum > 0 && uint64(quantum) > cut {
				cut = uint64(quantum)
			}
		}
	}
	retained := uint64(0)
	if cut < length {
		retained = length - cut
	}
	var guard, retainedLow uint32
	var sticky, allNines bool
	allNines = retained > 0
	if cut > 0 {
		stream = contextGroupStream{plan: &p}
		position := uint64(0)
		for i := uint64(0); i < p.groups && position < length; i++ {
			limb, ok := stream.next()
			if !ok {
				return contextFailure(op, ErrInsufficientStorage)
			}
			for place := 0; place < 9 && position < length; place++ {
				digit := limb % 10
				limb /= 10
				switch {
				case position < cut-1:
					sticky = sticky || digit != 0
				case position == cut-1:
					guard = digit
				case position == cut:
					retainedLow = digit
				}
				if position >= cut && digit != 9 {
					allNines = false
				}
				position++
			}
		}
	}
	inexact := guard != 0 || sticky
	if ctx.rounding == Exact && inexact {
		return contextExactRefusal(op)
	}
	up := cut > 0 && contextRoundUp(ctx.rounding, p.negative, guard, sticky, retainedLow)
	carryTop := up && allNines
	exponent, valid := contextExponentAdd(p.ideal, cut)
	if !valid {
		return contextFailure(op, ErrExponentRange)
	}
	// A carry through all retained nines adds one digit. Only a result that
	// would then exceed the precision shifts its exponent; a tiny result
	// rounded at the Etiny quantum keeps Etiny and gains the digit instead.
	n := retained
	if carryTop {
		if retained < precision {
			n++
		} else {
			exponent++
		}
	}
	if n == 0 {
		n = 1
	}
	zero := retained == 0 && !up
	events := Conditions(0)
	if cut > 0 {
		events |= Rounded
	}
	if inexact {
		events |= Inexact | roundingDirection(up, p.negative)
	}
	if ctx.guarded {
		if !zero && (exponent > int64(ctx.guards.Emax) || n > uint64(int64(ctx.guards.Emax)-exponent+1)) {
			return contextOverflow(p.base, p.negative, ctx, budget, op)
		}
		if tiny {
			events |= Subnormal
			if inexact {
				events |= Underflow
			}
		}
	}
	if exponent < math.MinInt32 || exponent > math.MaxInt32 {
		return contextFailure(op, ErrExponentRange)
	}
	if !admitted(budget.MaxDigits, n, true) || !contextFinalWork(p.base, n, budget.MaxWork) {
		return contextFailure(op, ErrInsufficientStorage)
	}
	if zero {
		return contextOutcome(zeroDecimal(int32(exponent)), events, ctx.traps, op)
	}
	count, err := arithmeticLimbCount(n, op)
	if err != nil {
		return Decimal{}, 0, err
	}
	if n <= 38 {
		var inline [5]uint32
		out := inline[:count]
		if !contextWrite(out, &p, length, cut, n, up, carryTop) {
			return contextFailure(op, ErrInsufficientStorage)
		}
		return contextOutcome(publishInlineArithmetic(out, int32(exponent), p.negative), events, ctx.traps, op)
	}
	if count <= slowSmallLimbs {
		var scratch [slowSmallLimbs]uint32
		out := scratch[:count]
		if !contextWrite(out, &p, length, cut, n, up, carryTop) {
			return contextFailure(op, ErrInsufficientStorage)
		}
		return contextOutcome(publishScratch(out, int32(exponent), p.negative), events, ctx.traps, op)
	}
	out := make([]uint32, count)
	if !contextWrite(out, &p, length, cut, n, up, carryTop) {
		return contextFailure(op, ErrInsufficientStorage)
	}
	return contextOutcome(publishOwned(out, int32(exponent), p.negative), events, ctx.traps, op)
}

// contextExactZero publishes an exact zero at the ideal exponent. Only FMA's
// int64 product exponent can put that ideal outside int32, where the zero is
// not publishable.
func contextExactZero(p *contextPlan, budget limits, op string) (Decimal, Conditions, error) {
	if p.ideal < math.MinInt32 || p.ideal > math.MaxInt32 {
		return contextFailure(op, ErrExponentRange)
	}
	if !admitted(budget.MaxDigits, 1, true) || !contextFinalWork(p.base, 1, budget.MaxWork) {
		return contextFailure(op, ErrInsufficientStorage)
	}
	return zeroDecimal(int32(p.ideal)), 0, nil
}

// contextWrite fills the n-digit rounded coefficient. A carry through all
// nines is the power of ten with n digits.
func contextWrite(out []uint32, p *contextPlan, length, cut, n uint64, up, carryTop bool) bool {
	if carryTop {
		place := n - 1
		out[place/9] = decimalPowers[place%9]
		return true
	}
	stream := contextGroupStream{plan: p}
	if cut == 0 {
		for i := range out {
			limb, ok := stream.next()
			if !ok {
				return false
			}
			out[i] = limb
		}
		return true
	}
	position := uint64(0)
	for i := uint64(0); i < p.groups && position < length; i++ {
		limb, ok := stream.next()
		if !ok {
			return false
		}
		for place := 0; place < 9 && position < length; place++ {
			digit := limb % 10
			limb /= 10
			if position >= cut {
				output := position - cut
				out[output/9] += digit * decimalPowers[output%9]
			}
			position++
		}
	}
	if up {
		carry := uint64(1)
		for i := range out {
			sum := uint64(out[i]) + carry
			out[i] = uint32(sum % decimalLimbBase)
			carry = sum / decimalLimbBase
			if carry == 0 {
				break
			}
		}
		return carry == 0
	}
	return true
}

func contextOverflow(base uint64, negative bool, ctx Context, budget limits, op string) (Decimal, Conditions, error) {
	n := uint64(ctx.precision)
	if !admitted(budget.MaxDigits, n, true) || !contextFinalWork(base, n, budget.MaxWork) {
		return contextFailure(op, ErrInsufficientStorage)
	}
	count, err := arithmeticLimbCount(n, op)
	if err != nil {
		return Decimal{}, 0, err
	}
	exponent := int32(int64(ctx.guards.Emax) - int64(ctx.precision) + 1)
	// Bmax lies strictly toward zero from the exact overflowing value.
	events := Overflow | Inexact | Rounded | roundingDirection(false, negative)
	fill := func(out []uint32) {
		for i := range out {
			out[i] = uint32(decimalLimbBase - 1)
		}
		width := 1 + (n-1)%9
		if width < 9 {
			out[len(out)-1] = decimalPowers[width] - 1
		}
	}
	if n <= 38 {
		var inline [5]uint32
		out := inline[:count]
		fill(out)
		return contextOutcome(publishInlineArithmetic(out, exponent, negative), events, ctx.traps, op)
	}
	if count <= slowSmallLimbs {
		var scratch [slowSmallLimbs]uint32
		out := scratch[:count]
		fill(out)
		return contextOutcome(publishScratch(out, exponent, negative), events, ctx.traps, op)
	}
	out := make([]uint32, count)
	fill(out)
	return contextOutcome(publishOwned(out, exponent, negative), events, ctx.traps, op)
}
