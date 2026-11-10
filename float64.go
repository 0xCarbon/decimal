// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"math"
	"math/bits"
	"strconv"
)

// Binary64 interop. Every finite double is the dyadic rational
// ±m·2^e, whose decimal expansion terminates in at most 767 significant
// digits (768 for a midpoint between adjacent doubles). Ingress expands it
// exactly into stack base-10^9 limbs and rounds through the shared division
// finisher. Egress and comparison enclose the decimal between two 192-bit
// products of its leading digits and a 128-bit power of five, and compare
// against an expanded dyadic point only when a rounding boundary falls
// inside the enclosure. No math/big is involved.

// binary64Limbs holds an exact dyadic expansion of at most 768 digits (86
// base-10^9 limbs) plus a spare limb for the finisher's rounding carry.
const binary64Limbs = 87

// binary64Top is the index just above MaxFloat64 in the monotone bit order
// of nonnegative doubles; its value is taken as 2^1024 (the +Inf pattern).
const binary64Top = 0x7FF0000000000000

// binary64Parts returns a finite f as ±m·2^e with m odd, or m = 0 for ±0.
func binary64Parts(f float64) (negative bool, m uint64, e int64) {
	negative, m, e = binary64Raw(math.Float64bits(f))
	if m == 0 {
		return negative, 0, 0
	}
	shift := bits.TrailingZeros64(m)
	return negative, m >> shift, e + int64(shift)
}

// binary64Raw decodes a bit pattern to its unreduced significand and
// exponent: the value of index b is m·2^e with ulp 2^e. The +Inf pattern
// decodes to 2^1024 for use as the search's upper bound.
func binary64Raw(b uint64) (negative bool, m uint64, e int64) {
	negative = b>>63 != 0
	exponent := int64(b>>52) & 0x7FF
	fraction := b & (1<<52 - 1)
	if exponent == 0 {
		return negative, fraction, -1074
	}
	return negative, fraction | 1<<52, exponent - 1075
}

// binary64Passes is the number of limb multiplication passes that expand
// 2^e or 5^−e: ⌈e/29⌉ for e ≥ 0 and ⌈−e/13⌉ for e < 0.
func binary64Passes(e int64) uint64 {
	if e >= 0 {
		return uint64(e+28) / 29
	}
	return uint64(-e+12) / 13
}

// float64FiveSmall holds 5^0 through 5^12.
var float64FiveSmall = [13]uint64{1, 5, 25, 125, 625, 3125, 15625, 78125, 390625, 1953125, 9765625, 48828125, 244140625}

// expandDyadicPoint writes the same limbs as expandDyadic with one
// multiplication of a tabulated 5^(13j) or 2^(29j) by the at most 86-bit
// m·5^r or m·2^r, and reports the limb products it spent: at
// most three per limb of the power, whatever the exponent, instead of a
// pass per 13 or 29 powers. It serves −1075 ≤ e ≤ 1024, every point an
// egress comparison meets.
func expandDyadicPoint(buf *[binary64Limbs]uint32, m uint64, e int64) (limbs []uint32, x int64, products uint64) {
	var power int64
	var hi, lo uint64
	if e < 0 {
		power = -e / 13
		hi, lo = bits.Mul64(m, float64FiveSmall[-e%13])
		x = e
	} else {
		r := uint(e % 29)
		power = float64TwoPowers + e/29
		hi, lo = m>>(64-r), m<<r
	}
	start, end := int(float64DyadicOffsets[power]), int(float64DyadicOffsets[power+1])
	var factor [3]uint64 // the small factor below 2^86 < 10^27
	var limbs5 [5]uint32
	nf := wordLimbs(&limbs5, hi, lo)
	for i := range nf {
		factor[i] = uint64(limbs5[i])
	}
	// Each column sums at most three products below 10^18 plus a carry
	// below 2^34, so it stays below 2^64.
	width := end - start
	n := width + nf
	var carry uint64
	for i := range n {
		column := carry
		for k := range nf {
			if p := i - k; p >= 0 && p < width {
				column += uint64(float64DyadicLimbs[start+p]) * factor[k]
				products++
			}
		}
		buf[i] = uint32(column % decimalLimbBase)
		carry = column / decimalLimbBase
	}
	for n > 0 && buf[n-1] == 0 {
		n--
	}
	return buf[:n], x, products
}

// expandDyadic writes the exact expansion of m·2^e (m < 2^55) into buf as
// little-endian base-10^9 limbs X at exponent x: X = m·2^e at x = 0 when
// e ≥ 0, and X = m·5^−e at x = e otherwise. The slice keeps buf's spare
// capacity.
func expandDyadic(buf *[binary64Limbs]uint32, m uint64, e int64) (limbs []uint32, x int64) {
	n := 0
	for v := m; v != 0; v /= decimalLimbBase {
		buf[n] = uint32(v % decimalLimbBase)
		n++
	}
	if e < 0 {
		k := -e
		for ; k >= 13; k -= 13 {
			n = multiplyLimbsSmall(buf, n, 1220703125) // 5^13
		}
		if k > 0 {
			factor := uint64(1)
			for range k {
				factor *= 5
			}
			n = multiplyLimbsSmall(buf, n, factor)
		}
		return buf[:n], e
	}
	k := e
	for ; k >= 29; k -= 29 {
		n = multiplyLimbsSmall(buf, n, 1<<29)
	}
	if k > 0 {
		n = multiplyLimbsSmall(buf, n, 1<<uint(k))
	}
	return buf[:n], 0
}

// multiplyLimbsSmall multiplies the first n limbs by factor < 2^31 in
// place; limb·factor + carry stays below 2^64.
func multiplyLimbsSmall(buf *[binary64Limbs]uint32, n int, factor uint64) int {
	var carry uint64
	for i := range n {
		product := uint64(buf[i])*factor + carry
		buf[i] = uint32(product % decimalLimbBase)
		carry = product / decimalLimbBase
	}
	for carry != 0 {
		buf[n] = uint32(carry % decimalLimbBase)
		carry /= decimalLimbBase
		n++
	}
	return n
}

func float64Nonfinite(f float64) bool { return math.IsNaN(f) || math.IsInf(f, 0) }

// FromFloat64 returns the shortest-round-trip decimal of a finite f: the
// shortest digits that strconv formats for f, which parse back to f,
// placed at the largest exponent not above 0 at which they are exact, so
// FromFloat64(100) is 100 and FromFloat64(0.1) is 0.1. ±0 gives the
// unsigned zero. NaN and ±Inf return ErrConversionSyntax.
func FromFloat64(f float64) (Decimal, error) {
	const op = "FromFloat64"
	if float64Nonfinite(f) {
		return Decimal{}, newError(op, ErrConversionSyntax)
	}
	if f == 0 {
		return Decimal{}, nil
	}
	// An integer below 2^53 is its own shortest round-trip decimal: a
	// decimal of fewer significant digits is a multiple of a higher power
	// of ten, at least one away, and the rounding interval is half an ulp
	// (at most one half) wide on each side.
	if a := math.Abs(f); a < 1<<53 && a == math.Trunc(a) {
		return inlineDecimal(uint128{lo: uint64(a)}, 0, f < 0), nil
	}
	var buf [32]byte
	var d Decimal
	if err := d.UnmarshalText(strconv.AppendFloat(buf[:0], f, 'e', -1, 64)); err != nil {
		return Decimal{}, newError(op, ErrConversionSyntax)
	}
	if d.exponent() > 0 {
		// At most 309 digits: the pad is exact and bounded.
		padded, _, err := d.Quantize(0, Exact)
		if err != nil {
			return Decimal{}, err
		}
		d = padded
	}
	return d, nil
}

// FromFloat64Exact returns the exact decimal value of a finite f, its full
// binary expansion (up to 767 significant digits), at the largest exponent
// not above 0 at which it is exact: FromFloat64Exact(0.1) is
// 0.1000000000000000055511151231257827021181583404541015625. ±0 gives the
// unsigned zero. NaN and ±Inf return ErrConversionSyntax.
func FromFloat64Exact(f float64) (Decimal, error) {
	const op = "FromFloat64Exact"
	if float64Nonfinite(f) {
		return Decimal{}, newError(op, ErrConversionSyntax)
	}
	negative, m, e := binary64Parts(f)
	if m == 0 {
		return Decimal{}, nil
	}
	var buf [binary64Limbs]uint32
	x, exponent := expandDyadic(&buf, m, e)
	return divPublish(divOutcome{r: x, exponent: exponent}, negative, 0, limits{}, op)
}

// FromFloat64ToExponent rounds the exact value of a finite f once to the
// given exponent under mode, the shape of SQL CAST(DOUBLE AS DECIMAL(p,s)):
// FromFloat64ToExponent(2.675, -2, TiesToEven) is 2.67 because the double
// lies below the tie. Results, Conditions and error identities equal
// FromRatToExponent of the double's exact rational, except physical
// admission, which is path-specific. The exact expansion (at most 767
// digits) lives on the stack, so 1e-300 at exponent −2 is a 0.00 without
// heap allocation, and results of at most 38 digits allocate nothing.
func FromFloat64ToExponent(f float64, exponent int32, mode RoundingMode) (Decimal, Conditions, error) {
	if d, events, ok := float64ToExponentInline(f, exponent, mode); ok {
		return d, events, nil
	}
	return fromFloat64ToExponent(f, exponent, mode, limits{}, "FromFloat64ToExponent")
}

// FromFloat64ToExponentWithBudget is FromFloat64ToExponent with copied
// quotas: the charge B is 87 work units per expansion pass plus one per
// padded limb, the whole tariff is W = B + 2N + 1 for an N-digit result,
// and MaxDigits caps N. Every quota is checked before the
// result is allocated.
func FromFloat64ToExponentWithBudget(f float64, exponent int32, mode RoundingMode, budget Budget) (Decimal, Conditions, error) {
	if d, events, ok := float64ToExponentInline(f, exponent, mode); ok && float64ToExponentAdmitted(f, exponent, d, budget.arith()) {
		return d, events, nil
	}
	return fromFloat64ToExponent(f, exponent, mode, budget.arith(), "FromFloat64ToExponentWithBudget")
}

// float64ToExponentInline is the unbudgeted FromFloat64ToExponent of a
// finite nonzero f = ±m·2^e at a target −19 ≤ t ≤ 0, the shape of a cast to
// DECIMAL(p,s): the value in units of 10^t is m·10^−t·2^e, whose integer
// part and half class are a shift of the product m·10^−t < 2^117 instead of
// a limb expansion of 5^−e. The rounding is roundToExponent's rule at ideal
// exponent 0. ok is false for zero, non-finite values, an Exact refusal, an
// unknown mode, a left shift leaving 128 bits and every other target; the
// general path owns those and every budget.
func float64ToExponentInline(f float64, target int32, mode RoundingMode) (Decimal, Conditions, bool) {
	if target > 0 || target < -19 || mode > Exact || float64Nonfinite(f) {
		return Decimal{}, 0, false
	}
	negative, m, e := binary64Parts(f)
	if m == 0 {
		return Decimal{}, 0, false
	}
	hi, lo := bits.Mul64(m, pow10Words[-target])
	var q uint128
	class := divExactClass
	switch {
	case e >= 0:
		width := int64(bits.Len64(lo))
		if hi != 0 {
			width = 64 + int64(bits.Len64(hi))
		}
		if width+e > 128 {
			return Decimal{}, 0, false
		}
		if e >= 64 {
			q = uint128{hi: lo << uint(e-64)}
		} else {
			q = uint128{lo: lo << uint(e), hi: hi<<uint(e) | lo>>(64-uint(e))}
		}
	case e <= -128:
		class = divBelow // 0 < m·10^−t < 2^117 ≤ 2^(−e−1)
	default:
		k := uint(-e)
		var rhi, rlo, halfHi, halfLo uint64 // the discarded low k bits and 2^(k−1)
		if k >= 64 {
			q = uint128{lo: hi >> (k - 64)}
			rhi, rlo = hi&(1<<(k-64)-1), lo
			if k == 64 {
				halfLo = 1 << 63
			} else {
				halfHi = 1 << (k - 65)
			}
		} else {
			q = uint128{lo: lo>>k | hi<<(64-k), hi: hi >> k}
			rlo, halfLo = lo&(1<<k-1), 1<<(k-1)
		}
		switch {
		case rhi|rlo == 0:
		case rhi < halfHi || rhi == halfHi && rlo < halfLo:
			class = divBelow
		case rhi == halfHi && rlo == halfLo:
			class = divHalfClass
		default:
			class = divAbove
		}
	}
	var events Conditions
	inexact := class != divExactClass
	if inexact {
		if mode == Exact {
			return Decimal{}, 0, false
		}
		events = Inexact | Rounded
	}
	guard, sticky := class.guardSticky()
	up := contextRoundUp(mode, negative, guard, sticky, uint32(q.lo&1))
	if inexact {
		events |= roundingDirection(up, negative)
	}
	if up {
		var carry uint64
		q.lo, carry = bits.Add64(q.lo, 1, 0)
		q.hi += carry // q < 2^117 here: an exact left shift never rounds up
	}
	return inlineDecimal(q, target, negative), events, true
}

// float64ToExponentAdmitted reports whether budget admits the general
// path's conversion of a finite nonzero f whose result d the inline path
// produced: the result's digit count N against MaxDigits, and the whole
// tariff W = B + 2N + 1 against MaxWork, with B the expansion passes and
// padded limbs fromFloat64ToExponent charges for f's exponent and the
// target. Those are its final checks; the earlier ones compare B alone, and
// for a padded value the same N and W, so a budget this admits is never
// refused there, and one it does not admit is refused there.
func float64ToExponentAdmitted(f float64, target int32, d Decimal, budget limits) bool {
	if budget.MaxDigits|budget.MaxWork == 0 {
		return true
	}
	_, _, e := binary64Parts(f)
	var pad uint64
	if x := min(e, 0); int64(target) < x {
		pad = uint64(x - int64(target))
	}
	n := uint64(1)
	if !d.isZero() {
		n = inlineDigits(d.words)
	}
	return budget.admits(n, binary64Passes(e)*binary64Limbs+(pad+8)/9+2*n+1)
}

func fromFloat64ToExponent(f float64, target int32, mode RoundingMode, budget limits, op string) (Decimal, Conditions, error) {
	if mode > Exact {
		return quantizeInvalidMode(op)
	}
	if float64Nonfinite(f) {
		return syntaxFailure(op)
	}
	negative, m, e := binary64Parts(f)
	if m == 0 {
		return ratZero(target, budget, op)
	}
	t := int64(target)
	x := min(e, 0)
	var pad uint64
	if t < x {
		pad = uint64(x - t)
	}
	charge, ok := arithmeticAdd(binary64Passes(e)*binary64Limbs, (pad+8)/9)
	if !ok || budget.MaxWork != 0 && charge > budget.MaxWork {
		return contextFailure(op, ErrInsufficientStorage)
	}
	var buf [binary64Limbs]uint32
	limbs, x := expandDyadic(&buf, m, e)
	if pad == 0 {
		r, class := dropDigits(limbs, divExactClass, uint64(t-x))
		return finishToExponent(r, class, t, 0, negative, mode, charge, budget, op)
	}
	digits, ok := arithmeticAdd(limbsDigits(limbs), pad)
	if !ok || !admitted(budget.MaxDigits, digits, true) {
		return contextFailure(op, ErrInsufficientStorage)
	}
	// The padded value is exact, so its digit count is final: the whole
	// tariff W = B + 2N + 1 is checked before any allocation.
	if budget.MaxWork != 0 && !contextFinalWork(charge, digits, budget.MaxWork) {
		return contextFailure(op, ErrInsufficientStorage)
	}
	count := 1 + (digits-1)/9
	var r []uint32
	if count < binary64Limbs {
		r = buf[:count] // in place; a padded value is exact and never carries
	} else {
		// The pad buffer and divPublish's owned copy are both live.
		twice, ok := arithmeticMul(digits, 2)
		if !ok || !ratAdmitted(0, twice) {
			return contextFailure(op, ErrInsufficientStorage)
		}
		r = make([]uint32, count, count+1)
	}
	return finishToExponent(padLimbs(r, limbs, pad), divExactClass, t, 0, negative, mode, charge, budget, op)
}

// padLimbs writes X·10^pad into r, which holds exactly the padded limbs and
// may alias X's buffer (X then occupies r's low limbs): it multiplies by
// 10^(pad mod 9) in place, then moves the limbs up by pad/9 and clears the
// vacated low limbs. It returns r trimmed with its spare capacity.
func padLimbs(r, x []uint32, pad uint64) []uint32 {
	return shiftLimbsLeft(r, copy(r, x), pad)
}

// FromFloat64WithContext rounds the exact value of a finite f once to the
// context precision with its guards and traps: the IEEE 754 convertFormat
// from binary64 to a decimal format such as Decimal64Context. Results,
// Conditions and error identities equal FromRatWithContext of the double's
// exact rational, except physical admission, which is path-specific. The
// expansion is bounded by 767 digits, but a guarded overflow publishes the
// context's largest value, whose p digits are bounded only by the precision;
// a budget on the context caps them. Precision 0 converts exactly.
func FromFloat64WithContext(f float64, ctx Context) (Decimal, Conditions, error) {
	return fromFloat64Context(f, ctx, ctx.arith, "FromFloat64WithContext", false)
}

// float64ContextInlineShape reports whether the word division serves a
// fraction ±m·2^e at the precision: a one-word denominator 2^−e, −63 ≤ e <
// 0, and a finite precision the inline division kernel rounds to. An
// integer's expansion is short, and stays with the exact expansion.
func float64ContextInlineShape(e int64, precision uint32) bool {
	return e < 0 && e >= -63 && precision != 0 && precision <= inlineDivMaxPrecision
}

// float64ContextInline is fromFloat64Context for a fraction ±m·2^e, m odd,
// of float64ContextInlineShape, whose exact rational is the one-word m over
// the one-word 2^−e. DivWithContext's inline kernel rounds that quotient at
// ideal exponent 0, which is the exact expansion's finisher: a value that
// fits the precision keeps the expansion's exponent e, since m·5^−e has no
// trailing zero to strip, and a longer one is rounded once from the same
// truncated quotient and class. A budget is admitted by the general path's
// only checks, the result's N digits and W = B + 2N + 1 with B the
// expansion passes of e, when the result carries no error. ok is false
// wherever the kernel defers and for every other budget.
//
//go:noinline
func float64ContextInline(negative bool, m uint64, e int64, ctx *Context, budget limits, op string) (Decimal, Conditions, error, bool) {
	result, conditions, err, ok := inlineDivContext(inlineDecimal(uint128{lo: m}, 0, negative), inlineDecimal(uint128{lo: 1 << uint(-e)}, 0, false), ctx, op)
	if !ok {
		return Decimal{}, 0, nil, false
	}
	if budget != (limits{}) {
		digits := uint64(1)
		if !result.isZero() {
			digits = inlineDigits(result.words)
		}
		if err != nil || !budget.admits(digits, binary64Passes(e)*binary64Limbs+2*digits+1) {
			return Decimal{}, 0, nil, false
		}
	}
	return result, conditions, err, true
}

// fromFloat64Context is the FromFloat64WithContext kernel. Public entry
// points pass expand=false. expand=true takes the exact expansion for
// every value: only tests pass it, as the reference the word division is
// pinned against.
func fromFloat64Context(f float64, ctx Context, budget limits, op string, expand bool) (Decimal, Conditions, error) {
	if float64Nonfinite(f) {
		return syntaxFailure(op)
	}
	negative, m, e := binary64Parts(f)
	if m == 0 {
		return ratZero(0, budget, op)
	}
	if !expand && float64ContextInlineShape(e, ctx.precision) {
		if result, conditions, err, ok := float64ContextInline(negative, m, e, &ctx, budget, op); ok {
			return result, conditions, err
		}
	}
	charge := binary64Passes(e) * binary64Limbs
	var buf [binary64Limbs]uint32
	limbs, x := expandDyadic(&buf, m, e)
	if ctx.precision == 0 {
		result, err := finishExact(limbs, x, uint64(-x), negative, charge, budget, op)
		return result, 0, err
	}
	precision := int64(ctx.precision)
	var etiny int64
	if ctx.guarded {
		etiny = int64(ctx.guards.Emin) - (precision - 1)
	}
	digits := int64(limbsDigits(limbs))
	if digits <= precision {
		// Exact first: the expansion already fits the precision.
		return finishContext(limbs, divExactClass, x, etiny, 0, negative, &ctx, charge, budget, op)
	}
	tPrime := x + digits - precision
	if ctx.guarded {
		tPrime = max(tPrime, etiny)
	}
	r, class := dropDigits(limbs, divExactClass, uint64(tPrime-x))
	return finishContext(r, class, tPrime, etiny, 0, negative, &ctx, charge, budget, op)
}

// dyadicWork counts an egress call's exact dyadic comparisons and the limb
// products their expansions spent.
type dyadicWork struct {
	compares uint64
	products uint64
}

// dyadicComparer compares |d| with dyadic points m·2^e. A coefficient
// longer than dyadicPrefixLimbs limbs is read through its leading limbs
// plus one sticky bit for the rest: every compared point has at most 768
// significant digits within two decades of d, so it lies on the prefix's
// digit grid.
type dyadicComparer struct {
	view     coefficientView
	exponent int32
	adjusted int64
	sticky   bool
	work     dyadicWork
}

const dyadicPrefixLimbs = 90

func newDyadicComparer(d Decimal) dyadicComparer {
	c := dyadicComparer{view: coefficientViewOf(d), exponent: d.exponent()}
	c.adjusted = clampAdjusted(adjusted(&c.view, int64(d.exponent())))
	if c.view.slow != nil && c.view.count > dyadicPrefixLimbs {
		dropped := c.view.count - dyadicPrefixLimbs
		for _, limb := range c.view.slow[:dropped] {
			if limb != 0 {
				c.sticky = true
				break
			}
		}
		c.view.slow = c.view.slow[dropped:]
		c.view.count = dyadicPrefixLimbs
		// The prefix's exponent stays near the adjusted exponent, which the
		// callers bound to the binary64 decades before comparing.
		c.exponent = int32(c.adjusted - int64(limbsDigits(c.view.slow)) + 1)
	}
	return c
}

// clampAdjusted reads a 128-bit adjusted exponent as an int64 saturated
// to ±2^40, far beyond every binary64 decade.
func clampAdjusted(a adjustedExponent) int64 {
	const limit = 1 << 40
	switch {
	case a.hi > 0 || a.hi == 0 && a.lo > limit:
		return limit
	case a.hi < -1 || a.hi == -1 && a.lo < ^uint64(limit-1):
		return -limit
	default:
		return int64(a.lo)
	}
}

// dyadicAdjustedLow is ⌊k·log10 2⌋, exact for |k| ≤ 2200 with the
// constant bracketing log10 2 on the side of k's sign.
func dyadicAdjustedLow(k int64) int64 {
	magnitude, c := uint64(k), uint64(301029995663981195)
	if k < 0 {
		magnitude, c = uint64(-k), 301029995663981196
	}
	hi, lo := bits.Mul64(magnitude, c)
	q, rem := bits.Div64(hi, lo, 1_000_000_000_000_000_000)
	if k >= 0 {
		return int64(q)
	}
	if rem != 0 {
		q++
	}
	return -int64(q)
}

// compare returns sign(|d| − m·2^e) for m < 2^55; m = 0 is the zero point.
func (c *dyadicComparer) compare(m uint64, e int64) int {
	if m == 0 {
		return 1
	}
	// The point lies in [2^(L−1+e), 2^(L+e)), so its adjusted exponent is
	// a or a+1 with a = ⌊(L−1+e)·log10 2⌋.
	low := dyadicAdjustedLow(int64(bits.Len64(m)) - 1 + e)
	if c.adjusted < low {
		return -1
	}
	if c.adjusted > low+1 {
		return 1
	}
	var buf [binary64Limbs]uint32
	limbs, x, products := expandDyadicPoint(&buf, m, e)
	c.work.compares++
	c.work.products += products
	point := coefficientView{slow: limbs, count: len(limbs)}
	cmp := compareMagnitude(&c.view, int64(c.exponent), &point, x)
	if cmp == 0 && c.sticky {
		return 1
	}
	return cmp
}

// compareIndex compares |d| with the nonnegative double of bit pattern b.
func (c *dyadicComparer) compareIndex(b uint64) int {
	if b == binary64Top {
		return c.compare(1, 1024)
	}
	_, m, e := binary64Raw(b)
	return c.compare(m, e)
}

// Float64 returns the double nearest d (ties to even) with its exactness
// and direction: Conditions is 0 when the double equals d exactly (an
// exact subnormal reports Subnormal alone), and otherwise
// Inexact|Rounded with Increased or Decreased, plus Overflow for ±Inf and
// Underflow|Subnormal for an inexact result below 2^−1022 (tininess before
// rounding). A nonzero d that rounds to zero returns a zero with d's sign.
func (d Decimal) Float64() (float64, Conditions) {
	return d.float64Rounded(TiesToEven)
}

// Float64Rounded returns the double selected from d by mode, with the
// Conditions of Float64. Overflow follows IEEE 754 §7.4: TowardZero gives
// ±MaxFloat64, TowardPositiveInfinity gives +Inf or −MaxFloat64,
// TowardNegativeInfinity gives +MaxFloat64 or −Inf, and the nearest modes
// and AwayFromZero give ±Inf. So TowardNegativeInfinity and
// TowardPositiveInfinity always bracket d with adjacent doubles. Exact
// returns the double only when it equals d, and otherwise a
// *Error trapping Inexact.
func (d Decimal) Float64Rounded(mode RoundingMode) (float64, Conditions, error) {
	const op = "Float64Rounded"
	if mode > Exact {
		return 0, 0, newError(op, ErrInvalidContext)
	}
	f, conditions := d.float64Rounded(mode)
	if mode == Exact && conditions&Inexact != 0 {
		return 0, 0, conditionError(op, Inexact, "")
	}
	return f, conditions, nil
}

func (d Decimal) float64Rounded(mode RoundingMode) (float64, Conditions) {
	f, conditions, _ := d.float64Work(mode)
	return f, conditions
}

// float64Work is float64Rounded that also reports the exact dyadic
// comparisons it spent.
func (d Decimal) float64Work(mode RoundingMode) (f float64, conditions Conditions, work dyadicWork) {
	if d.isZero() {
		return 0, 0, dyadicWork{}
	}
	negative := d.negative()
	place, ok := d.binary64PlaceSmall()
	if !ok {
		if place, work, ok = d.binary64PlaceBounded(); !ok {
			place, work = d.binary64PlaceGeneral()
		}
	}
	b, class := place.index, place.class
	if b >= binary64Top {
		f, conditions = float64Overflow(mode, negative)
		return f, conditions, work
	}
	if b < 1<<52 { // the floor lies below 2^−1022, so 0 < |d| < 2^−1022
		conditions = Subnormal
	}
	if class == divExactClass {
		return float64WithSign(b, negative), conditions, work
	}
	guard, sticky := class.guardSticky()
	up := contextRoundUp(mode, negative, guard, sticky, uint32(b&1))
	if up {
		b++
		if b == binary64Top {
			f, conditions = float64Overflow(mode, negative)
			return f, conditions, work
		}
	}
	conditions |= Inexact | Rounded | roundingDirection(up, negative)
	if conditions&Subnormal != 0 {
		conditions |= Underflow
	}
	return float64WithSign(b, negative), conditions, work
}

// binary64Place locates a nonzero |d| among the nonnegative doubles: index
// is the largest bit pattern whose value is at most |d| (binary64Top when
// |d| ≥ 2^1024), and class places |d| against that double and the midpoint
// above it.
type binary64Place struct {
	index uint64
	class divHalf
}

// float64Pow10 holds 10^0 through 10^22, the powers of ten that binary64
// represents exactly.
var float64Pow10 = [23]float64{
	1e0, 1e1, 1e2, 1e3, 1e4, 1e5, 1e6, 1e7, 1e8, 1e9, 1e10, 1e11,
	1e12, 1e13, 1e14, 1e15, 1e16, 1e17, 1e18, 1e19, 1e20, 1e21, 1e22,
}

// float64Fives holds 5^0 through 5^22.
var float64Fives = [23]uint64{
	1, 5, 25, 125, 625, 3_125, 15_625, 78_125, 390_625, 1_953_125, 9_765_625, 48_828_125,
	244_140_625, 1_220_703_125, 6_103_515_625, 30_517_578_125, 152_587_890_625,
	762_939_453_125, 3_814_697_265_625, 19_073_486_328_125, 95_367_431_640_625,
	476_837_158_203_125, 2_384_185_791_015_625,
}

// binary64PlaceSmall places a one-word coefficient w < 2^53 at an exponent
// −22 ≤ e ≤ 0, the shape of money: w and 10^−e are both exact doubles, so
// one IEEE division is the nearest double f = m·2^x of w/10^−e, and
// comparing the integers m·5^−e and w·2^−(x−e) (both below 2^106) places
// the exact value against f. No tie exists (a midpoint needs 54 significant
// bits and w has at most 53), so a nearest f below the value leaves it
// below the midpoint over f, and a nearest f above it leaves it above the
// midpoint over f's predecessor. ok is false for every other shape.
func (d Decimal) binary64PlaceSmall() (binary64Place, bool) {
	w, e := d.words.lo, d.exponent()
	if d.slow != nil || d.words.hi != 0 || w-1 >= 1<<53-1 || e > 0 || e < -22 {
		return binary64Place{}, false
	}
	if e == 0 {
		return binary64Place{index: math.Float64bits(float64(w)), class: divExactClass}, true
	}
	k := uint(-e)
	b := math.Float64bits(float64(w) / float64Pow10[k])
	m := b&(1<<52-1) | 1<<52
	s := 1075 - int(b>>52) - int(k) // f·10^k = m·5^k / 2^s
	if s < 1 || s > 127 {
		return binary64Place{}, false // unreachable: 2 ≤ s ≤ 105
	}
	phi, plo := bits.Mul64(m, float64Fives[k]) // m·5^k
	var whi, wlo uint64                        // w·2^s
	if s < 64 {
		whi, wlo = w>>(64-uint(s)), w<<uint(s)
	} else {
		whi = w << (uint(s) - 64)
	}
	switch {
	case phi == whi && plo == wlo:
		return binary64Place{index: b, class: divExactClass}, true
	case phi < whi || phi == whi && plo < wlo:
		return binary64Place{index: b, class: divBelow}, true
	}
	return binary64Place{index: b - 1, class: divAbove}, true
}

// binary64PlaceGeneral is the reference placement: it searches the bit
// patterns with exact dyadic comparisons.
func (d Decimal) binary64PlaceGeneral() (binary64Place, dyadicWork) {
	c := newDyadicComparer(d)
	// 10^308 < 2^1024 ≤ 10^309, and 10^−325 < 2^−1075.
	if c.adjusted >= 309 || c.adjusted == 308 && c.compare(1, 1024) >= 0 {
		return binary64Place{index: binary64Top, class: divAbove}, c.work
	}
	if c.adjusted <= -326 {
		return binary64Place{class: divBelow}, c.work
	}
	b := c.floorIndex()
	class := divExactClass
	if c.compareIndex(b) != 0 {
		_, m, e := binary64Raw(b)
		switch c.compare(2*m+1, e-1) {
		case -1:
			class = divBelow
		case 0:
			class = divHalfClass
		default:
			class = divAbove
		}
	}
	return binary64Place{index: b, class: class}, c.work
}

// binary64PlaceBounded places |d| from its leading 64 bits or 19 digits
// and the 128-bit power of five, in work independent of the exponent.
// The truncations enclose |d| in lo ≤ |d| ≤ hi, both products
// of at most 192 bits; when lo and hi fall in the same half-ulp cell that
// cell is the answer, and when one cell boundary separates them a single
// exact comparison against it decides. ok is false otherwise, which the
// 2^−59 enclosure width makes unreachable; the caller then takes the
// general path.
func (d Decimal) binary64PlaceBounded() (place binary64Place, work dyadicWork, ok bool) {
	w, sticky, t, q, verdict := binary64Lead(d)
	switch {
	case verdict > 0:
		return binary64Place{index: binary64Top, class: divAbove}, dyadicWork{}, true
	case verdict < 0:
		return binary64Place{class: divBelow}, dyadicWork{}, true
	}
	lo, hi, exact, e := binary64Enclosure(w, sticky, t, q)
	posLo, onLo := binary64Position(lo, e)
	if exact {
		return binary64Settle(posLo, onLo), dyadicWork{}, true
	}
	// lo < |d| < hi strictly: ε > 0 or dropped digits are nonzero.
	posHi, _ := binary64Position(hi, e)
	switch posHi {
	case posLo:
		return binary64Settle(posLo, false), dyadicWork{}, true
	case posLo + 1:
		c := newDyadicComparer(d)
		var cmp int
		if b := posHi >> 1; posHi&1 == 0 {
			cmp = c.compareIndex(b)
		} else {
			_, m, e := binary64Raw(b)
			cmp = c.compare(2*m+1, e-1)
		}
		switch cmp {
		case -1:
			return binary64Settle(posLo, false), c.work, true
		case 0:
			return binary64Settle(posHi, true), c.work, true
		}
		return binary64Settle(posHi, false), c.work, true
	}
	return binary64Place{}, dyadicWork{}, false
}

// binary64Settle turns a half-ulp cell position into a placement: the
// position is 2·index plus 1 above the midpoint, and onBoundary says |d|
// is the cell's lower end.
func binary64Settle(pos uint64, onBoundary bool) binary64Place {
	place := binary64Place{index: min(pos>>1, binary64Top)}
	switch {
	case place.index == binary64Top: // |d| ≥ 2^1024
		place.class = divAbove
	case onBoundary && pos&1 == 0:
		place.class = divExactClass
	case onBoundary:
		place.class = divHalfClass
	case pos&1 == 0:
		place.class = divBelow
	default:
		place.class = divAbove
	}
	return place
}

// binary64Lead reads a nonzero |d| as (w + f)·2^t·10^q with 0 ≤ f < 1 and
// sticky reporting f > 0: an inline coefficient keeps its leading 64 bits,
// a limb coefficient its leading 19 digits. verdict is +1 when |d| ≥
// 2^1024 and −1 when |d| < 2^−1075, both decided by the exponent alone;
// otherwise q lies in the power table.
func binary64Lead(d Decimal) (w uint64, sticky bool, t, q int64, verdict int) {
	if d.slow == nil {
		// Every inline coefficient is below 2^128 < 10^39.
		switch {
		case d.exponent() > float64TableMax: // |d| ≥ 10^309
			return 0, false, 0, 0, 1
		case d.exponent() < float64TableMin: // |d| < 10^(39−364)
			return 0, false, 0, 0, -1
		}
		hi, lo := d.words.hi, d.words.lo
		if hi == 0 {
			return lo, false, 0, int64(d.exponent()), 0
		}
		z := uint(bits.LeadingZeros64(hi))
		return hi<<z | lo>>(64-z), lo<<z != 0, int64(64 - z), int64(d.exponent()), 0
	}
	limbs := d.slow.limbs
	n := len(limbs)
	a := clampAdjusted(adjusted(&coefficientView{slow: limbs, count: n}, int64(d.exponent())))
	switch {
	case a >= 309:
		return 0, false, 0, 0, 1
	case a <= -326:
		return 0, false, 0, 0, -1
	}
	// Gather whole limbs from the top while they fit in 19 digits, then
	// the leading digits of the next one; the rest only feeds sticky.
	i := n - 1
	w = uint64(limbs[i])
	digits := int64(limbDigits(limbs[i]))
	for i--; i >= 0 && digits+9 <= 19; i-- {
		w = w*decimalLimbBase + uint64(limbs[i])
		digits += 9
	}
	if i >= 0 && digits < 19 {
		keep := 19 - digits
		split := pow10Words[9-keep]
		w = w*pow10Words[keep] + uint64(limbs[i])/split
		sticky = uint64(limbs[i])%split != 0
		digits = 19
		i--
	}
	for ; i >= 0 && !sticky; i-- {
		sticky = limbs[i] != 0
	}
	return w, sticky, 0, a - digits + 1, 0
}

func float64WithSign(b uint64, negative bool) float64 {
	if negative {
		b |= 1 << 63
	}
	return math.Float64frombits(b)
}

// float64Overflow is the IEEE 754 §7.4 overflow result for |r∞| above
// MaxFloat64; TiesTowardZero and AwayFromZero overflow to infinity by
// analogy with the nearest modes.
func float64Overflow(mode RoundingMode, negative bool) (float64, Conditions) {
	infinite := true
	switch mode {
	case TowardZero, Exact:
		infinite = false
	case TowardPositiveInfinity:
		infinite = !negative
	case TowardNegativeInfinity:
		infinite = negative
	}
	result := math.MaxFloat64
	if infinite {
		result = math.Inf(1)
	}
	if negative {
		result = -result
	}
	return result, Overflow | Inexact | Rounded | roundingDirection(infinite, negative)
}

// floorIndex returns the largest index b ≤ 0x7FEFFFFFFFFFFFFF with
// v(b) ≤ |d|, for 0 < |d| < 2^1024. It starts from a float estimate and
// gallops then bisects on exact comparisons, so the estimate affects only
// the number of comparisons.
func (c *dyadicComparer) floorIndex() uint64 {
	const top = binary64Top - 1
	b := min(math.Float64bits(c.estimate()), top)
	if c.compareIndex(b) >= 0 {
		// Gallop up to a bound whose value exceeds |d|; binary64Top does.
		low, step := b, uint64(1)
		high := uint64(binary64Top)
		for {
			probe := low + step
			if probe >= binary64Top {
				break
			}
			if c.compareIndex(probe) < 0 {
				high = probe
				break
			}
			low, step = probe, step*2
		}
		return c.bisect(low, high)
	}
	// Gallop down to an index whose value is at most |d|; index 0 (zero) is.
	high, step := b, uint64(1)
	low := uint64(0)
	for step <= high {
		probe := high - step
		if c.compareIndex(probe) >= 0 {
			low = probe
			break
		}
		high, step = probe, step*2
	}
	return c.bisect(low, high)
}

// bisect narrows v(low) ≤ |d| < v(high) to adjacent indices.
func (c *dyadicComparer) bisect(low, high uint64) uint64 {
	for high-low > 1 {
		mid := low + (high-low)/2
		if c.compareIndex(mid) >= 0 {
			low = mid
		} else {
			high = mid
		}
	}
	return low
}

// estimate approximates |d| from its leading 19 digits; the decimal
// exponent is already bounded to the binary64 decades, and each
// math.Pow10 factor stays finite and nonzero.
func (c *dyadicComparer) estimate() float64 {
	var lead uint64
	digits := 0
	cursor := newDigitCursor(&c.view)
	for digits < 19 {
		digit, ok := cursor.next()
		if !ok {
			break
		}
		lead = lead*10 + uint64(digit)
		digits++
	}
	scale := int(c.adjusted) - digits + 1
	value := float64(lead)
	switch {
	case scale < -300:
		value = value * 1e-300 * math.Pow10(scale+300)
	case scale > 300:
		value = value * 1e300 * math.Pow10(scale-300)
	default:
		value *= math.Pow10(scale)
	}
	return value
}

// CompareFloat64 orders d against the exact binary rational of f without
// converting either: −1, 0 or +1 as d is less than, equal to or greater
// than f. ±0 equals every zero, +Inf exceeds every Decimal and −Inf is
// below every Decimal; NaN is unordered and returns ErrInvalidOperation.
// The float nearest 0.1 exceeds the decimal 0.1.
func (d Decimal) CompareFloat64(f float64) (int, error) {
	cmp, _, err := d.compareFloat64Work(f)
	return cmp, err
}

// compareFloat64Work is CompareFloat64 that also reports the exact dyadic
// comparisons it spent.
func (d Decimal) compareFloat64Work(f float64) (int, dyadicWork, error) {
	switch {
	case math.IsNaN(f):
		return 0, dyadicWork{}, newError("CompareFloat64", ErrInvalidOperation)
	case math.IsInf(f, 1):
		return -1, dyadicWork{}, nil
	case math.IsInf(f, -1):
		return 1, dyadicWork{}, nil
	}
	negative, m, e := binary64Parts(f)
	switch {
	case m == 0 && d.isZero():
		return 0, dyadicWork{}, nil
	case d.isZero():
		if negative {
			return 1, dyadicWork{}, nil
		}
		return -1, dyadicWork{}, nil
	case m == 0 || d.negative() != negative:
		if d.negative() {
			return -1, dyadicWork{}, nil
		}
		return 1, dyadicWork{}, nil
	}
	var cmp int
	var work dyadicWork
	if place, ok := d.binary64PlaceSmall(); ok {
		// |d| lies in [v(index), v(index+1)) and equals v(index) only in
		// the exact class; bit patterns order the nonnegative doubles.
		magnitude := math.Float64bits(f) &^ (1 << 63)
		switch {
		case magnitude > place.index:
			cmp = -1
		case magnitude < place.index || place.class != divExactClass:
			cmp = 1
		}
	} else {
		cmp, work = d.compareBinary64(m, e)
	}
	if d.negative() {
		cmp = -cmp
	}
	return cmp, work, nil
}

// compareBinary64 returns sign(|d| − m·2^e) for nonzero d and 0 < m <
// 2^53 from d's 192-bit enclosure, with one exact comparison only when the
// enclosure contains the point.
func (d Decimal) compareBinary64(m uint64, e int64) (int, dyadicWork) {
	w, sticky, t, q, verdict := binary64Lead(d)
	if verdict != 0 { // beyond every double's magnitude
		return verdict, dyadicWork{}
	}
	lo, hi, exact, scale := binary64Enclosure(w, sticky, t, q)
	low := binary64CompareScaled(lo, scale, m, e)
	switch {
	case exact:
		return low, dyadicWork{}
	case low >= 0: // |d| > lo ≥ the point
		return 1, dyadicWork{}
	case binary64CompareScaled(hi, scale, m, e) <= 0:
		return -1, dyadicWork{}
	}
	c := newDyadicComparer(d)
	return c.compare(m, e), c.work
}

// float64PowerExponent is s with 5^q = (M + ε)·2^s for the table entry M:
// ⌊q·log2 5⌋ − 127, where ⌊q·log2 10⌋ = ⌊217706·q/2^16⌋ over the table.
func float64PowerExponent(q int64) int64 {
	return (q*217706)>>16 - q - 127
}

// float64PowerExact reports that the table entry for q is all of 5^q:
// 5^55 < 2^128 < 5^56.
func float64PowerExact(q int64) bool {
	return q >= 0 && q <= 55
}

// binary64Enclosure returns lo ≤ (w + f)·2^t·10^q ≤ hi as 192-bit
// multiples of 2^e. exact reports lo equal to the value, which needs both
// f = 0 and an exact power (5^q < 2^128, q ≥ 0); otherwise both bounds
// are strict. The width is below 2^−59 of the value.
func binary64Enclosure(w uint64, sticky bool, t, q int64) (lo, hi [3]uint64, exact bool, e int64) {
	entry := float64Powers[q-float64TableMin]
	mhi, mlo := entry[0], entry[1]
	lo = mul64x128(w, mhi, mlo)
	e = float64PowerExponent(q) + q + t
	exactPower := float64PowerExact(q)
	if exactPower && !sticky {
		return lo, lo, true, e
	}
	if !exactPower { // the table entry is truncated: 5^q < (M + 1)·2^s
		var carry uint64
		mlo, carry = bits.Add64(mlo, 1, 0)
		mhi += carry
	}
	hi = mul64x128(w, mhi, mlo)
	if sticky { // f < 1 adds less than one more (M + 1)
		var carry uint64
		hi[0], carry = bits.Add64(hi[0], mlo, 0)
		hi[1], carry = bits.Add64(hi[1], mhi, carry)
		hi[2] += carry
	}
	return lo, hi, false, e
}

// mul64x128 returns w·(hi·2^64 + lo) as little-endian words.
func mul64x128(w, hi, lo uint64) [3]uint64 {
	h0, l0 := bits.Mul64(w, lo)
	h1, l1 := bits.Mul64(w, hi)
	mid, carry := bits.Add64(h0, l1, 0)
	return [3]uint64{l0, mid, h1 + carry}
}

func bitLen192(x [3]uint64) int {
	switch {
	case x[2] != 0:
		return 128 + bits.Len64(x[2])
	case x[1] != 0:
		return 64 + bits.Len64(x[1])
	}
	return bits.Len64(x[0])
}

// binary64Position returns the half-ulp cell of v = x·2^e > 0 as 2·b + r:
// b is the largest bit pattern whose value is at most v and r is 1 when v
// lies at or above the midpoint over it. onBoundary reports v at the
// cell's lower end, a double or a midpoint. Every v ≥ 2^1024 is the cell
// 2·binary64Top.
func binary64Position(x [3]uint64, e int64) (pos uint64, onBoundary bool) {
	l := int64(bitLen192(x)) + e // 2^(l−1) ≤ v < 2^l
	if l > 1024 {
		return 2 * binary64Top, false
	}
	ulp := max(l-53, -1074)
	shift := ulp - 1 - e // cell = ⌊x/2^shift⌋ < 2^54
	var cell uint64
	switch {
	case shift <= 0: // then x < 2^54
		cell, onBoundary = x[0]<<uint(-shift), true
	case shift >= 192:
		cell = 0
	default:
		k, r := shift/64, uint(shift%64)
		cell = x[k] >> r
		if r > 0 && k < 2 {
			cell |= x[k+1] << (64 - r)
		}
		onBoundary = x[k]&(1<<r-1) == 0
		for _, word := range x[:k] {
			onBoundary = onBoundary && word == 0
		}
	}
	b := uint64(ulp+1074)<<52 + cell>>1
	return 2*b + cell&1, onBoundary
}

// binary64CompareScaled returns sign(x·2^ex − m·2^em) for x ≥ 2^127 and
// 0 < m < 2^64.
func binary64CompareScaled(x [3]uint64, ex int64, m uint64, em int64) int {
	nx, nm := bitLen192(x), bits.Len64(m)
	if lx, lm := int64(nx)+ex, int64(nm)+em; lx != lm {
		if lx < lm {
			return -1
		}
		return 1
	}
	var y [3]uint64
	shift := nx - nm
	k, r := shift/64, uint(shift%64)
	y[k] = m << r
	if r > 0 && k < 2 {
		y[k+1] = m >> (64 - r)
	}
	for i := 2; i >= 0; i-- {
		if x[i] != y[i] {
			if x[i] < y[i] {
				return -1
			}
			return 1
		}
	}
	return 0
}
