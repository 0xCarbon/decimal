// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"math"
	"math/big"
	"math/bits"
	"runtime"
)

// Rational interop: one scaled binary division at the math/big boundary
// produces the truncated quotient and its half class, and the shared
// division finishers round, guard, flag and publish it exactly as the Div family does.

const ratRemedy = "non-terminating rational: supply a finite-precision context (FromRatWithContext) or an explicit exponent (FromRatToExponent)"

// FromRat converts a rational exactly. A terminating rational (reduced
// denominator 2^a·5^b) is returned at the largest exponent not above zero
// that holds it (5/2 is 2.5, 100/1 is 100); a non-terminating rational
// returns a *Error with Condition Inexact and a remedy. A nil r or a
// source whose raw words are malformed returns ErrConversionSyntax.
func FromRat(r *big.Rat) (Decimal, error) {
	if n, d, ok := ratInlineOperands(r); ok {
		if q, ok := inlineDivExact(n, d); ok {
			return q, nil
		}
	}
	d, _, err := fromRatExact(r, limits{}, "FromRat")
	return d, err
}

// ratInlineOperands returns a well-formed rational whose nonzero numerator
// and positive denominator each fit one 64-bit word as two exponent-zero
// decimals: n/d is then the inline division kernels' shape, whose exact and
// to-exponent results at ideal exponent 0 are FromRat's and
// FromRatToExponent's. ok is false for nil, zero, malformed and wider
// sources; the general path owns those, every budget and every refusal.
func ratInlineOperands(r *big.Rat) (n, d Decimal, ok bool) {
	if r == nil {
		return Decimal{}, Decimal{}, false
	}
	num, den := r.Num(), r.Denom()
	nw, nok := ratWord(num)
	dw, dok := ratWord(den)
	if !nok || !dok || den.Sign() <= 0 {
		return Decimal{}, Decimal{}, false
	}
	return inlineDecimal(uint128{lo: nw}, 0, num.Sign() < 0), inlineDecimal(uint128{lo: dw}, 0, false), true
}

// ratWord is |x| when its well-formed words hold one nonzero 64-bit value.
func ratWord(x *big.Int) (uint64, bool) {
	words := x.Bits()
	if len(words) == 0 || len(words) > 64/bits.UintSize || words[len(words)-1] == 0 {
		return 0, false
	}
	v := uint64(words[0])
	if len(words) == 2 {
		v |= uint64(words[1]) << 32
	}
	return v, true
}

// FromRatWithContext rounds the rational once to the context precision
// under its mode, guards and traps, as DivWithContext rounds a quotient.
func FromRatWithContext(r *big.Rat, ctx Context) (Decimal, Conditions, error) {
	return fromRatContext(r, ctx, ctx.arith, "FromRatWithContext")
}

// FromRatToExponent rounds the rational once to exactly targetExponent under
// mode, with unlimited precision and no guards or traps.
func FromRatToExponent(r *big.Rat, targetExponent int32, mode RoundingMode) (Decimal, Conditions, error) {
	if mode <= Exact {
		if n, d, ok := ratInlineOperands(r); ok {
			if result, events, refused, ok := inlineDivToExponent(n, d, targetExponent, mode); ok && !refused {
				return result, events, nil
			}
		}
	}
	return fromRatToExponent(r, targetExponent, mode, limits{}, "FromRatToExponent")
}

// FromRatToExponentWithBudget is FromRatToExponent with checked quotas.
func FromRatToExponentWithBudget(r *big.Rat, targetExponent int32, mode RoundingMode, budget Budget) (Decimal, Conditions, error) {
	limit := budget.arith()
	if mode <= Exact {
		if n, d, ok := ratInlineOperands(r); ok {
			if result, events, refused, ok := inlineDivToExponent(n, d, targetExponent, mode); ok && !refused &&
				(limit.admits(inlineResultDigits, inlineRatWork) || ratToExponentInlineAdmitted(n.words.lo, d.words.lo, targetExponent, result, limit)) {
				return result, events, nil
			}
		}
	}
	return fromRatToExponent(r, targetExponent, mode, limit, "FromRatToExponentWithBudget")
}

// ratToExponentInlineAdmitted reports whether budget admits
// fromRatToExponent's charges for a one-word numerator n over a one-word
// denominator d at target, whose rounded result the word division
// produced: the plan's precharge and physical admission from the bit
// lengths, and the final N digits and W = B + 2N + 1 of the result. Those
// caps imply the earlier ones: the precharge alone, and the refusal of a
// quotient whose digit floor exceeds the digit cap, since the result has at
// least that many digits.
//
//go:noinline
func ratToExponentInlineAdmitted(n, d uint64, target int32, result Decimal, budget limits) bool {
	s := ratSource{bn: uint64(bits.Len64(n)), bd: uint64(bits.Len64(d))}
	p := s.plan(int64(target))
	if !p.ok || !ratAdmitted(p.operandWords, p.quotientBound+1) {
		return false
	}
	digits := uint64(1)
	if !result.isZero() {
		digits = inlineDigits(result.words)
	}
	work, ok := contextFinalCharge(p.charge, digits)
	return ok && budget.admits(digits, work)
}

// ratExactInlineAdmitted reports whether budget admits fromRatExact's
// charges for a one-word numerator n over a one-word denominator d whose
// exact quotient is q: the bare tariff of the bit lengths and the
// denominator's trailing zero bits, its physical admission, and the final
// N digits and W = B + 2N + 1 of the quotient, which imply the earlier
// caps.
//
//go:noinline
func ratExactInlineAdmitted(n, d uint64, q Decimal, budget limits) bool {
	bn, bd, a := uint64(bits.Len64(n)), uint64(bits.Len64(d)), uint64(bits.TrailingZeros64(d))
	bMax := ratBMax(bd, a)
	charge, words, bound, ok := ratExactTerms(bn, bd, bMax, max(a, bMax))
	if !ok || !ratAdmitted(words, bound+1) {
		return false
	}
	digits := inlineDigits(q.words)
	work, ok := contextFinalCharge(charge, digits)
	return ok && budget.admits(digits, work)
}

// ratContextInlineAdmitted reports whether budget certainly admits
// fromRatContextGeneral's charges for a one-word numerator n over a
// one-word denominator d under ctx: the exact attempt's charge when the
// precision exceeds the bit lengths, the division plan's at the same t′,
// their physical admissions, and the finisher's 2N+1 at N = p, the most
// digits a context result has. A budget below that bound stays with the
// general path, which may still admit a shorter or terminating result.
//
//go:noinline
func ratContextInlineAdmitted(n, d uint64, ctx *Context, budget limits) bool {
	s := ratSource{bn: uint64(bits.Len64(n)), bd: uint64(bits.Len64(d))}
	aLow, ok := ratAdjustedLow(s.bn, s.bd)
	if !ok {
		return false
	}
	precision := int64(ctx.precision)
	tPrime := aLow - precision + 1
	if ctx.guarded {
		tPrime = max(tPrime, int64(ctx.guards.Emin)-(precision-1))
	}
	var spent uint64
	if uint64(ctx.precision) > s.bn+s.bd {
		a := uint64(bits.TrailingZeros64(d))
		bMax := ratBMax(s.bd, a)
		charge, words, bound, ok := ratExactTerms(s.bn, s.bd, bMax, max(a, bMax))
		if !ok || !ratAdmitted(words, bound+1) {
			return false
		}
		spent = charge
	}
	p := s.plan(tPrime)
	charge, ok := arithmeticAdd(spent, p.charge)
	work, ok2 := contextFinalCharge(charge, uint64(ctx.precision))
	return p.ok && ok && ok2 && ratAdmitted(p.operandWords, p.quotientBound+1) && budget.admits(uint64(ctx.precision), work)
}

// ratSource is a validated rational n/d with d > 0. A nil d denotes
// denominator one, avoiding materialization before budget admission.
type ratSource struct {
	n, d     *big.Int
	bn, bd   uint64 // checked bit lengths of |n| and d
	negative bool
	zero     bool
}

func syntaxFailure(op string) (Decimal, Conditions, error) {
	return Decimal{}, 0, newError(op, ErrConversionSyntax)
}

// readRat validates the caller's rational through checked Bits views: a
// malformed zero-top word slice or a nonpositive denominator (possible only
// through raw reference writes) is invalid source input.
func readRat(r *big.Rat) (ratSource, bool) {
	if r.IsInt() {
		// Denom's implicit one must not escape into the source descriptor.
		// Its sign still needs validation: raw mutation can create -1,
		// and IsInt compares the magnitude alone.
		if r.Denom().Sign() <= 0 {
			return ratSource{}, false
		}
		n := r.Num()
		bn, ok := checkedBitLength(n)
		return ratSource{n: n, bn: bn, bd: 1, zero: bn == 0, negative: n.Sign() < 0}, ok
	}
	n, d := r.Num(), r.Denom()
	var s ratSource
	s.n, s.d = n, d
	if d.Sign() <= 0 {
		return s, false
	}
	var ok bool
	if s.bn, ok = checkedBitLength(n); !ok {
		return s, false
	}
	if s.bd, ok = checkedBitLength(d); !ok {
		return s, false
	}
	s.zero = s.bn == 0
	s.negative = n.Sign() < 0
	return s, true
}

// checkedBitLength derives the bit length of |x| from its Bits view with
// the checked metadata rules; it cannot wrap on 32-bit targets.
func checkedBitLength(x *big.Int) (uint64, bool) {
	words := x.Bits()
	if len(words) == 0 {
		return 0, true
	}
	top := words[len(words)-1]
	if top == 0 {
		return 0, false
	}
	return bigIntIngressSafeBitLength(uint64(len(words)), uint64(top), uint64(bits.UintSize))
}

// ratWords is the 64-bit word count of an n-bit magnitude.
func ratWords(bitCount uint64) uint64 { return (bitCount + 63) / 64 }

// ratPowerWords bounds the words of 10^k with the constant 332193/100000 >
// log2 10.
func ratPowerWords(k uint64) (uint64, bool) {
	hi, lo := bits.Mul64(k, 332193)
	if hi != 0 {
		return 0, false
	}
	return ratWords(lo/100000 + 1), true
}

// ratPowerCharge is the square-and-multiply bound ⌈4·w²/3⌉ + w for 10^k.
func ratPowerCharge(w uint64) (uint64, bool) {
	sq, ok := arithmeticMul(w, w)
	if !ok {
		return 0, false
	}
	four, ok := arithmeticMul(sq, 4)
	if !ok {
		return 0, false
	}
	return arithmeticAdd((four+2)/3, w)
}

// ratQuotientDivisionCharge is the schoolbook bound 2·(wq+1)·(wb+1) for a
// quotient of at most wq words by a divisor of at most wb words.
func ratQuotientDivisionCharge(wq, wb uint64) (uint64, bool) {
	t, ok := arithmeticMul(wq+1, wb+1)
	if !ok {
		return 0, false
	}
	return arithmeticMul(t, 2)
}

// ratDivisionCharge is 2·(wa−wb+2)·(wb+1) when wa ≥ wb, else wa+wb.
func ratDivisionCharge(wa, wb uint64) (uint64, bool) {
	if wa < wb {
		return arithmeticAdd(wa, wb)
	}
	t, ok := arithmeticMul(wa-wb+2, wb+1)
	if !ok {
		return 0, false
	}
	return arithmeticMul(t, 2)
}

// ratConversionCharge bounds converting a wq-word quotient to base-10^9
// limbs: Uq·⌈Uq/9⌉ with Uq = ⌊64·wq·30103/100000⌋+1.
func ratConversionCharge(wq uint64) (uint64, uint64, bool) {
	bitCount, ok := arithmeticMul(wq, 64)
	if !ok {
		return 0, 0, false
	}
	u, _, ok := binaryEnvelope(bitCount)
	if !ok {
		return 0, 0, false
	}
	c, ok := arithmeticMul(u, 1+(u-1)/9)
	return c, u, ok
}

// ratScratchBytes is the toolchain-pinned math/big scratch envelope for w
// planned operand words: 8·w·(8+⌈log2 w⌉) + 8 KiB. Go 1.27.1's recursive
// multiplication and Exp keep O(w·log w) cumulative temporaries, so a
// constant factor is falsified by measurement;
// TestFromRatScratchEnvelope pins the envelope over a sweep.
func ratScratchBytes(w uint64) (uint64, bool) {
	factor, ok := arithmeticMul(w, 8*(8+uint64(bits.Len64(w))))
	if !ok {
		return 0, false
	}
	return arithmeticAdd(factor, 8192)
}

// ratAdmitted checks the math/big scratch envelope plus the result limbs
// against the target's address window before the first allocation.
// quotientDigitsFloor is a lower bound on the digits of q = ⌊|n|·10^k/d⌋
// from the bit lengths alone, zero when they prove nothing. With C just
// below and C′ just above log2 10: for k ≥ 0, |n|·10^k ≥ 2^(bn−1+⌊kC⌋) and
// d < 2^bd; for k < 0, d·10^−k < 2^(bd+⌊−kC′⌋+1). Either way q ≥ 2^L − 1
// for the resulting L, and 2^L − 1 has at least ⌊L·0.30102⌋ digits.
func (s *ratSource) quotientDigitsFloor(k int64) uint64 {
	const scale = 10_000_000_000_000_000
	gain, loss := s.bn-1, s.bd
	if k >= 0 {
		hi, lo := bits.Mul64(uint64(k), 33219280948873623)
		if hi >= scale {
			return 0
		}
		floor, _ := bits.Div64(hi, lo, scale)
		gain += floor
	} else {
		hi, lo := bits.Mul64(uint64(-k), 33219280948873624)
		if hi >= scale {
			return 0
		}
		floor, _ := bits.Div64(hi, lo, scale)
		loss += floor + 1
	}
	if gain <= loss {
		return 0
	}
	hi, lo := bits.Mul64(gain-loss, 30102)
	digits, _ := bits.Div64(hi, lo, 100000)
	return digits
}

func ratAdmitted(operandWords, resultDigits uint64) bool {
	maxObject, maxAddress, ok := bigIntRuntimeLimits(runtime.GOOS, runtime.GOARCH, uint64(bits.UintSize))
	if !ok {
		return false
	}
	scratch, ok := ratScratchBytes(operandWords)
	if !ok || scratch > maxAddress {
		return false
	}
	limbs := 1 + (resultDigits-1)/9
	if limbs > uint64(math.MaxInt)/4 {
		return false
	}
	result, ok := bigIntRoundObject(limbs*4 + 64)
	if !ok || result > maxObject {
		return false
	}
	total, ok := arithmeticAdd(scratch, result)
	return ok && total <= maxAddress
}

// ratPlan is a planned scaled division at exponent t.
type ratPlan struct {
	tiny          bool
	k             int64
	charge        uint64
	operandWords  uint64
	quotientBound uint64 // quotient digit bound Uq
	ok            bool
}

// plan classifies the path at exponent t (ideal exponent 0) and computes the
// precharge and the physical operand words from bit lengths only.
func (s *ratSource) plan(t int64) ratPlan {
	var p ratPlan
	if t == math.MinInt64 {
		return p
	}
	p.k = -t
	wn, wd := ratWords(s.bn), ratWords(s.bd)
	if p.k < 0 {
		j := uint64(-p.k)
		// ⌊j·C⌋ with C = 33219280948873623/10^16 < log2 10.
		hi, lo := bits.Mul64(j, 33219280948873623)
		if hi >= 10_000_000_000_000_000 {
			p.tiny, p.charge, p.ok = true, 1, true // j·C exceeds any bit length
			return p
		}
		floor, _ := bits.Div64(hi, lo, 10_000_000_000_000_000)
		if s.bn+1 < s.bd+floor {
			p.tiny, p.charge, p.ok = true, 1, true
			return p
		}
		wj, ok := ratPowerWords(j)
		if !ok {
			return p
		}
		wD := wd + wj
		power, ok1 := ratPowerCharge(wj)
		scale, ok2 := arithmeticMul(wd, wj)
		// wD over-counts D = d·10^j's words, so the quotient's words come
		// from D's least bit length, bd + ⌊j·C⌋: q < 2^(bn − bits(D) + 1).
		wq := uint64(1)
		if s.bn+1 > s.bd+floor {
			wq = ratWords(s.bn + 1 - s.bd - floor)
		}
		division, ok3 := ratQuotientDivisionCharge(wq, wD)
		conversion, uq, ok4 := ratConversionCharge(wq)
		charge, ok5 := checkedSum(power, scale, division, conversion, wn, wD)
		p.operandWords, _ = checkedSum(wn, wD, wq)
		p.charge, p.quotientBound = charge, uq
		p.ok = ok1 && ok2 && ok3 && ok4 && ok5
		return p
	}
	wk, ok := ratPowerWords(uint64(p.k))
	if !ok {
		return p
	}
	wN := wn + wk
	power, ok1 := ratPowerCharge(wk)
	scale, ok2 := arithmeticMul(wn, wk)
	division, ok3 := ratDivisionCharge(wN, wd)
	wq := uint64(1)
	if wN >= wd {
		wq = wN - wd + 1
	}
	conversion, uq, ok4 := ratConversionCharge(wq)
	charge, ok5 := checkedSum(power, scale, division, conversion, wN, wd)
	p.operandWords, _ = checkedSum(wN, wd, wq)
	p.charge, p.quotientBound = charge, uq
	p.ok = ok1 && ok2 && ok3 && ok4 && ok5
	return p
}

// digits computes q = trunc(|n|·10^k / d) (or |n| / (d·10^−k)) and the half
// class of the discarded part, then converts q to base-10^9 limbs with a
// spare limb for the finisher's rounding carry.
func (s *ratSource) digits(p ratPlan) ([]uint32, divHalf) {
	if p.tiny {
		return make([]uint32, 0, 2), divBelow
	}
	// The signed numerator is used directly: QuoRem truncates toward zero,
	// so |q| and |rem| are the magnitudes' quotient and remainder.
	denominator := s.d
	if denominator == nil {
		denominator = big.NewInt(1) // admitted work, never the precharge
	}
	var dividend, divisor *big.Int
	if p.k >= 0 {
		dividend = new(big.Int).Exp(big.NewInt(10), big.NewInt(p.k), nil)
		dividend.Mul(dividend, s.n)
		divisor = denominator
	} else {
		divisor = new(big.Int).Exp(big.NewInt(10), big.NewInt(-p.k), nil)
		divisor.Mul(divisor, denominator)
		dividend = s.n
	}
	q, rem := new(big.Int).QuoRem(dividend, divisor, new(big.Int))
	q.Abs(q)
	rem.Abs(rem)
	class := divExactClass
	if rem.Sign() != 0 {
		switch rem.Lsh(rem, 1).Cmp(divisor) {
		case -1:
			class = divBelow
		case 0:
			class = divHalfClass
		default:
			class = divAbove
		}
	}
	return bigToLimbs(q), class
}

// ratTextConversionWords is the quotient size above which bigToLimbs uses
// math/big's subquadratic text conversion instead of word-by-word limb
// multiplication.
const ratTextConversionWords = 32

// bigToLimbs converts a nonnegative big.Int to little-endian base-10^9
// limbs, trimmed, with one spare zero limb of capacity.
func bigToLimbs(x *big.Int) []uint32 { return bigToLimbsCounted(x, nil) }

func bigToLimbsCounted(x *big.Int, count *ratCount) []uint32 {
	words := x.Bits()
	if len(words) > ratTextConversionWords {
		// math/big's divide-and-conquer text conversion is subquadratic;
		// its digits are packed into limbs nine at a time.
		text := x.Append(nil, 10)
		out := make([]uint32, 1+(len(text)-1)/9+1)
		used := 0
		for end := len(text); end > 0; end -= 9 {
			var limb uint32
			for _, c := range text[max(end-9, 0):end] {
				limb = limb*10 + uint32(c-'0')
			}
			out[used] = limb
			used++
		}
		return out[:used]
	}
	return bigToLimbsByWords(x, count)
}

// bigToLimbsByWords is bigToLimbs by repeated limb multiplication, which
// allocates only the result.
func bigToLimbsByWords(x *big.Int, count *ratCount) []uint32 {
	words := x.Bits()
	n := uint64(len(words)) * uint64(bits.UintSize)
	u, _, _ := binaryEnvelope(max(n, 1))
	out := make([]uint32, 1+(u-1)/9+1)
	used := 0
	chunks := n / 32
	for chunkIndex := chunks; chunkIndex > 0; chunkIndex-- {
		position := chunkIndex - 1
		var chunk uint32
		if bits.UintSize == 32 {
			chunk = uint32(words[int(position)])
		} else {
			word := uint64(words[int(position/2)])
			if position%2 == 0 {
				chunk = uint32(word)
			} else {
				chunk = uint32(word >> 32)
			}
		}
		carry := uint64(chunk)
		for i := range used {
			scalar := uint64(out[i])*(1<<32) + carry
			out[i] = uint32(scalar % decimalLimbBase)
			carry = scalar / decimalLimbBase
		}
		for carry != 0 {
			out[used] = uint32(carry % decimalLimbBase)
			carry /= decimalLimbBase
			used++
		}
		if count != nil {
			count.limbSteps += uint64(used)
		}
	}
	return out[:used]
}

// ratZero publishes the unsigned zero at exponent e under the one-digit,
// one-work tariff.
func ratZero(e int32, budget limits, op string) (Decimal, Conditions, error) {
	if !admitted(budget.MaxDigits, 1, true) || !contextFinalWork(1, 1, budget.MaxWork) {
		return contextFailure(op, ErrInsufficientStorage)
	}
	return zeroDecimal(e), 0, nil
}

func fromRatToExponent(r *big.Rat, target int32, mode RoundingMode, budget limits, op string) (Decimal, Conditions, error) {
	if r == nil {
		return syntaxFailure(op)
	}
	if mode > Exact {
		return quantizeInvalidMode(op)
	}
	s, ok := readRat(r)
	if !ok {
		return syntaxFailure(op)
	}
	if s.zero {
		return ratZero(target, budget, op)
	}
	t := int64(target)
	p := s.plan(t)
	if !p.ok || budget.MaxWork != 0 && p.charge > budget.MaxWork || !ratAdmitted(p.operandWords, p.quotientBound+1) {
		return contextFailure(op, ErrInsufficientStorage)
	}
	// A quotient that certainly exceeds the digit cap is refused before
	// the division builds it. The Exact mode first has to learn whether the
	// quotient is exact, which decides its refusal.
	if budget.MaxDigits != 0 && mode != Exact && !p.tiny && s.quotientDigitsFloor(p.k) > budget.MaxDigits {
		return contextFailure(op, ErrInsufficientStorage)
	}
	q, class := s.digits(p)
	return finishToExponent(q, class, t, 0, s.negative, mode, p.charge, budget, op)
}

// ratAdjustedLow is the lower bound a_lo: floorDiv((Δ−1)·c, 10^18) with the constant
// that underestimates log10 2 for the sign of Δ−1, so a_lo ≤ adjusted.
func ratAdjustedLow(bn, bd uint64) (int64, bool) {
	if bn > math.MaxInt64 || bd > math.MaxInt64 {
		return 0, false
	}
	x := int64(bn) - int64(bd) - 1
	const low, high = 301029995663981195, 301029995663981196
	magnitude, c := uint64(x), uint64(low)
	if x < 0 {
		magnitude, c = uint64(-x), high
	}
	hi, lo := bits.Mul64(magnitude, c)
	if hi >= 1_000_000_000_000_000_000 {
		return 0, false
	}
	q, rem := bits.Div64(hi, lo, 1_000_000_000_000_000_000)
	if x >= 0 {
		return int64(q), true
	}
	if rem != 0 {
		q++
	}
	return -int64(q), true
}

// fromRatContext serves a one-word numerator over a one-word denominator
// with the inline division kernels at ideal exponent 0: the exact quotient
// at precision 0, as FromRat does, and otherwise DivWithContext's rounding
// of the same quotient, which the general path reaches through the same
// finisher. A budget is admitted by ratExactInlineAdmitted at precision 0
// and by ratContextInlineAdmitted at a finite one; every other budget,
// shape and refusal stays with the general path.
func fromRatContext(r *big.Rat, ctx Context, budget limits, op string) (Decimal, Conditions, error) {
	if ctx.precision == 0 {
		if n, d, ok := ratInlineOperands(r); ok {
			if q, ok := inlineDivExact(n, d); ok && (budget == (limits{}) || ratExactInlineAdmitted(n.words.lo, d.words.lo, q, budget)) {
				return q, 0, nil
			}
		}
		return fromRatExact(r, budget, op)
	}
	if ctx.precision <= inlineDivMaxPrecision {
		if n, d, ok := ratInlineOperands(r); ok && (budget == (limits{}) || ratContextInlineAdmitted(n.words.lo, d.words.lo, &ctx, budget)) {
			if result, conditions, err, ok := inlineDivContext(n, d, &ctx, op); ok {
				return result, conditions, err
			}
		}
	}
	return fromRatContextGeneral(r, ctx, budget, op)
}

// fromRatContextGeneral is the general FromRatWithContext path at a finite
// precision: it owns every budget charge and refusal.
func fromRatContextGeneral(r *big.Rat, ctx Context, budget limits, op string) (Decimal, Conditions, error) {
	if r == nil {
		return syntaxFailure(op)
	}
	s, ok := readRat(r)
	if !ok {
		return syntaxFailure(op)
	}
	if s.zero {
		return ratZero(0, budget, op)
	}
	precision := int64(ctx.precision)
	aLow, ok := ratAdjustedLow(s.bn, s.bd)
	if !ok {
		return contextFailure(op, ErrInsufficientStorage)
	}
	// With a_lo ≤ adjusted ≤ a_lo+1, q at t′ = a_lo−p+1 has p or p+1 digits.
	tPrime := aLow - precision + 1
	var etiny int64
	if ctx.guarded {
		etiny = int64(ctx.guards.Emin) - (precision - 1)
		tPrime = max(tPrime, etiny)
	}
	// Exact-first: a terminating value has at most bn+bd digits, so above
	// that precision it is exact and only a non-terminating value needs p
	// digits. Work then never grows with a precision the result does not
	// use. Each phase is precharged and admitted before it allocates; the
	// division phase is charged on top of the exact attempt.
	var spent uint64
	if bound, ok := arithmeticAdd(s.bn, s.bd); ok && uint64(ctx.precision) > bound {
		e := s.exactPlan()
		if e.ok && e.a-e.shared <= 1<<31 {
			if budget.MaxWork != 0 && e.charge > budget.MaxWork || !ratAdmitted(e.operandWords, e.quotientBound+1) {
				return contextFailure(op, ErrInsufficientStorage)
			}
			q, m, terminating := s.exactDigits(e)
			if terminating {
				return finishContext(q, divExactClass, -int64(m), etiny, 0, s.negative, &ctx, e.charge, budget, op)
			}
			spent = e.charge
		}
	}
	p := s.plan(tPrime)
	charge, ok := arithmeticAdd(spent, p.charge)
	if !p.ok || !ok || budget.MaxWork != 0 && charge > budget.MaxWork || !ratAdmitted(p.operandWords, p.quotientBound+1) {
		return contextFailure(op, ErrInsufficientStorage)
	}
	if spent != 0 && ctx.rounding == Exact {
		// The exact attempt proved the value does not terminate, so Exact
		// refuses without the division (a guarded overflow refuses alike).
		return contextExactRefusal(op)
	}
	q, class := s.digits(p)
	return finishContext(q, class, tPrime, etiny, 0, s.negative, &ctx, charge, budget, op)
}

func fromRatExact(r *big.Rat, budget limits, op string) (Decimal, Conditions, error) {
	if r == nil {
		return syntaxFailure(op)
	}
	s, ok := readRat(r)
	if !ok {
		return syntaxFailure(op)
	}
	if s.zero {
		return ratZero(0, budget, op)
	}
	e := s.exactPlan()
	if e.a-e.shared > 1<<31 {
		return contextFailure(op, ErrExponentRange)
	}
	if !e.ok || budget.MaxWork != 0 && e.charge > budget.MaxWork || !ratAdmitted(e.operandWords, e.quotientBound+1) {
		return contextFailure(op, ErrInsufficientStorage)
	}
	// An integer is its own exact result: one that certainly exceeds the
	// digit cap is refused before it is converted. A fraction first has to
	// show that it terminates, which the work cap bounds.
	if budget.MaxDigits != 0 && s.d == nil && s.quotientDigitsFloor(0) > budget.MaxDigits {
		return contextFailure(op, ErrInsufficientStorage)
	}
	q, m, terminating := s.exactDigits(e)
	if m > 1<<31 {
		return contextFailure(op, ErrExponentRange)
	}
	if !terminating {
		return Decimal{}, 0, conditionError(op, Inexact, ratRemedy)
	}
	result, err := finishExact(q, -int64(m), m, s.negative, e.charge, budget, op)
	return result, 0, err
}

// ratExactPlan is the bare path's precharge and operand words.
type ratExactPlan struct {
	a, shared, bMax uint64
	charge          uint64
	operandWords    uint64
	quotientBound   uint64
	ok              bool
}

// exactPlan computes the bare path's plan from bit lengths and trailing
// zero counts only. Only the twos are exact before the loop; twos
// shared by a non-reduced pair (written through Num or Denom) cancel by
// value, so exponent checks use a − shared.
func (s *ratSource) exactPlan() ratExactPlan {
	e := ratExactPlan{}
	if s.d != nil {
		e.a = uint64(s.d.TrailingZeroBits())
	}
	e.shared = min(uint64(s.n.TrailingZeroBits()), e.a)
	e.bMax = ratBMax(s.bd, e.a)
	e.charge, e.operandWords, e.quotientBound, e.ok = ratExactTerms(s.bn, s.bd, e.bMax, max(e.a, e.bMax))
	return e
}

// ratBMax bounds the fives of a denominator of bd bits with a trailing zero
// bits: ⌊(bd − a)·log5 2⌋.
func ratBMax(bd, a uint64) uint64 {
	hi, lo := bits.Mul64(bd-a, 430676558073393051)
	q, _ := bits.Div64(hi, lo, 1_000_000_000_000_000_000)
	return q
}

// ratExactTerms is the bare FromRat tariff for bit lengths bn,
// bd, a factor-5 loop of bMax iterations and a scale 10^m, m = max(a, bMax);
// shared by exactPlan and the estimators.
func ratExactTerms(bn, bd, bMax, m uint64) (charge, operandWords, quotientBound uint64, ok bool) {
	wn, wd := ratWords(bn), ratWords(bd)
	loop, ok1 := arithmeticMul(bMax, wd+1)
	quo, ok2 := ratDivisionCharge(wn, wd)
	wm, ok3 := ratPowerWords(m)
	power, ok4 := ratPowerCharge(wm)
	scale, ok5 := arithmeticMul(wn, wm)
	conversion, uc, ok6 := ratConversionCharge(wn + wm)
	charge, ok7 := checkedSum(loop, quo, power, scale, conversion, wn, wd)
	operands, ok8 := checkedSum(wn, wd, wn, wm)
	return charge, operands, uc, ok1 && ok2 && ok3 && ok4 && ok5 && ok6 && ok7 && ok8
}

// ratExactWorst is the bare tariff's maximum over every denominator of bd
// bits, whatever its trailing zero bits a ∈ [0, bd−1]: the
// loop term decreases in a (maximum at a = 0), and max(a, bMax(a)) is
// V-shaped (maximum at an endpoint), so the sum of per-term maxima is
// computed in O(1).
func ratExactWorst(bn, bd uint64) (charge, operandWords, quotientBound uint64, ok bool) {
	bMax := ratBMax(bd, 0)
	m := bMax
	if bd > 0 {
		m = max(bMax, bd-1)
	}
	return ratExactTerms(bn, bd, bMax, m)
}

// exactDigits runs the admitted bare path: it removes the fives of d by
// the precharged loop, tests whether d″ divides n, and returns the exact
// coefficient n·2^(m−a)·5^(m−b)/d″ with its exponent −m. terminating is
// false, with no coefficient, when the value does not terminate.
// ratCount records the FromRat family's own loop trip counts for tests;
// production passes nil, as divCount does for the division
// kernel.
type ratCount struct {
	fives     uint64 // successful factor-5 divisions (each removes ≥ 1 five)
	limbSteps uint64 // bigToLimbsByWords inner steps
}

// ratFivePrefix is the number of fives the valuation loops remove one at a
// time before continuing on fiveLadder: a valuation up to it costs exactly
// the single-five loop, divisions and allocations included.
const ratFivePrefix = 32

// fiveLadder removes the rest of a valuation once v fives are removed one
// at a time: it divides x > 0 by 5 while 5 divides it and v < limit, and
// returns the quotient, the spare buffer and the final v. quotient and rem
// are scratch; the result and the spare buffer are x and quotient in some
// order, and five holds 5 and is never modified.
//
// Ascending, x is divided by p_k = 5^(2^k) while it divides and p_{k+1} =
// p_k² still fits in x and the limit; when the ascent stops at k, the
// fives still to remove are t = min(ν5(x), limit−v) < 2^(k+1) (or < 2^k
// when p_k itself was declined), and a descent over p_k, …, p_0 removes
// exactly the binary digits of t, because p_i is taken iff 5^(2^i) | x
// and 2^i ≤ limit−v, that is iff t ≥ 2^i. The ladder takes O(log v)
// divisions whose divisors never exceed x or 5^limit, so its word
// operations stay within the charged loop term (limit or bMax)·(words+1)
// of the single-five loop it replaces; its powers sum to less than twice
// the largest, which is at most x.
func fiveLadder(x, quotient, rem, five *big.Int, limit, v uint64, count *ratCount) (*big.Int, *big.Int, uint64) {
	var powers [64]*big.Int
	powers[0] = five
	take := func(k int) bool {
		p := powers[k]
		if limit-v < 1<<k || p.BitLen() > x.BitLen() {
			return false // the limit, or p > x > 0, excludes p
		}
		quotient.QuoRem(x, p, rem)
		if rem.Sign() != 0 {
			return false
		}
		x, quotient = quotient, x
		v += 1 << k
		if count != nil {
			count.fives++
		}
		return true
	}
	k := 0
	for take(k) {
		p := powers[k]
		if k+1 == len(powers) || (limit-v)>>1 < 1<<k || 2*p.BitLen()-1 > x.BitLen() {
			k++ // p_{k+1} > x or beyond the limit: t < 2^(k+1)
			break
		}
		powers[k+1] = new(big.Int).Mul(p, p)
		k++
	}
	for k--; k >= 0; k-- {
		take(k)
	}
	return x, quotient, v
}

func (s *ratSource) exactDigits(e ratExactPlan) (q []uint32, m uint64, terminating bool) {
	return s.exactDigitsCounted(e, nil)
}

func (s *ratSource) exactDigitsCounted(e ratExactPlan, count *ratCount) (q []uint32, m uint64, terminating bool) {
	denominator := s.d
	if denominator == nil {
		denominator = big.NewInt(1) // admitted work, never the precharge
	}
	reduced := new(big.Int).Rsh(denominator, uint(e.a))
	five := big.NewInt(5)
	// One quotient and one remainder are reused across the loop, so its
	// allocation is O(words), not O(b·words).
	quotient, rem := new(big.Int), new(big.Int)
	// The single-five loop, inline: a valuation reaching ratFivePrefix
	// continues on the block ladder.
	var b uint64
	for {
		if b == ratFivePrefix {
			reduced, quotient, b = fiveLadder(reduced, quotient, rem, five, math.MaxUint64, b, count)
			break
		}
		quotient.QuoRem(reduced, five, rem)
		if rem.Sign() != 0 {
			break
		}
		reduced, quotient = quotient, reduced
		b++
		if count != nil {
			count.fives++
		}
	}
	a := e.a - e.shared
	m = max(a, b)
	if m > 1<<31 {
		return nil, m, false
	}
	numerator := new(big.Int).Abs(s.n)
	numerator.Rsh(numerator, uint(e.shared))
	quotient.QuoRem(numerator, reduced, rem) // quotient and reduced are distinct
	if rem.Sign() != 0 {
		return nil, m, false
	}
	quotient.Lsh(quotient, uint(m-a))
	quotient.Mul(quotient, new(big.Int).Exp(five, new(big.Int).SetUint64(m-b), nil))
	return bigToLimbsCounted(quotient, count), m, true
}

// Rat sets z to the exactly equal value in lowest terms and returns z; a
// nil z allocates a new *big.Rat, as big.Float.Rat does. On a refusal z is
// not modified.
func (d Decimal) Rat(z *big.Rat) (*big.Rat, error) {
	return d.ratWithBudget(z, Budget{}, "Rat")
}

// RatWithBudget is Rat with copied quotas: MaxInputDigits caps the
// coefficient digits, MaxDigits caps the numerator's and the
// denominator's decimal lengths, and MaxWork caps the conversion and
// reduction work, all checked before allocating.
func (d Decimal) RatWithBudget(z *big.Rat, budget Budget) (*big.Rat, error) {
	return d.ratWithBudget(z, budget, "RatWithBudget")
}

func (d Decimal) ratWithBudget(dst *big.Rat, budget Budget, op string) (*big.Rat, error) {
	if d.isZero() {
		return ratDestination(dst).SetInt64(0), nil
	}
	if budget.MaxInputDigits|budget.MaxDigits|budget.MaxWork == 0 || d.ratInlineAdmitted(budget) {
		if out, ok := d.ratInline(dst); ok {
			return out, nil
		}
	}
	return d.ratGeneral(dst, budget, op)
}

// ratGeneral is the general Rat conversion of a nonzero value: it owns
// every budget charge and refusal.
func (d Decimal) ratGeneral(dst *big.Rat, budget Budget, op string) (*big.Rat, error) {
	refuse := func(code ErrorCode) (*big.Rat, error) { return nil, newError(op, code) }
	v := coefficientViewOf(d)
	digits, ok := arithmeticDigits(&v)
	if !ok || budget.MaxInputDigits != 0 && digits > budget.MaxInputDigits {
		return refuse(ErrInsufficientStorage)
	}
	if d.exponent() >= 0 {
		// Integral: numerator c·10^e over 1, through the BigInt egress path
		// and its envelope.
		n, err := d.bigIntWithBudget(nil, budget, op)
		if err != nil {
			return nil, err
		}
		// The Rat takes the fresh words by reference (SetBits), without the
		// copy SetInt makes; SetInt64 resets its denominator to 1.
		out := ratDestination(dst).SetInt64(1)
		out.Num().SetBits(n.Bits())
		if d.negative() {
			out.Num().Neg(out.Num())
		}
		return out, nil
	}
	// c·10^−j: strip trailing decimal zeros on the limbs first.
	j := uint64(-int64(d.exponent()))
	z := min(countTrailingZeros(&v), j)
	j -= z
	numeratorDigits := digits - z
	if budget.MaxDigits != 0 && (numeratorDigits > budget.MaxDigits || j+1 > budget.MaxDigits) {
		return refuse(ErrInsufficientStorage)
	}
	work, wc, wj, ok := ratEgressCharge(digits, j, z)
	if !ok || budget.MaxWork != 0 && work > budget.MaxWork || !ratAdmitted(wc+wj, numeratorDigits) {
		return refuse(ErrInsufficientStorage)
	}
	integral := d.withExponent(0).withNegative(false)
	if z > 0 {
		reduced, _, err := integral.QuantizeWithContext(int32(z), Context{})
		if err != nil {
			return nil, err
		}
		integral = reduced
		integral = integral.withExponent(0)
	}
	c, err := integral.bigIntWithBudget(nil, Budget{}, op)
	if err != nil {
		return nil, err
	}
	// Remove common factors of 2 and 5 with the denominator 2^j·5^j.
	twos := min(uint64(c.TrailingZeroBits()), j)
	c.Rsh(c, uint(twos))
	five := big.NewInt(5)
	q, rem := new(big.Int), new(big.Int) // reused: O(words) allocation
	fives := uint64(0)
	for fives < j {
		if fives == ratFivePrefix && j-fives >= ratFivePrefix {
			c, _, fives = fiveLadder(c, q, rem, five, j, fives, nil)
			break
		}
		q.QuoRem(c, five, rem)
		if rem.Sign() != 0 {
			break
		}
		c, q = q, c
		fives++
	}
	den := new(big.Int).Exp(five, new(big.Int).SetUint64(j-fives), nil)
	den.Lsh(den, uint(j-twos))
	// The pair is already in lowest terms. The Rat takes both integers'
	// words by reference: no Set copies and no SetFrac normalization.
	// SetInt64 initializes the denominator so Denom returns a reference.
	out := ratDestination(dst).SetInt64(1)
	out.Num().SetBits(c.Bits())
	if d.negative() {
		out.Num().Neg(out.Num())
	}
	out.Denom().SetBits(den.Bits())
	return out, nil
}

// ratInline is the Rat of a one-word coefficient c at an exponent −19 ≤ e
// < 0: c/(2^j·5^j) is reduced in one word (shared twos by a shift, shared
// fives one at a time) and both integers, each below 2^64, are stored
// without a math/big division or power. ok is false for every other
// shape. It charges nothing: the caller admits a budget.
func (d Decimal) ratInline(dst *big.Rat) (*big.Rat, bool) {
	c, e := d.words.lo, d.exponent()
	if d.slow != nil || d.words.hi != 0 || c == 0 || e >= 0 || e < -19 {
		return nil, false
	}
	j := uint(-e)
	twos := min(uint(bits.TrailingZeros64(c)), j)
	c >>= twos
	fives := uint(0)
	for fives < j && c%5 == 0 {
		c /= 5
		fives++
	}
	// SetInt64 initializes the denominator so Denom returns a reference.
	out := ratDestination(dst).SetInt64(1)
	out.Num().SetUint64(c)
	if d.negative() {
		out.Num().Neg(out.Num())
	}
	out.Denom().SetUint64(float64Fives[j-fives] << (j - twos))
	return out, true
}

// ratInlineAdmitted reports whether budget admits the general Rat
// conversion of a value of ratInline's shape, a nonzero one-word
// coefficient c at exponent −j with 1 ≤ j ≤ 19: by the bound of every such
// conversion's charges, or else by this one's, which are the input-digit
// cap on its digits, the digit cap on the numerator left by the z stripped
// zeros and on the j−z+1 digits of the denominator, the tariff of those
// counts, and its physical admission. It is false for every other shape.
//
//go:noinline
func (d Decimal) ratInlineAdmitted(budget Budget) bool {
	c, e := d.words.lo, d.exponent()
	if d.slow != nil || d.words.hi != 0 || c == 0 || e >= 0 || e < -19 {
		return false
	}
	if budget.admitsConversion(inlineRatEgressDigits, inlineRatEgressWork) {
		return true
	}
	j := uint64(-e)
	digits := uint64(wordDigits(c))
	var z uint64
	for z < j && c%10 == 0 {
		c /= 10
		z++
	}
	j -= z
	numeratorDigits := digits - z
	if budget.MaxInputDigits != 0 && digits > budget.MaxInputDigits ||
		budget.MaxDigits != 0 && (numeratorDigits > budget.MaxDigits || j+1 > budget.MaxDigits) {
		return false
	}
	work, wc, wj, ok := ratEgressCharge(digits, j, z)
	return ok && (budget.MaxWork == 0 || work <= budget.MaxWork) && ratAdmitted(wc+wj, numeratorDigits)
}

// ratDestination is dst, or a new *big.Rat for a nil dst; callers take it
// only once the conversion can no longer refuse.
func ratDestination(dst *big.Rat) *big.Rat {
	if dst == nil {
		return new(big.Rat)
	}
	return dst
}

// ratEgressCharge is Rat's tariff for a d-digit coefficient at exponent
// −(j+z) with z stripped trailing zeros, shared with
// the estimators: W_BigInt of the stripped coefficient, the
// factor-5 loop (j+1)·wc, the power P(wj) and wj, plus the limb strip d when
// z > 0; wc and wj are the numerator's and 10^j's word bounds.
func ratEgressCharge(digits, j, z uint64) (work, wc, wj uint64, ok bool) {
	numeratorDigits := digits - z
	wc = ratWords(numeratorDigits*332193/100000 + 1)
	wj, okj := ratPowerWords(j)
	power, okp := ratPowerCharge(wj)
	loop, okl := arithmeticMul(j+1, wc)
	convert, okc := bigIntEgressWork(numeratorDigits, numeratorDigits)
	var strip uint64
	if z > 0 {
		strip = digits
	}
	work, okw := checkedSum(convert, loop, power, wj, strip)
	return work, wc, wj, okj && okp && okl && okc && okw
}

// countTrailingZeros counts trailing decimal zeros of a nonzero coefficient.
func countTrailingZeros(v *coefficientView) uint64 {
	var z uint64
	for i := range v.count {
		limb := v.limb(i)
		if limb == 0 {
			z += 9
			continue
		}
		for limb%10 == 0 {
			limb /= 10
			z++
		}
		break
	}
	return z
}
