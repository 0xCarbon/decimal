// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"math"
	"math/bits"
)

// Parse accepts one liberal decimal grammar with no caller-imposed budget.
// Checked resource refusals and invalid literals return a typed Error.
// A string or a []byte is parsed in place, without a copy. Parse is generic:
// as an untyped function value write Parse[string] (or Parse[[]byte]).
func Parse[T Literal](s T) (Decimal, error) {
	return parseWithBudget(s, textLimits{}, "Parse")
}

// MustParse is for trusted literals. It panics with the Error returned
// by Parse, including checked resource refusal for a valid literal.
func MustParse[T Literal](s T) Decimal {
	d, err := Parse(s)
	if err != nil {
		panic(err)
	}
	return d
}

// parseWithBudget is the one decimal parser. Byte input is copied only into
// an *Error; a successful parse retains nothing from s. A short literal
// within both budgets returns from parseInline's single pass;
// everything else, including every refusal, is parseGeneral's.
func parseWithBudget[T Literal](s T, budget textLimits, op string) (Decimal, error) {
	if len(s) <= inlineParseMax && (budget.MaxInputBytes == 0 || uint64(len(s)) <= budget.MaxInputBytes) {
		if c, exponent, negative, significant, ok := parseInline(s); ok &&
			(budget.MaxDigits == 0 || uint64(significant) <= budget.MaxDigits) {
			return inlineDecimal(uint128{lo: c}, exponent, negative), nil
		}
	}
	return parseGeneral(s, budget, op)
}

// parseGeneral owns the parse semantics: the input-byte budget, the
// grammar (scanDecimal), the exponent range, the coefficient-digit budget
// and storage in either band.
func parseGeneral[T Literal](s T, budget textLimits, op string) (Decimal, error) {
	fail := func(code ErrorCode, condition Conditions) (Decimal, error) {
		return Decimal{}, parseFailure(s, op, code, condition)
	}
	if budget.MaxInputBytes != 0 && uint64(len(s)) > budget.MaxInputBytes {
		return fail(ErrInsufficientStorage, InsufficientStorage)
	}
	parts, result := scanDecimal(s)
	switch result {
	case scanSyntax:
		return fail(ErrConversionSyntax, ConversionSyntax)
	case scanRange:
		return fail(ErrExponentRange, 0)
	}

	// Leading zeros take scan work but no coefficient storage; written
	// trailing zeros count as significant digits.
	integral, fraction := parts.integral, parts.fraction
	integral = integral[zeroSpan(integral):]
	if len(integral) == 0 {
		fraction = fraction[zeroSpan(fraction):]
	}
	significant := max(len(integral)+len(fraction), 1)
	if budget.MaxDigits != 0 && uint64(significant) > budget.MaxDigits {
		return fail(ErrInsufficientStorage, InsufficientStorage)
	}
	limbCount := 1 + (significant-1)/9
	maxInt := int(^uint(0) >> 1)
	if limbCount > maxInt/4 {
		return fail(ErrInsufficientStorage, InsufficientStorage)
	}
	exponent := int32(parts.exponent)
	if len(integral) == 0 && len(fraction) == 0 {
		return zeroDecimal(exponent), nil // zero keeps its requested exponent, without a sign
	}
	// At most 39 digits can fit below 2^128; the inline accumulation reports
	// overflow for the 39-digit values at or above it.
	if significant <= 39 {
		if lo, hi, ok := accumulateWords(0, 0, integral); ok {
			if lo, hi, ok = accumulateWords(lo, hi, fraction); ok {
				return inlineDecimal(uint128{lo, hi}, exponent, parts.negative), nil
			}
		}
	}
	if limbCount <= slowSmallLimbs {
		h := new(slowCoefficient)
		h.limbs = h.small[:limbCount]
		fillCoefficientLimbs(h.limbs, parts)
		return slowDecimal(h, exponent, parts.negative), nil
	}
	return slowDecimal(&slowCoefficient{limbs: coefficientLimbs(parts, limbCount)}, exponent, parts.negative), nil
}

// inlineParseMax bounds the literals parseInline tries. A longer literal
// either has more than 19 significant digits or pads them with zeros or
// exponent digits; it defers after one comparison, so long inputs pay
// nothing for the fast path.
const inlineParseMax = 30

// parseInline is parseWithBudget's single-pass fast path: one
// left-to-right pass over at most inlineParseMax bytes of
// [+-]?D*(.D*)?([eE][+-]?D{1,9})? with at least one coefficient digit and
// at most 19 significant digits, which fit one word. It returns the
// coefficient, the effective exponent (|lexical| < 10^9 and fewer than 30
// fraction digits keep it inside int32), the written sign and the
// significant-digit count parseWithBudget charges: leading zeros are free,
// written trailing zeros count, and a zero counts one digit. ok=false only
// means defer: the general path owns every error and every literal outside
// these bounds.
func parseInline[T Literal](s T) (c uint64, exponent int32, negative bool, significant int, ok bool) {
	if len(s) == 0 || len(s) > inlineParseMax {
		return 0, 0, false, 0, false
	}
	i := 0
	if s[0] == '-' || s[0] == '+' {
		negative = s[0] == '-'
		i = 1
	}
	// Leading zeros add nothing to c, so c wraps only past 19 significant
	// digits, and such a literal defers below.
	start := i
	for ; len(s)-i >= 8; i += 8 {
		x := load64(s[i : i+8])
		if !eightDigitsIn(x) {
			break
		}
		c = c*100_000_000 + uint64(eightDigits(x))
	}
	for ; i < len(s) && s[i]-'0' <= 9; i++ {
		c = c*10 + uint64(s[i]-'0')
	}
	integral := i - start
	digits, fraction := integral, 0
	if i < len(s) && s[i] == '.' {
		i++
		for ; len(s)-i >= 8; i += 8 {
			x := load64(s[i : i+8])
			if !eightDigitsIn(x) {
				break
			}
			c = c*100_000_000 + uint64(eightDigits(x))
		}
		for ; i < len(s) && s[i]-'0' <= 9; i++ {
			c = c*10 + uint64(s[i]-'0')
		}
		fraction = i - start - integral - 1
		digits += fraction
	}
	if digits == 0 {
		return 0, 0, false, 0, false
	}
	if digits > 19 {
		// Only leading zeros can keep the significant digits within 19.
		lead := zeroSpan(s[start : start+integral])
		if lead == integral && fraction != 0 {
			lead += zeroSpan(s[i-fraction : i])
		}
		if digits-lead > 19 {
			return 0, 0, false, 0, false
		}
	}
	if i < len(s) {
		if s[i]|0x20 != 'e' { // only 'e' and 'E' map to 'e'
			return 0, 0, false, 0, false
		}
		i++
		negativeExp := false
		if i < len(s) && (s[i] == '+' || s[i] == '-') {
			negativeExp = s[i] == '-'
			i++
		}
		if n := len(s) - i; n == 0 || n > 9 {
			return 0, 0, false, 0, false
		}
		for ; i < len(s); i++ {
			d := s[i] - '0'
			if d > 9 {
				return 0, 0, false, 0, false
			}
			exponent = exponent*10 + int32(d)
		}
		if negativeExp {
			exponent = -exponent
		}
	}
	// c < 10^19 now, and its decimal width is the significant-digit count:
	// leading zeros are absent from c and trailing zeros are in it.
	significant = bits.Len64(c) * 1233 >> 12 // ⌊log10 2^len⌋, within one
	if c >= pow10Words[significant] {
		significant++
	}
	return c, exponent - int32(fraction), negative, max(significant, 1), true
}

// eightDigitsIn reports whether the little-endian word x holds eight ASCII
// digits, by swarDigitSpan's SWAR classification.
func eightDigitsIn(x uint64) bool {
	const high = 0x8080808080808080
	low := x &^ high
	return (^((low|high)-0x3030303030303030)|(low+0x4646464646464646)|x)&high == 0
}

// accumulateWords returns (hi:lo)*10^len(digits) + digits when the result
// stays below 2^128. Digits are consumed in 19-digit chunks that fit one
// word, eight at a time by SWAR (eightDigits). The words stay scalars so
// both remain in registers across the loop.
func accumulateWords[T Literal](lo, hi uint64, digits T) (uint64, uint64, bool) {
	for len(digits) != 0 {
		k := min(len(digits), 19)
		var chunk uint64
		i := 0
		for ; k-i >= 8; i += 8 {
			chunk = chunk*100_000_000 + uint64(eightDigits(load64(digits[i:i+8])))
		}
		for ; i < k; i++ {
			chunk = chunk*10 + uint64(digits[i]-'0')
		}
		digits = digits[k:]
		carry, low := bits.Mul64(lo, pow10Words[k])
		overflow, high := bits.Mul64(hi, pow10Words[k])
		low, c := bits.Add64(low, chunk, 0)
		high, c = bits.Add64(high, carry, c)
		if overflow != 0 || c != 0 {
			return lo, hi, false
		}
		lo, hi = low, high
	}
	return lo, hi, true
}

// coefficientLimbs forms a fresh immutable little-endian base-10^9 slice.
// It reads the two scanner spans directly, with no joined coefficient copy,
// converting each nine-digit group with one SWAR eight-digit step.
func coefficientLimbs[T Literal](parts decimalParts[T], count int) []uint32 {
	limbs := make([]uint32, count)
	fillCoefficientLimbs(limbs, parts)
	return limbs
}

// fillCoefficientLimbs writes the spans' digits into limbs, which holds
// exactly their limb count. Limbs are nine-digit groups counted from the
// last fraction digit, so the fraction's full groups come first, then at
// most one group straddling the decimal point, then the integral's full
// groups and its leading partial group. Each run is its own loop and every
// full group is one nineDigits step.
func fillCoefficientLimbs[T Literal](limbs []uint32, parts decimalParts[T]) {
	integral, fraction := parts.integral, parts.fraction
	i, end := 0, len(fraction)
	for ; i < len(limbs) && end >= 9; i++ {
		end -= 9
		limbs[i] = nineDigits(fraction[end], load64(fraction[end+1:end+9]))
	}
	if i == len(limbs) {
		return
	}
	if end != 0 { // the group straddles the decimal point
		start := max(len(integral)-(9-end), 0)
		limbs[i] = digitGroup(integral[start:])*decimalPowers[end] + digitGroup(fraction[:end])
		i++
		end = start
	} else {
		end = len(integral)
	}
	for ; i < len(limbs) && end >= 9; i++ {
		end -= 9
		limbs[i] = nineDigits(integral[end], load64(integral[end+1:end+9]))
	}
	if i < len(limbs) {
		limbs[i] = digitGroup(integral[:end])
	}
}

// nineDigits converts nine validated ASCII digits: the leading digit lead
// times 10^8 plus the eight that follow it, loaded into x, by one SWAR
// step. It is not generic, so it inlines into each group loop.
func nineDigits(lead byte, x uint64) uint32 {
	return uint32(lead-'0')*100_000_000 + eightDigits(x)
}

// digitGroup converts at most nine validated ASCII digits.
func digitGroup[T Literal](s T) uint32 {
	var v uint32
	if len(s) >= 8 {
		for i := range len(s) - 8 {
			v = v*10 + uint32(s[i]-'0')
		}
		return v*100_000_000 + eightDigits(load64(s[len(s)-8:]))
	}
	for i := range len(s) {
		v = v*10 + uint32(s[i]-'0')
	}
	return v
}

// eightDigits converts eight ASCII digits, most significant byte first in
// memory (little-endian word), by pairwise SWAR multiply-adds.
func eightDigits(x uint64) uint32 {
	x -= 0x3030303030303030
	x = x*10 + x>>8 // adjacent digit pairs in the low byte of each 16 bits
	x = ((x&0x000000FF000000FF)*(100+(1_000_000<<32)) + (x>>16&0x000000FF000000FF)*(1+(10_000<<32))) >> 32
	return uint32(x)
}

// ParseToExponent rounds the literal's exact value once to the given
// exponent under mode, the shape of SQL CAST(text AS DECIMAL(p,s)).
// Whenever Parse succeeds it equals Parse followed by Quantize in value,
// cohort, Conditions and error identity; it also rounds literals whose
// effective exponent lies below int32 (1e-99999999999 at −2 is 0.00). A
// nonzero literal whose effective exponent exceeds int32 returns
// ErrExponentRange. Work is O(len(s) + result digits) and only the result's
// digits are stored, so a long literal rounded to a short result allocates
// nothing when the result is inline. Untrusted text should use
// ParseToExponentWithBudget: a far target pads up to 2^32 zeros.
func ParseToExponent[T Literal](s T, exponent int32, mode RoundingMode) (Decimal, Conditions, error) {
	return parseToExponent(s, exponent, mode, textLimits{}, "ParseToExponent")
}

// ParseToExponentWithBudget is ParseToExponent with Budget quotas:
// MaxInputBytes counts len(s) before scanning, and MaxDigits caps
// the result's coefficient digits before it is allocated.
func ParseToExponentWithBudget[T Literal](s T, exponent int32, mode RoundingMode, budget Budget) (Decimal, Conditions, error) {
	return parseToExponent(s, exponent, mode, budget.text(), "ParseToExponentWithBudget")
}

// ParseWithContext rounds the literal's exact value once to the context
// precision with its guards and traps (GDA to-number in a non-clamping
// context): a value that fits the precision keeps its written exponent
// unless guards raise it to Etiny, precision 0 converts exactly, and guards
// resolve out-of-range exponents by Subnormal, Underflow or Overflow. A zero keeps its written exponent
// unclamped. Work is O(len(s)) plus the result's digits.
func ParseWithContext[T Literal](s T, ctx Context) (Decimal, Conditions, error) {
	return parseWithContext(s, ctx, textLimits{MaxInputBytes: ctx.inputBytes, MaxDigits: ctx.arith.MaxDigits}, "ParseWithContext")
}

// parsedDigits is a scanned literal as a rounding source: its significant
// digits (leading zeros stripped, trailing zeros kept) as two input spans,
// their count D, and the saturated effective exponent E.
type parsedDigits[T Literal] struct {
	parts  decimalParts[T]
	digits uint64
}

// scanRoundingSource applies the input-byte budget, then the grammar; an
// effective exponent outside int32 is kept (saturated) for the caller.
func scanRoundingSource[T Literal](s T, budget textLimits, op string) (parsedDigits[T], error) {
	if budget.MaxInputBytes != 0 && uint64(len(s)) > budget.MaxInputBytes || uint64(len(s)) >= 1<<58 {
		return parsedDigits[T]{}, parseFailure(s, op, ErrInsufficientStorage, InsufficientStorage)
	}
	parts, result := scanDecimal(s)
	if result == scanSyntax {
		return parsedDigits[T]{}, parseFailure(s, op, ErrConversionSyntax, ConversionSyntax)
	}
	parts.integral = parts.integral[zeroSpan(parts.integral):]
	if len(parts.integral) == 0 {
		parts.fraction = parts.fraction[zeroSpan(parts.fraction):]
	}
	return parsedDigits[T]{parts: parts, digits: uint64(len(parts.integral) + len(parts.fraction))}, nil
}

// parseFailure builds the text family's error. A resource refusal of byte
// input never copies the input, so its Input is empty; every other error,
// and every error of a string (which is not copied), carries the input.
func parseFailure[T Literal](s T, op string, code ErrorCode, condition Conditions) error {
	if _, text := any(s).(string); !text && code == ErrInsufficientStorage {
		return newError(op, code)
	}
	return &Error{Op: op, Input: string(s), Code: code, Condition: condition}
}

// digit returns significant digit i (0 is the most significant).
func (p *parsedDigits[T]) digit(i uint64) uint32 {
	if n := uint64(len(p.parts.integral)); i < n {
		return uint32(p.parts.integral[i] - '0')
	} else {
		return uint32(p.parts.fraction[i-n] - '0')
	}
}

// nonzeroFrom reports whether any significant digit at index i or later is
// nonzero, scanning the rest of both spans without allocating.
func (p *parsedDigits[T]) nonzeroFrom(i uint64) bool {
	if i >= p.digits {
		return false
	}
	n := uint64(len(p.parts.integral))
	if i < n {
		rest := p.parts.integral[i:]
		if zeroSpan(rest) < len(rest) {
			return true
		}
		i = n
	}
	rest := p.parts.fraction[i-n:]
	return zeroSpan(rest) < len(rest)
}

// prefix fills r with the leading k significant digits (1 ≤ k ≤ D); r
// holds exactly their limb count.
func (p *parsedDigits[T]) prefix(r []uint32, k uint64) {
	view := p.parts
	if n := uint64(len(view.integral)); k <= n {
		view.integral, view.fraction = view.integral[:k], view.fraction[:0]
	} else {
		view.fraction = view.fraction[:k-n]
	}
	fillCoefficientLimbs(r, view)
}

// class is the half class of the digits from index k on, which a rounding
// at digit k discards: the guard digit k against 5 and the sticky rest.
func (p *parsedDigits[T]) class(k uint64) divHalf {
	if k >= p.digits {
		return divExactClass
	}
	guard, sticky := p.digit(k), p.nonzeroFrom(k+1)
	switch {
	case guard == 0 && !sticky:
		return divExactClass
	case guard < 5:
		return divBelow
	case guard == 5 && !sticky:
		return divHalfClass
	default:
		return divAbove
	}
}

// retainedScratch returns scratch for the retained leading digits plus the
// finisher's carry limb: the 48-limb stack buffer when it fits, otherwise
// an admitted heap buffer.
func retainedScratch(stack *[divStackLimbs]uint32, digits uint64) ([]uint32, bool) {
	count := uint64(0)
	if digits > 0 {
		count = 1 + (digits-1)/9
	}
	if count+1 <= divStackLimbs {
		return stack[:count], true
	}
	if !divAdmitted(count+1, digits) {
		return nil, false
	}
	return make([]uint32, count, count+1), true
}

// retainedDigits builds R and its class for a rounding that discards the
// last drop significant digits (drop ≥ 0) or appends pad zeros (pad > 0).
func (p *parsedDigits[T]) retainedDigits(stack *[divStackLimbs]uint32, drop, pad uint64, budget textLimits) ([]uint32, divHalf, bool) {
	var keep uint64
	if drop < p.digits {
		keep = p.digits - drop
	}
	total, ok := arithmeticAdd(keep, pad)
	if !ok || !admitted(budget.MaxDigits, total, true) {
		return nil, 0, false
	}
	r, ok := retainedScratch(stack, total)
	if !ok {
		return nil, 0, false
	}
	class := divBelow
	switch {
	case keep == 0 && drop == p.digits:
		class = p.class(0)
		if class == divExactClass { // unreachable for a nonzero literal
			class = divBelow
		}
	case keep == 0:
	default:
		lowCount := 1 + (keep-1)/9
		p.prefix(r[:lowCount], keep)
		class = p.class(keep)
		if pad > 0 {
			r = shiftLimbsLeft(r, int(lowCount), pad)
		}
	}
	return r, class, true
}

// shiftLimbsLeft multiplies the value in r's first n limbs by 10^pad in
// place; r holds exactly the padded limb count and the carry fits.
func shiftLimbsLeft(r []uint32, n int, pad uint64) []uint32 {
	var carry uint64
	factor := uint64(decimalPowers[pad%9])
	for i := range n {
		product := uint64(r[i])*factor + carry
		r[i] = uint32(product % decimalLimbBase)
		carry = product / decimalLimbBase
	}
	if carry != 0 {
		r[n] = uint32(carry)
		n++
	}
	whole := int(pad / 9)
	copy(r[whole:whole+n], r[:n])
	clear(r[:whole])
	return trimLimbs(r[:whole+n])
}

func parseToExponent[T Literal](s T, target int32, mode RoundingMode, budget textLimits, op string) (Decimal, Conditions, error) {
	if mode > Exact {
		return quantizeInvalidMode(op)
	}
	// A short literal without a digit cap is Parse's single pass followed by
	// the inline Quantize kernel, the documented equivalence; every refusal
	// and every wider shape stays with the rounding source below.
	// A digit cap of at least 39 admits every inline result: the retained
	// digits and the rounded coefficient both stay below 2^128.
	if (budget.MaxDigits == 0 || budget.MaxDigits >= inlineResultDigits) && len(s) <= parseRoundInlineMax && (budget.MaxInputBytes == 0 || uint64(len(s)) <= budget.MaxInputBytes) {
		if len(s) <= inlineParseMax {
			if c, exponent, negative, _, ok := parseInline(s); ok {
				if c == 0 {
					return zeroDecimal(target), 0, nil
				}
				if result, events, refused, ok := inlineQuantize(inlineDecimal(uint128{lo: c}, exponent, negative), target, mode); ok && !refused {
					return result, events, nil
				}
			}
		}
		// Up to 38 bytes the exact value is inline in two words.
		if exact, ok := parseExactWords(s); ok {
			if exact.isZero() {
				return zeroDecimal(target), 0, nil
			}
			if result, events, refused, ok := inlineQuantize(exact, target, mode); ok && !refused {
				return result, events, nil
			}
		}
	}
	return parseToExponentSource(s, target, mode, budget, op)
}

// parseToExponentSource is parseToExponent over the rounding source: it
// owns every budget refusal and every shape.
func parseToExponentSource[T Literal](s T, target int32, mode RoundingMode, budget textLimits, op string) (Decimal, Conditions, error) {
	src, err := scanRoundingSource(s, budget, op)
	if err != nil {
		return Decimal{}, 0, err
	}
	if src.digits == 0 {
		return zeroDecimal(target), 0, nil
	}
	e := src.parts.exponent
	if e > math.MaxInt32 {
		return Decimal{}, 0, parseFailure(s, op, ErrExponentRange, 0)
	}
	t := int64(target)
	var drop, pad uint64
	if t >= e {
		drop = uint64(t - e)
	} else {
		pad = uint64(e - t)
	}
	var stack [divStackLimbs]uint32
	r, class, ok := src.retainedDigits(&stack, drop, pad, budget)
	if !ok {
		return Decimal{}, 0, parseFailure(s, op, ErrInsufficientStorage, InsufficientStorage)
	}
	return parseOutcome(s, op)(finishToExponent(r, class, t, e, src.parts.negative, mode, 0, limits{MaxDigits: budget.MaxDigits}, op))
}

func parseWithContext[T Literal](s T, ctx Context, budget textLimits, op string) (Decimal, Conditions, error) {
	if ctx.precision == 0 {
		// Precision 0 is exact Parse in one pass, with Parse's byte, digit,
		// grammar and range refusals: parseWithBudget's
		// body, inlined here to keep the call depth of a direct Parse.
		if len(s) <= inlineParseMax && (budget.MaxInputBytes == 0 || uint64(len(s)) <= budget.MaxInputBytes) {
			if c, exponent, negative, significant, ok := parseInline(s); ok &&
				(budget.MaxDigits == 0 || uint64(significant) <= budget.MaxDigits) {
				return inlineDecimal(uint128{lo: c}, exponent, negative), 0, nil
			}
		}
		d, err := parseGeneral(s, budget, op)
		return d, 0, err
	}
	// A short literal that already fits the precision, the digit cap and the
	// guards' normal range is published as written with no Conditions: the
	// finisher has nothing to round, raise or flag. Zero keeps its exponent.
	if len(s) <= inlineParseMax && (budget.MaxInputBytes == 0 || uint64(len(s)) <= budget.MaxInputBytes) {
		if c, exponent, negative, significant, ok := parseInline(s); ok &&
			(budget.MaxDigits == 0 || uint64(significant) <= budget.MaxDigits) {
			adjusted := int64(exponent) + int64(significant) - 1
			if c == 0 || uint64(significant) <= uint64(ctx.precision) &&
				(!ctx.guarded || adjusted >= int64(ctx.guards.Emin) && adjusted <= int64(ctx.guards.Emax)) {
				return inlineDecimal(uint128{lo: c}, exponent, negative), 0, nil
			}
		}
	}
	// A literal of at most 38 bytes has an inline exact value: parse it
	// exactly and round the words once, as context arithmetic rounds an
	// exact inline result. A refusal of the exact parse, a zero and every
	// guard, Exact or range case defer to the rounding source, and so does
	// a budget that source refuses.
	if len(s) <= parseRoundInlineMax && (budget.MaxInputBytes == 0 || uint64(len(s)) <= budget.MaxInputBytes) {
		if exact, ok := parseExactWords(s); ok && !exact.isZero() && parseRoundDigitsAdmitted(exact, ctx.precision, budget.MaxDigits) {
			if contextExactFits(exact, ctx) {
				return exact, 0, nil
			}
			if rounded, events, ok := contextRoundInline(exact, ctx); ok {
				return contextOutcome(rounded, events, ctx.traps, op)
			}
		}
	}
	return parseRounded(s, ctx, budget, op)
}

// parseRoundInlineMax bounds the literals whose exact value parseWithContext
// rounds in words: 38 bytes hold at most 38 digits, below 2^128.
const parseRoundInlineMax = 38

// parseRoundDigitsAdmitted reports whether a digit cap admits the rounding
// source's work on a nonzero literal whose exact value the words hold, for
// the outcomes the word rounding returns: the source caps the digits it
// retains, the literal's D digits when they fit the precision and p digits
// when it rounds, which is the result's count either way.
func parseRoundDigitsAdmitted(exact Decimal, precision uint32, maxDigits uint64) bool {
	return maxDigits == 0 || min(inlineDigits(exact.words), uint64(precision)) <= maxDigits
}

// parseExactWords is parseGeneral for a literal of at most
// parseRoundInlineMax bytes, whose exact value is inline. It allocates
// nothing: ok is false for a syntax or exponent-range refusal, which the
// caller's general path reports.
func parseExactWords[T Literal](s T) (Decimal, bool) {
	parts, result := scanDecimal(s)
	if result != scanOK {
		return Decimal{}, false
	}
	// Leading zeros add nothing, and 38 digits cannot overflow two words.
	lo, hi, ok := accumulateWords(0, 0, parts.integral)
	if ok {
		lo, hi, ok = accumulateWords(lo, hi, parts.fraction)
	}
	exponent := int32(parts.exponent)
	if lo|hi == 0 {
		return zeroDecimal(exponent), ok // zero carries no sign
	}
	return inlineDecimal(uint128{lo, hi}, exponent, parts.negative), ok
}

// parseRounded is parseWithContext at a nonzero precision for every
// literal: it scans the rounding source and rounds it once.
func parseRounded[T Literal](s T, ctx Context, budget textLimits, op string) (Decimal, Conditions, error) {
	src, err := scanRoundingSource(s, budget, op)
	if err != nil {
		return Decimal{}, 0, err
	}
	e := src.parts.exponent
	outside := e < math.MinInt32 || e > math.MaxInt32
	if src.digits == 0 {
		// Zero keeps its exponent unclamped and publishes through the Parse
		// path.
		if outside {
			return Decimal{}, 0, parseFailure(s, op, ErrExponentRange, 0)
		}
		d, err := parseWithBudget(s, textLimits{MaxDigits: budget.MaxDigits}, op)
		return d, 0, err
	}
	precision := int64(ctx.precision)
	var etiny int64
	if ctx.guarded {
		etiny = int64(ctx.guards.Emin) - (precision - 1)
	}
	var stack [divStackLimbs]uint32
	digits := int64(src.digits)
	// Round at t′ = E + (D − p) when the literal exceeds the precision, and
	// at E when it fits (exact first); guards raise t′ to Etiny either way,
	// so only the result's digits are materialized and budgeted.
	tPrime := e
	if digits > precision {
		tPrime = e + digits - precision
	}
	if ctx.guarded {
		tPrime = max(tPrime, etiny)
	}
	drop := uint64(tPrime - e)
	r, class, ok := src.retainedDigits(&stack, drop, 0, budget)
	if !ok {
		return Decimal{}, 0, parseFailure(s, op, ErrInsufficientStorage, InsufficientStorage)
	}
	return parseOutcome(s, op)(finishContext(r, class, tPrime, etiny, e, src.parts.negative, &ctx, 0, limits{MaxDigits: budget.MaxDigits}, op))
}

// parseOutcome adapts a finisher's resource or range refusal to the parse
// family's error (parseFailure); conditions, traps and context errors pass
// through.
func parseOutcome[T Literal](s T, op string) func(Decimal, Conditions, error) (Decimal, Conditions, error) {
	return func(d Decimal, c Conditions, err error) (Decimal, Conditions, error) {
		// Operation refusals carry a code; context errors and trapped
		// condition sets pass through unchanged.
		if e, ok := err.(*Error); ok && e.Code != 0 && e.Code != ErrInvalidContext {
			if _, text := any(s).(string); !text && e.Code == ErrInsufficientStorage {
				return Decimal{}, 0, e // a resource refusal of bytes never copies them
			}
			return Decimal{}, 0, &Error{Op: op, Input: string(s), Code: e.Code, Condition: e.Condition}
		}
		return d, c, err
	}
}
