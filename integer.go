// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"math/big"
	"math/bits"
	"reflect"
	"runtime"
)

// FromInt64 constructs an exact decimal integer at exponent zero.
func FromInt64(value int64) Decimal { return New(value, 0) }

// FromUint64 constructs an exact decimal integer at exponent zero.
func FromUint64(value uint64) Decimal {
	return inlineDecimal(uint128{lo: value}, 0, false)
}

// Int64 returns the exact numeric integer. A fractional or out-of-range
// value returns zero and a typed error without materializing a large integer.
func (d Decimal) Int64() (int64, error) {
	if d.isZero() {
		return 0, nil
	}
	limit := uint64(1<<63 - 1)
	if d.negative() {
		limit++
	}
	if d.slow == nil && d.words.hi == 0 {
		magnitude, code := wordInteger(d.words.lo, d.exponent(), limit)
		if code != 0 {
			return 0, newError("Int64", code)
		}
		return signedMagnitude(magnitude, d.negative()), nil
	}
	return d.int64Limbs(limit)
}

// int64Limbs is the general limb path for coefficients of two or more words.
func (d Decimal) int64Limbs(limit uint64) (int64, error) {
	v := coefficientViewOf(d)
	digits, ok := arithmeticDigits(&v)
	if !ok {
		return 0, newError("Int64", ErrIntegerRange)
	}
	var drop, extra uint64
	if d.exponent() < 0 {
		drop = uint64(-int64(d.exponent()))
		if drop >= digits || !integerLowDigitsZero(&v, drop) {
			return 0, newError("Int64", ErrNonIntegral)
		}
	} else {
		extra = uint64(d.exponent())
	}
	resultDigits := digits - drop + extra
	if resultDigits > 19 {
		return 0, newError("Int64", ErrIntegerRange)
	}
	magnitude, ok := integerMagnitude(&v, digits, drop, extra, limit)
	if !ok {
		return 0, newError("Int64", ErrIntegerRange)
	}
	return signedMagnitude(magnitude, d.negative()), nil
}

// signedMagnitude negates in two's complement; 2^63 maps to MinInt64.
func signedMagnitude(magnitude uint64, negative bool) int64 {
	if negative {
		return int64(-magnitude)
	}
	return int64(magnitude)
}

// wordInteger converts a nonzero one-word coefficient times 10^exponent to an
// exact integer at most limit. It returns ErrNonIntegral before range.
func wordInteger(coefficient uint64, exponent int32, limit uint64) (uint64, ErrorCode) {
	if exponent < 0 {
		if exponent < -19 {
			return 0, ErrNonIntegral // 10^20 exceeds every nonzero word
		}
		divisor := pow10Words[-exponent]
		if coefficient%divisor != 0 {
			return 0, ErrNonIntegral
		}
		coefficient /= divisor
	} else if exponent > 0 {
		if exponent > 19 {
			return 0, ErrIntegerRange
		}
		high, low := bits.Mul64(coefficient, pow10Words[exponent])
		if high != 0 {
			return 0, ErrIntegerRange
		}
		coefficient = low
	}
	if coefficient > limit {
		return 0, ErrIntegerRange
	}
	return coefficient, 0
}

// Uint64 returns the exact numeric integer or an error if the value is
// fractional or outside the unsigned 64-bit range.
func (d Decimal) Uint64() (uint64, error) {
	if d.isZero() {
		return 0, nil
	}
	if d.slow == nil && d.words.hi == 0 {
		limit := ^uint64(0)
		if d.negative() {
			limit = 0 // any nonzero negative integer is out of range
		}
		magnitude, code := wordInteger(d.words.lo, d.exponent(), limit)
		if code != 0 {
			return 0, newError("Uint64", code)
		}
		return magnitude, nil
	}
	return d.uint64Limbs()
}

// uint64Limbs is the general limb path for coefficients of two or more words.
func (d Decimal) uint64Limbs() (uint64, error) {
	v := coefficientViewOf(d)
	digits, ok := arithmeticDigits(&v)
	if !ok {
		return 0, newError("Uint64", ErrIntegerRange)
	}
	var drop, extra uint64
	if d.exponent() < 0 {
		drop = uint64(-int64(d.exponent()))
		if drop >= digits || !integerLowDigitsZero(&v, drop) {
			return 0, newError("Uint64", ErrNonIntegral)
		}
	} else {
		extra = uint64(d.exponent())
	}
	if d.negative() || digits-drop+extra > 20 {
		return 0, newError("Uint64", ErrIntegerRange)
	}
	magnitude, ok := integerMagnitude(&v, digits, drop, extra, ^uint64(0))
	if !ok {
		return 0, newError("Uint64", ErrIntegerRange)
	}
	return magnitude, nil
}

func integerLowDigitsZero(v *coefficientView, count uint64) bool {
	whole, part := count/9, count%9
	for i := range whole {
		if v.limb(int(i)) != 0 {
			return false
		}
	}
	return part == 0 || v.limb(int(whole))%decimalPowers[part] == 0
}

func integerMagnitude(v *coefficientView, digits, drop, extra, limit uint64) (uint64, bool) {
	var magnitude uint64
	for position := digits; position > drop; {
		position--
		digit := uint64(quantizeDigit(v, position))
		if magnitude > (limit-digit)/10 {
			return 0, false
		}
		magnitude = magnitude*10 + digit
	}
	for range extra {
		if magnitude > limit/10 {
			return 0, false
		}
		magnitude *= 10
	}
	return magnitude, true
}

// bigIntPage is Go 1.27.1's 8 KiB page (internal/runtime/gc.PageShift),
// which upper-bounds every small size class and the large-object rounding of
// a planned allocation.
const bigIntPage = uint64(1 << 13)

// bigIntObjectBytes conservatively covers big.Int's bool and slice header.
const bigIntObjectBytes = uint64(64)

func bigIntRoundObject(size uint64) (uint64, bool) {
	withRemainder, ok := arithmeticAdd(size, bigIntPage-1)
	return withRemainder &^ (bigIntPage - 1), ok
}

// bigIntRuntimeLimits mirrors Go 1.27.1 runtime/malloc.go's heapAddrBits and
// maxAlloc expressions; on 32-bit targets a combined plan is further limited
// by MaxInt. These limits describe addressability, not available memory, and
// must be renewed on a toolchain change.
func bigIntRuntimeLimits(goos, goarch string, wordBits uint64) (maxObject, maxAddress uint64, ok bool) {
	var heapBits uint
	switch wordBits {
	case 32:
		heapBits = 32
		if goarch == "mips" || goarch == "mipsle" {
			heapBits = 31
		}
	case 64:
		heapBits = 48
		if goarch == "wasm" {
			heapBits = 32
		} else if goos == "ios" && goarch == "arm64" {
			heapBits = 40
		}
	default:
		return 0, 0, false
	}
	addressSpace := uint64(1) << heapBits
	maxObject = addressSpace
	maxAddress = addressSpace - 1
	if wordBits == 32 {
		maxObject--
		maxAddress = 1<<31 - 1
	}
	return maxObject, maxAddress, true
}

// bigIntTarget is the physical plan for one Go target: its big.Word width,
// Go int maximum and the runtime's object and address ceilings. Live calls
// use the running target; synthetic probes plan other targets on any host.
type bigIntTarget struct{ wordBits, maxInt, maxAddressBytes, maxObjectBytes uint64 }

type bigIntIngressPlan struct {
	u, w, limbs, sourceBytes, outputBytes, holderBytes         uint64
	sourceRoundedBytes, outputRoundedBytes, holderRoundedBytes uint64
}

func bigIntIngressRuntimeTarget() bigIntTarget {
	return bigIntTargetFor(runtime.GOOS, runtime.GOARCH, uint64(bits.UintSize))
}

// bigIntTargetFor plans a target whose big.Word and int are wordBits wide.
// An unknown word size yields zero limits, which fail closed.
func bigIntTargetFor(goos, goarch string, wordBits uint64) bigIntTarget {
	maxObject, maxAddress, ok := bigIntRuntimeLimits(goos, goarch, wordBits)
	if !ok {
		return bigIntTarget{}
	}
	return bigIntTarget{wordBits: wordBits, maxInt: 1<<(wordBits-1) - 1, maxAddressBytes: maxAddress, maxObjectBytes: maxObject}
}

// bigIntIngressSafeBitLength derives the full-width bit length of a
// normalized Bits view from its length and top word alone. Unlike
// big.Int.BitLen it cannot wrap on 32-bit targets.
func bigIntIngressSafeBitLength(wordCount, top, wordBits uint64) (uint64, bool) {
	topBits := uint64(bits.Len64(top))
	if wordCount == 0 || topBits == 0 || wordBits != 32 && wordBits != 64 || topBits > wordBits {
		return 0, false
	}
	hi, lo := bits.Mul64(wordCount-1, wordBits)
	if hi != 0 {
		return 0, false
	}
	n, carry := bits.Add64(lo, topBits, 0)
	return n, carry == 0
}

// bigIntIngressPreflight checks the quotas for a nonzero n-bit source and
// every planned allocation, counting the live source words, before any
// coefficient word is read.
func bigIntIngressPreflight(n uint64, budget Budget, target bigIntTarget) (bigIntIngressPlan, bool) {
	if n == 0 || target.wordBits != 32 && target.wordBits != 64 || target.maxInt == 0 || target.maxObjectBytes == 0 || target.maxAddressBytes == 0 {
		return bigIntIngressPlan{}, false
	}
	q, r := n/100000, n%100000
	qpart, ok := arithmeticMul(q, 30103)
	if !ok {
		return bigIntIngressPlan{}, false
	}
	u, ok := arithmeticAdd(qpart, r*30103/100000) // r < 100000
	if !ok {
		return bigIntIngressPlan{}, false
	}
	u, ok = arithmeticAdd(u, 1)
	if !ok || !admitted(budget.MaxInputDigits, u, true) || !admitted(budget.MaxDigits, u, true) {
		return bigIntIngressPlan{}, false
	}
	plan := bigIntIngressPlan{u: u, limbs: 1 + (u-1)/9, holderBytes: uint64(reflect.TypeFor[slowCoefficient]().Size())}
	if budget.MaxWork != 0 {
		t, ok := arithmeticMul(plan.limbs, 2)
		if !ok {
			return bigIntIngressPlan{}, false
		}
		square, ok := arithmeticMul(t, t)
		if !ok {
			return bigIntIngressPlan{}, false
		}
		plan.w, ok = arithmeticAdd(square, t)
		if !ok || plan.w > budget.MaxWork {
			return bigIntIngressPlan{}, false
		}
	}
	plan.outputBytes, ok = arithmeticMul(plan.limbs, 4)
	if !ok || plan.limbs > target.maxInt || plan.outputBytes > target.maxInt || plan.holderBytes > target.maxInt {
		return bigIntIngressPlan{}, false
	}
	sourceWords := 1 + (n-1)/target.wordBits
	if sourceWords > target.maxInt {
		return bigIntIngressPlan{}, false
	}
	plan.sourceBytes, ok = arithmeticMul(sourceWords, target.wordBits/8)
	if !ok || plan.sourceBytes > target.maxInt {
		return bigIntIngressPlan{}, false
	}
	if plan.sourceRoundedBytes, ok = bigIntRoundObject(plan.sourceBytes); !ok {
		return bigIntIngressPlan{}, false
	}
	if plan.outputRoundedBytes, ok = bigIntRoundObject(plan.outputBytes); !ok {
		return bigIntIngressPlan{}, false
	}
	plan.holderRoundedBytes, ok = bigIntRoundObject(plan.holderBytes)
	if !ok || plan.outputRoundedBytes > target.maxObjectBytes || plan.holderRoundedBytes > target.maxObjectBytes {
		return bigIntIngressPlan{}, false
	}
	total, ok := arithmeticAdd(plan.sourceRoundedBytes, plan.outputRoundedBytes)
	if !ok {
		return bigIntIngressPlan{}, false
	}
	total, ok = arithmeticAdd(total, plan.holderRoundedBytes)
	if !ok || total > target.maxAddressBytes {
		return bigIntIngressPlan{}, false
	}
	return plan, true
}

// FromBigInt constructs the exact integer value at exponent zero. A nil
// source, or one whose Bits view has a zero highest word after raw mutation,
// returns ErrConversionSyntax; a source beyond the platform's addressable
// allocation returns ErrInsufficientStorage. The result never aliases the
// source, which must not be mutated concurrently.
func FromBigInt(value *big.Int) (Decimal, error) {
	return fromBigInt(value, Budget{}, "FromBigInt")
}

// FromBigIntWithBudget has FromBigInt's semantics and refuses with
// ErrInsufficientStorage, before reading coefficient words or allocating,
// when the conservative digit or work envelope exceeds a positive quota.
func FromBigIntWithBudget(value *big.Int, budget Budget) (Decimal, error) {
	return fromBigInt(value, budget, "FromBigIntWithBudget")
}

// fromBigInt converts on the running target. An unbudgeted source of at
// most 128 bits has nothing to plan. A budgeted one that the general
// conversion's own preflight admits is copied instead of converted through
// limbs.
func fromBigInt(value *big.Int, budget Budget, op string) (Decimal, error) {
	if budget.MaxInputDigits|budget.MaxDigits|budget.MaxWork == 0 {
		if d, ok := fromBigIntInline(value); ok {
			return d, nil
		}
	} else if value != nil && len(value.Bits()) <= 128/bits.UintSize && bigIntInlineAdmitted(value, &budget) {
		if d, ok := fromBigIntInline(value); ok {
			return d, nil
		}
	}
	return fromBigIntOnTarget(value, budget, op, bigIntIngressRuntimeTarget())
}

// bigIntInlineAdmitted reports whether the general conversion admits a
// well-formed source of at most 128 bits of words under budget: a zero
// always, and otherwise by its preflight of the bit length, read from the
// length and top word alone as that conversion reads them. The preflight is
// its only refusal of such a source. It is false for a malformed source.
func bigIntInlineAdmitted(value *big.Int, budget *Budget) bool {
	words := value.Bits()
	if len(words) == 0 {
		return true
	}
	top := words[len(words)-1]
	if top == 0 {
		return false
	}
	n, ok := bigIntIngressSafeBitLength(uint64(len(words)), uint64(top), uint64(bits.UintSize))
	if !ok {
		return false
	}
	_, admitted := bigIntIngressPreflight(n, *budget, bigIntIngressRuntimeTarget())
	return admitted
}

// fromBigIntInline is the conversion of a well-formed magnitude
// below 2^128 on the running target: zero, or at most 128 bits of words
// with a nonzero top word, which are the inline coefficient as they are.
// The preflight admits every such source on every 32- and 64-bit target
// (its three planned objects round to one page each), so only the copy
// remains. ok is false for nil, malformed and longer sources.
func fromBigIntInline(value *big.Int) (Decimal, bool) {
	if value == nil {
		return Decimal{}, false
	}
	words := value.Bits()
	if len(words) > 128/bits.UintSize || len(words) != 0 && words[len(words)-1] == 0 {
		return Decimal{}, false
	}
	var w uint128
	if bits.UintSize == 64 {
		switch len(words) {
		case 2:
			w.hi = uint64(words[1])
			fallthrough
		case 1:
			w.lo = uint64(words[0])
		}
	} else {
		for i, word := range words { // at most four 32-bit words
			if i < 2 {
				w.lo |= uint64(word) << (32 * uint(i))
			} else {
				w.hi |= uint64(word) << (32 * uint(i-2))
			}
		}
	}
	return inlineDecimal(w, 0, value.Sign() < 0), true
}

func fromBigIntOnTarget(value *big.Int, budget Budget, op string, target bigIntTarget) (Decimal, error) {
	if value == nil {
		return Decimal{}, newError(op, ErrConversionSyntax)
	}
	// Bits returns a borrowed slice header. Read only its length and top word
	// before admission; never mutate or retain its backing storage.
	words := value.Bits()
	if len(words) == 0 {
		if !admitted(budget.MaxInputDigits, 1, true) || !admitted(budget.MaxDigits, 1, true) ||
			!admitted(budget.MaxWork, 1, true) {
			return arithmeticFailure(op, ErrInsufficientStorage)
		}
		return Decimal{}, nil
	}
	top := words[len(words)-1]
	if top == 0 {
		return Decimal{}, newError(op, ErrConversionSyntax)
	}
	n, ok := bigIntIngressSafeBitLength(uint64(len(words)), uint64(top), uint64(bits.UintSize))
	if !ok {
		return arithmeticFailure(op, ErrInsufficientStorage)
	}
	plan, ok := bigIntIngressPreflight(n, budget, target)
	if !ok {
		return arithmeticFailure(op, ErrInsufficientStorage)
	}
	if plan.limbs <= conversionScratchLimbs {
		var scratch [conversionScratchLimbs]uint32
		used, ok := bigIntFill(scratch[:plan.limbs], words, n)
		if !ok {
			return arithmeticFailure(op, ErrInsufficientStorage)
		}
		return publishScratch(scratch[:used], 0, value.Sign() < 0), nil
	}
	out := make([]uint32, int(plan.limbs))
	used, ok := bigIntFill(out, words, n)
	if !ok {
		return arithmeticFailure(op, ErrInsufficientStorage)
	}
	return publishOwned(out[:used], 0, value.Sign() < 0), nil
}

// bigIntFill converts the n-bit magnitude in words into base-10^9 limbs in
// out, sized by the proved envelope, and returns the count used; false
// reports an internal invariant breach.
func bigIntFill(out []uint32, words []big.Word, n uint64) (int, bool) {
	used := 0
	chunks := 1 + (n-1)/32
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
			if used == len(out) { // unreachable under the proved U envelope
				return 0, false
			}
			out[used] = uint32(carry % decimalLimbBase)
			carry /= decimalLimbBase
			used++
		}
	}
	if used == 0 || out[used-1] == 0 { // internal invariant
		return 0, false
	}
	return used, true
}

// BigInt sets z to the exact numeric integer and returns z, reusing z's
// words when they have room; a nil z allocates a new *big.Int, as
// big.Float.Int does. A fractional value returns ErrNonIntegral; checked
// growth may return ErrInsufficientStorage before allocating the result. On
// a refusal z is not modified.
func (d Decimal) BigInt(z *big.Int) (*big.Int, error) {
	return d.bigIntWithBudget(z, Budget{}, "BigInt")
}

// BigIntWithBudget has BigInt's exact semantics and applies independent
// input-digit, output-digit and work quotas. Zero means no caller quota.
func (d Decimal) BigIntWithBudget(z *big.Int, budget Budget) (*big.Int, error) {
	return d.bigIntWithBudget(z, budget, "BigIntWithBudget")
}

func bigIntEgressWork(input, output uint64) (uint64, bool) {
	a, b := 1+(input-1)/9, 1+(output-1)/9
	total, ok := arithmeticAdd(a, b)
	if !ok {
		return 0, false
	}
	square, ok := arithmeticMul(total, total)
	if !ok {
		return 0, false
	}
	return arithmeticAdd(square, total)
}

// bigIntEgressWords plans both heap objects before either is allocated. It
// cannot promise that addressable memory is available.
func bigIntEgressWords(digits uint64) (int, bool) {
	count, ok := bigIntEgressWordsForTarget(digits, bigIntIngressRuntimeTarget())
	return int(count), ok // count <= the running target's MaxInt
}

// bigIntEgressWordsForTarget is the physical admission path shared by live
// calls and synthetic boundary probes; it returns the planned word count.
func bigIntEgressWordsForTarget(digits uint64, target bigIntTarget) (uint64, bool) {
	if digits == 0 || target.wordBits != 32 && target.wordBits != 64 || target.maxInt == 0 {
		return 0, false
	}
	q, r := digits/100000, digits%100000
	whole, ok := arithmeticMul(q, 332193)
	if !ok {
		return 0, false
	}
	partial := (r*332193 + 99999) / 100000
	bitBound, ok := arithmeticAdd(whole, partial)
	if !ok || bitBound == 0 {
		return 0, false
	}
	count := 1 + (bitBound-1)/target.wordBits
	wordBytes := target.wordBits / 8 // Go 1.27.1 big.Word is uint.
	bytes, ok := arithmeticMul(count, wordBytes)
	if !ok || count > target.maxInt || bytes > target.maxInt {
		return 0, false
	}
	roundedBytes, ok := bigIntRoundObject(bytes)
	if !ok {
		return 0, false
	}
	roundedObject, ok := bigIntRoundObject(bigIntObjectBytes)
	if !ok {
		return 0, false
	}
	total, ok := arithmeticAdd(roundedBytes, roundedObject)
	if !ok || roundedBytes > target.maxObjectBytes || roundedObject > target.maxObjectBytes || total > target.maxAddressBytes {
		return 0, false
	}
	return count, true
}

// bigIntEgressAdmitted reports whether budget admits the general BigInt
// conversion of an integral value with a digits-digit coefficient and a
// resultDigits-digit integer: its input-digit, result-digit and work caps,
// which read nothing else.
func bigIntEgressAdmitted(digits, resultDigits uint64, budget *Budget) bool {
	if budget.MaxInputDigits != 0 && digits > budget.MaxInputDigits || budget.MaxDigits != 0 && resultDigits > budget.MaxDigits {
		return false
	}
	if budget.MaxWork == 0 {
		return true
	}
	work, ok := bigIntEgressWork(digits, resultDigits)
	return ok && work <= budget.MaxWork
}

// bigIntInlineAdmitted reports whether budget admits the general BigInt
// conversion of a nonzero inline coefficient, when the value is integral:
// by the bound of every conversion bigIntInline serves, or else by the
// digit counts the general path caps, the coefficient's and the integer's,
// which a nonnegative exponent raises and a negative one lowers. A value
// with no integer digit is not admitted; the general path refuses it.
//
//go:noinline
func (d Decimal) bigIntInlineAdmitted(budget Budget) bool {
	if budget.admitsConversion(inlineResultDigits, inlineBigIntWork) {
		return true
	}
	digits := inlineDigits(d.words)
	resultDigits := digits
	if e := int64(d.exponent()); e >= 0 {
		resultDigits += uint64(e)
	} else if drop := uint64(-e); drop < digits {
		resultDigits -= drop
	} else {
		return false
	}
	return bigIntEgressAdmitted(digits, resultDigits, &budget)
}

// bigIntInline is the BigInt of a nonzero inline coefficient whose integer
// stays below 2^128: the scaled or exactly divided words are stored
// directly. ok is false, with z untouched, for every refusal and every
// other shape; the general path owns those. It charges nothing: the caller
// admits a budget.
func (d Decimal) bigIntInline(z *big.Int) (*big.Int, bool) {
	w := d.words
	if e := d.exponent(); e > 0 {
		var ok bool
		if w, ok = inlineScale(w, uint64(e)); !ok {
			return nil, false
		}
	} else if e < 0 {
		if e < -19 {
			return nil, false
		}
		divisor := pow10Words[-e]
		var r uint64
		if w.hi == 0 {
			w.lo, r = w.lo/divisor, w.lo%divisor
		} else {
			w.hi, r = bits.Div64(0, w.hi, divisor)
			w.lo, r = bits.Div64(r, w.lo, divisor)
		}
		if r != 0 || w.lo|w.hi == 0 {
			return nil, false // fractional: the general path refuses
		}
	}
	// The general path's word count, so both paths size z alike.
	wordCount, ok := bigIntEgressWords(inlineDigits(w))
	needed := (bits.Len64(w.lo) + bits.UintSize - 1) / bits.UintSize
	if w.hi != 0 {
		needed = 64/bits.UintSize + (bits.Len64(w.hi)+bits.UintSize-1)/bits.UintSize
	}
	if !ok || wordCount < needed {
		return nil, false
	}
	var words []big.Word
	if z != nil {
		if b := z.Bits(); cap(b) >= wordCount {
			words = b[:wordCount]
			clear(words)
		}
	}
	if words == nil {
		words = make([]big.Word, wordCount)
	}
	if bits.UintSize == 64 {
		words[0] = big.Word(w.lo)
		if w.hi != 0 {
			words[1] = big.Word(w.hi)
		}
	} else {
		for i := range needed {
			if i < 2 {
				words[i] = big.Word(uint32(w.lo >> (32 * uint(i))))
			} else {
				words[i] = big.Word(uint32(w.hi >> (32 * uint(i-2))))
			}
		}
	}
	if z == nil {
		z = new(big.Int)
	}
	z.SetBits(words[:needed])
	if d.negative() {
		z.Neg(z)
	}
	return z, true
}

func (d Decimal) bigIntWithBudget(z *big.Int, budget Budget, op string) (*big.Int, error) {
	if d.isZero() {
		if z == nil {
			return new(big.Int), nil
		}
		return z.SetInt64(0), nil
	}
	if d.slow == nil && (budget.MaxInputDigits|budget.MaxDigits|budget.MaxWork == 0 || d.bigIntInlineAdmitted(budget)) {
		if out, ok := d.bigIntInline(z); ok {
			return out, nil
		}
	}
	return d.bigIntGeneral(z, budget, op)
}

// bigIntGeneral is the general BigInt conversion of a nonzero value: it
// owns every budget charge and refusal.
func (d Decimal) bigIntGeneral(z *big.Int, budget Budget, op string) (*big.Int, error) {
	refuse := func(code ErrorCode) (*big.Int, error) {
		return nil, newError(op, code)
	}
	v := coefficientViewOf(d)
	digits, ok := arithmeticDigits(&v)
	if !ok || budget.MaxInputDigits != 0 && digits > budget.MaxInputDigits {
		return refuse(ErrInsufficientStorage)
	}
	var drop, extra, resultDigits uint64
	if d.exponent() < 0 {
		drop = uint64(-int64(d.exponent()))
		if drop >= digits {
			return refuse(ErrNonIntegral)
		}
		resultDigits = digits - drop
		if budget.MaxWork != 0 {
			work, valid := bigIntEgressWork(digits, resultDigits)
			if !valid || work > budget.MaxWork {
				return refuse(ErrInsufficientStorage)
			}
		}
		if !integerLowDigitsZero(&v, drop) {
			return refuse(ErrNonIntegral)
		}
	} else {
		extra = uint64(d.exponent())
		resultDigits, ok = arithmeticAdd(digits, extra)
		if !ok {
			return refuse(ErrInsufficientStorage)
		}
	}
	if budget.MaxDigits != 0 && resultDigits > budget.MaxDigits {
		return refuse(ErrInsufficientStorage)
	}
	if d.exponent() >= 0 && budget.MaxWork != 0 {
		work, valid := bigIntEgressWork(digits, resultDigits)
		if !valid || work > budget.MaxWork {
			return refuse(ErrInsufficientStorage)
		}
	}
	wordCount, ok := bigIntEgressWords(resultDigits)
	if !ok {
		return refuse(ErrInsufficientStorage)
	}
	// Reuse z's words when they fit: every refusal below is an internal
	// invariant (the envelope bounds the words and the low digits were
	// checked zero), so admitted calls do not leave z modified on failure.
	var words []big.Word
	if z != nil {
		if b := z.Bits(); cap(b) >= wordCount {
			words = b[:wordCount]
			clear(words)
		}
	}
	if words == nil {
		words = make([]big.Word, wordCount)
	}
	used := 0
	appendGroup := func(factor, digit uint32) bool {
		carry := uint(digit)
		for i := range used {
			hi, lo := bits.Mul(uint(words[i]), uint(factor))
			sum, overflow := bits.Add(lo, carry, 0)
			words[i] = big.Word(sum)
			carry = hi + overflow
		}
		if carry != 0 {
			if used == len(words) {
				return false
			}
			words[used] = big.Word(carry)
			used++
		}
		return true
	}
	if drop == 0 {
		for i := v.count - 1; i >= 0; i-- {
			if !appendGroup(uint32(decimalLimbBase), v.limb(i)) {
				return refuse(ErrInsufficientStorage)
			}
		}
		for range extra / 9 {
			if !appendGroup(uint32(decimalLimbBase), 0) {
				return refuse(ErrInsufficientStorage)
			}
		}
		if rem := extra % 9; rem != 0 && !appendGroup(decimalPowers[rem], 0) {
			return refuse(ErrInsufficientStorage)
		}
	} else {
		whole, rem := drop/9, drop%9
		divisor := uint64(1)
		if rem != 0 {
			divisor = uint64(decimalPowers[rem])
		}
		var remainder uint64
		for i := v.count - 1; i >= int(whole); i-- {
			value := remainder*decimalLimbBase + uint64(v.limb(i))
			quotient := value / divisor
			remainder = value % divisor
			if !appendGroup(uint32(decimalLimbBase), uint32(quotient)) {
				return refuse(ErrInsufficientStorage)
			}
		}
		if remainder != 0 {
			return refuse(ErrNonIntegral)
		}
	}
	if z == nil {
		z = new(big.Int)
	}
	z.SetBits(words[:used])
	if d.negative() {
		z.Neg(z)
	}
	return z, nil
}
