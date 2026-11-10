// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"encoding/binary"
	"math"
	"math/bits"
	"runtime"
	"slices"
)

// Exact coefficient interchange: every form exchanges the constructed cohort,
// the coefficient integer and the exponent, never normalizes it and reports
// "does not fit" instead of truncating.

// NewInt128 constructs coefficient·10^exponent from a signed 128-bit
// two's-complement coefficient split into its high and low 64-bit words,
// the layout of a 128-bit integer column. It never allocates.
func NewInt128(hi int64, lo uint64, exponent int32) Decimal {
	high := uint64(hi)
	negative := hi < 0
	if negative {
		var borrow uint64
		lo, borrow = bits.Sub64(0, lo, 0)
		high, _ = bits.Sub64(0, high, borrow)
	}
	if high == 0 && lo == 0 {
		return zeroDecimal(exponent)
	}
	return inlineDecimal(uint128{lo, high}, exponent, negative)
}

// CoefficientInt128 returns the coefficient as signed 128-bit
// two's-complement words. ok is false, with zero words, exactly when the
// coefficient lies outside [−2^127, 2^127−1]. The exponent is reported
// separately by Exponent. It never allocates.
func (d Decimal) CoefficientInt128() (hi int64, lo uint64, ok bool) {
	if d.slow != nil {
		// Published slow coefficients are at least 2^128 (the canonical
		// band); the limbs decide rather than the band.
		inline, fits := publishInline(d.slow.limbs, d.exponent(), d.negative())
		if !fits {
			return 0, 0, false
		}
		d = inline
	}
	low, high := d.words.lo, d.words.hi
	const top = uint64(1) << 63
	if d.negative() {
		if high > top || high == top && low != 0 {
			return 0, 0, false
		}
		var borrow uint64
		low, borrow = bits.Sub64(0, low, 0)
		high, _ = bits.Sub64(0, high, borrow)
		return int64(high), low, true
	}
	if high >= top {
		return 0, 0, false
	}
	return int64(high), low, true
}

// SQLDecimal binds a Decimal through the database/sql decimal decompose
// convention, for drivers that recognize it (for example drivers that type
// parameters by value). The default parameter converter hands a type with
// Decompose to the driver instead of calling Value, so drivers without
// decompose support reject SQLDecimal; pass the Decimal itself to those
// drivers, which receive canonical text through Value. A NamedValueChecker
// sees SQLDecimal before the default converter. Bind SQL NULL as nil, never
// as a nil *SQLDecimal: database/sql calls Decompose on any decompose
// value it is given.
type SQLDecimal struct{ Decimal Decimal }

// Decompose returns form 0 (finite), the sign, the minimal big-endian
// coefficient magnitude (empty for zero) and the exponent. The magnitude
// is written into buf[:0] when its capacity suffices.
func (v SQLDecimal) Decompose(buf []byte) (form byte, negative bool, coefficient []byte, exponent int32) {
	d := v.Decimal
	coefficient = appendMagnitude(buf[:0], d)
	return 0, d.negative() && len(coefficient) > 0, coefficient, d.exponent()
}

// Compose sets the receiver from the database/sql decompose convention:
// form 0 with a big-endian magnitude and the exponent. The non-finite forms
// 1 and 2 and unknown forms return ErrConversionSyntax, as non-finite text
// does. The receiver changes only on success and never aliases coefficient.
func (d *Decimal) Compose(form byte, negative bool, coefficient []byte, exponent int32) error {
	// At most 16 bytes fit the inline coefficient and every target's address
	// window, so there is nothing to plan. A nil receiver or another form
	// takes the general path for its error.
	if d != nil && form == 0 {
		if len(coefficient) == 0 {
			*d = zeroDecimal(exponent)
			return nil
		}
		if len(coefficient) <= 16 {
			*d = inlineDecimal(bigEndian128(coefficient), exponent, negative)
			return nil
		}
	}
	return d.compose(form, negative, coefficient, exponent, Budget{}, "Compose")
}

// ComposeWithBudget is Compose with the copied digit and work quotas of a
// Budget, applied to the conservative envelope of the raw coefficient
// length.
func (d *Decimal) ComposeWithBudget(form byte, negative bool, coefficient []byte, exponent int32, budget Budget) error {
	// As Compose: 1 to 16 bytes are the inline coefficient as they are,
	// under a budget that admits their envelope.
	if n := len(coefficient); d != nil && form == 0 && n >= 1 && n <= 16 && binaryInlineAdmitted(n, budget) {
		*d = inlineDecimal(bigEndian128(coefficient), exponent, negative)
		return nil
	}
	return d.compose(form, negative, coefficient, exponent, budget, "ComposeWithBudget")
}

func (d *Decimal) compose(form byte, negative bool, coefficient []byte, exponent int32, budget Budget, op string) error {
	if d == nil {
		return newError(op, ErrInvalidOperation)
	}
	if form != 0 {
		return newError(op, ErrConversionSyntax)
	}
	if len(coefficient) == 0 {
		*d = zeroDecimal(exponent)
		return nil
	}
	result, err := fromBinary(coefficient, false, false, negative, exponent, budget, op)
	if err != nil {
		return err
	}
	*d = result
	return nil
}

// NewTwosComplement constructs coefficient·10^exponent from a
// two's-complement coefficient of any width with sign extension, in the
// given byte order (binary.BigEndian as in Parquet, binary.LittleEndian as
// in Arrow and storage lanes, or binary.NativeEndian). Empty input returns
// ErrConversionSyntax; any other ByteOrder returns ErrInvalidOperation; an
// input beyond the addressable window returns ErrInsufficientStorage. The
// input is neither mutated nor retained.
func NewTwosComplement(b []byte, order binary.ByteOrder, exponent int32) (Decimal, error) {
	return newTwosComplement(b, order, exponent, Budget{}, "NewTwosComplement")
}

// NewTwosComplementWithBudget is NewTwosComplement with the copied quotas
// of a Budget, checked against the conservative envelope
// of the raw input length before any conversion.
func NewTwosComplementWithBudget(b []byte, order binary.ByteOrder, exponent int32, budget Budget) (Decimal, error) {
	return newTwosComplement(b, order, exponent, budget, "NewTwosComplementWithBudget")
}

func newTwosComplement(b []byte, order binary.ByteOrder, exponent int32, budget Budget, op string) (Decimal, error) {
	little, ok := byteOrderLittle(order)
	if !ok {
		return Decimal{}, newError(op, ErrInvalidOperation)
	}
	if len(b) == 0 {
		return Decimal{}, newError(op, ErrConversionSyntax)
	}
	return fromBinary(b, little, true, false, exponent, budget, op)
}

// byteOrderLittle recognizes the standard byte orders by identity and
// never calls a caller-defined ByteOrder.
func byteOrderLittle(order binary.ByteOrder) (little, ok bool) {
	switch order {
	case binary.ByteOrder(binary.BigEndian):
		return false, true
	case binary.ByteOrder(binary.LittleEndian):
		return true, true
	case binary.ByteOrder(binary.NativeEndian):
		var probe [2]byte
		binary.NativeEndian.PutUint16(probe[:], 1)
		return probe[0] == 1, true
	}
	return false, false
}

// binaryReader reads a coefficient's bytes from most to least significant.
type binaryReader struct {
	b      []byte
	little bool
}

func (r binaryReader) at(i int) byte {
	if r.little {
		return r.b[len(r.b)-1-i]
	}
	return r.b[i]
}

// fromBinary converts a two's-complement (signed) or unsigned magnitude
// coefficient. Admission uses the raw length; sizing uses the length after
// sign-padding bytes are skipped.
func fromBinary(b []byte, little, signed, negativeFlag bool, exponent int32, budget Budget, op string) (Decimal, error) {
	// At most 16 bytes fit the inline coefficient and every target's address
	// window: an unbudgeted conversion has nothing to plan or strip, and a
	// budgeted one only the envelope of its raw length to admit, as the
	// general conversion admits it before it strips the sign padding.
	if len(b) <= 16 && (budget.MaxInputDigits|budget.MaxDigits|budget.MaxWork == 0 || binaryInlineAdmitted(len(b), budget)) {
		return inlineBinary(b, little, signed, negativeFlag, exponent), nil
	}
	return fromBinaryGeneral(b, little, signed, negativeFlag, exponent, budget, op)
}

// binaryInlineAdmitted reports whether budget admits the general
// conversion of n ≤ 16 raw bytes: by the envelope of 16 bytes, which bounds
// every such length's, or else by the envelope of n bytes, its digit bound
// against both digit caps and its work bound.
//
//go:noinline
func binaryInlineAdmitted(n int, budget Budget) bool {
	if budget.admitsConversion(inlineBinaryDigits, inlineBinaryWork) {
		return true
	}
	u, w, ok := binaryEnvelope(uint64(n) * 8)
	return ok && admitted(budget.MaxInputDigits, u, true) && admitted(budget.MaxDigits, u, true) && admitted(budget.MaxWork, w, true)
}

// fromBinaryGeneral is the general conversion: it owns every refusal and
// every length.
func fromBinaryGeneral(b []byte, little, signed, negativeFlag bool, exponent int32, budget Budget, op string) (Decimal, error) {
	r := binaryReader{b: b, little: little}
	negative := negativeFlag
	pad := byte(0)
	if signed {
		negative = r.at(0)&0x80 != 0
		if negative {
			pad = 0xff
		}
	}
	rawBits, ok := arithmeticMul(uint64(len(b)), 8)
	if !ok {
		return Decimal{}, newError(op, ErrInsufficientStorage)
	}
	u, w, ok := binaryEnvelope(rawBits)
	if !ok || !admitted(budget.MaxInputDigits, u, true) || !admitted(budget.MaxDigits, u, true) ||
		!admitted(budget.MaxWork, w, true) || !binaryAdmitted(uint64(len(b)), u) {
		return Decimal{}, newError(op, ErrInsufficientStorage)
	}
	start := 0
	for start < len(b) && r.at(start) == pad {
		start++
	}
	if signed && negative && (start == len(b) || r.at(start)&0x80 == 0) {
		start-- // keep one sign byte so the remaining bytes stay negative
	}
	if start == len(b) {
		return zeroDecimal(exponent), nil
	}
	if len(b)-start <= 16 {
		rest := b[start:]
		if little {
			rest = b[:len(b)-start]
		}
		return inlineBinary(rest, little, signed && negative, negative, exponent), nil
	}
	return binaryHorner(r, start, signed && negative, negative, exponent), nil
}

// inlineBinary converts 1 to 16 bytes: two's complement when signed,
// otherwise a magnitude with the given sign.
func inlineBinary(b []byte, little, signed, negative bool, exponent int32) Decimal {
	var words uint128
	if little {
		words = littleEndian128(b)
	} else {
		words = bigEndian128(b)
	}
	if signed {
		top := b[0]
		if little {
			top = b[len(b)-1]
		}
		if negative = top&0x80 != 0; negative {
			// Sign-extend from the input width, then negate to the magnitude.
			if used := uint(len(b)) * 8; used < 64 {
				words.lo |= ^uint64(0) << used
				words.hi = ^uint64(0)
			} else {
				words.hi |= ^uint64(0) << (used - 64)
			}
			var borrow uint64
			words.lo, borrow = bits.Sub64(0, words.lo, 0)
			words.hi, _ = bits.Sub64(0, words.hi, borrow)
		}
	}
	return inlineDecimal(words, exponent, negative)
}

// bigEndian128 returns the unsigned value of at most 16 big-endian bytes.
func bigEndian128(b []byte) uint128 {
	if n := len(b); n >= 8 {
		return uint128{binary.BigEndian.Uint64(b[n-8:]), binary.BigEndian.Uint64(b) >> (uint(16-n) * 8)}
	}
	var lo uint64
	for _, v := range b {
		lo = lo<<8 | uint64(v)
	}
	return uint128{lo, 0}
}

// littleEndian128 returns the unsigned value of at most 16 little-endian bytes.
func littleEndian128(b []byte) uint128 {
	if n := len(b); n >= 8 {
		return uint128{binary.LittleEndian.Uint64(b), binary.LittleEndian.Uint64(b[n-8:]) >> (uint(16-n) * 8)}
	}
	var lo uint64
	for _, v := range slices.Backward(b) {
		lo = lo<<8 | uint64(v)
	}
	return uint128{lo, 0}
}

// binaryHorner is the general conversion: Horner over bytes from index
// start into base-10^9 limbs. With invert, a negative two's-complement
// input converts as ~x + 1 without mutating the caller's bytes. A result
// whose envelope fits conversionScratchLimbs is built on the stack and
// published with one allocation.
func binaryHorner(r binaryReader, start int, invert, negative bool, exponent int32) Decimal {
	strippedBits := uint64(len(r.b)-start) * 8
	digits, _, _ := binaryEnvelope(strippedBits)
	count := 1 + (digits-1)/9 + 1
	if count <= conversionScratchLimbs {
		var scratch [conversionScratchLimbs]uint32
		used := hornerFill(scratch[:count], r, start, invert)
		return publishScratch(scratch[:used], exponent, negative)
	}
	out := make([]uint32, count)
	used := hornerFill(out, r, start, invert)
	return publishOwned(out[:used], exponent, negative)
}

// hornerFill writes binaryHorner's limbs into out, sized by the envelope,
// and returns the count used.
func hornerFill(out []uint32, r binaryReader, start int, invert bool) int {
	used := 0
	feed := func(v uint64, factor uint64) {
		carry := v
		for i := range used {
			t := uint64(out[i])*factor + carry
			out[i] = uint32(t % decimalLimbBase)
			carry = t / decimalLimbBase
		}
		for carry != 0 {
			out[used] = uint32(carry % decimalLimbBase)
			carry /= decimalLimbBase
			used++
		}
	}
	// The leading bytes that do not fill a group of four go one at a
	// time; the rest go four per pass over the limbs.
	i := start
	for lead := (len(r.b) - start) % 4; lead > 0; lead-- {
		v := r.at(i)
		if invert {
			v = ^v
		}
		feed(uint64(v), 1<<8)
		i++
	}
	for ; i < len(r.b); i += 4 {
		v := uint32(r.at(i))<<24 | uint32(r.at(i+1))<<16 | uint32(r.at(i+2))<<8 | uint32(r.at(i+3))
		if invert {
			v = ^v
		}
		feed(uint64(v), 1<<32)
	}
	if invert {
		carry := uint64(1)
		for i := 0; carry != 0; i++ {
			if i == used {
				out[used] = 0
				used++
			}
			t := uint64(out[i]) + carry
			out[i] = uint32(t % decimalLimbBase)
			carry = t / decimalLimbBase
		}
	}
	return used
}

// binaryEnvelope is the FromBigInt envelope for an n-bit magnitude:
// U = floor(n·30103/100000)+1 digits and W = (2⌈U/9⌉)^2 + 2⌈U/9⌉ work.
func binaryEnvelope(n uint64) (u, w uint64, ok bool) {
	q, rem := n/100000, n%100000
	u, ok = arithmeticMul(q, 30103)
	if !ok {
		return 0, 0, false
	}
	if u, ok = arithmeticAdd(u, rem*30103/100000+1); !ok {
		return 0, 0, false
	}
	t, ok := arithmeticMul(1+(u-1)/9, 2)
	if !ok {
		return 0, 0, false
	}
	square, ok := arithmeticMul(t, t)
	if !ok {
		return 0, 0, false
	}
	w, ok = arithmeticAdd(square, t)
	return u, w, ok
}

// binaryAdmitted checks the combined live bytes of the caller's source and
// the planned coefficient against the target's address window.
func binaryAdmitted(sourceBytes, digits uint64) bool {
	maxObject, maxAddress, ok := bigIntRuntimeLimits(runtime.GOOS, runtime.GOARCH, uint64(bits.UintSize))
	if !ok {
		return false
	}
	limbs := 1 + (digits-1)/9
	if limbs > uint64(math.MaxInt)/4 {
		return false
	}
	result, ok := bigIntRoundObject(limbs*4 + 64)
	if !ok || result > maxObject {
		return false
	}
	source, ok := bigIntRoundObject(sourceBytes)
	if !ok {
		return false
	}
	total, ok := arithmeticAdd(result, source)
	return ok && total <= maxAddress
}

// AppendTwosComplement appends the coefficient (not the value; the exponent
// is separate) as exactly width sign-extended two's-complement bytes in the
// given byte order. width < 1 or an unknown order returns
// ErrInvalidOperation; a width beyond the addressable window returns
// ErrInsufficientStorage; a coefficient outside [−2^(8w−1), 2^(8w−1)−1]
// returns ErrIntegerRange. dst is returned unchanged on every error.
func (d Decimal) AppendTwosComplement(dst []byte, width int, order binary.ByteOrder) ([]byte, error) {
	const op = "AppendTwosComplement"
	little, ok := byteOrderLittle(order)
	if !ok || width < 1 {
		return dst, newError(op, ErrInvalidOperation)
	}
	maxObject, _, known := bigIntRuntimeLimits(runtime.GOOS, runtime.GOARCH, uint64(bits.UintSize))
	if !known || width > math.MaxInt-len(dst) || uint64(width) > math.MaxUint64/8 || uint64(len(dst)+width) > maxObject {
		return dst, newError(op, ErrInsufficientStorage)
	}
	if d.slow == nil {
		return d.appendInlineTwosComplement(dst, width, little)
	}
	// Digit pre-check: more digits than 2^(8w-1) has cannot fit.
	v := coefficientViewOf(d)
	digits, _ := arithmeticDigits(&v)
	if bound, ok := twosComplementDigitBound(width); ok && v.count > 0 && digits > bound {
		return dst, newError(op, ErrIntegerRange)
	}
	// Magnitude as little-endian bytes in scratch; dst is untouched until the
	// value is known to fit.
	var stack [40]byte
	mag := limbsToBytes(stack[:0], &v)
	for len(mag) > 0 && mag[len(mag)-1] == 0 {
		mag = mag[:len(mag)-1]
	}
	if !twosComplementFits(mag, width, d.negative()) {
		return dst, newError(op, ErrIntegerRange)
	}
	start := len(dst)
	dst = slices.Grow(dst, width)[:start+width]
	out := dst[start:]
	carry := uint16(1)
	for i := range width {
		var m byte
		if i < len(mag) {
			m = mag[i]
		}
		if d.negative() {
			s := uint16(^m) + carry
			m, carry = byte(s), s>>8
		}
		if little {
			out[i] = m
		} else {
			out[width-1-i] = m
		}
	}
	return dst, nil
}

// appendInlineTwosComplement is AppendTwosComplement for an inline
// coefficient after the order, width and storage checks: the 128-bit
// magnitude is range-checked against 2^(8w−1), negated in two words and
// stored with two word writes, sign-extended beyond 16 bytes.
func (d Decimal) appendInlineTwosComplement(dst []byte, width int, little bool) ([]byte, error) {
	lo, hi := d.words.lo, d.words.hi
	negative := d.negative()
	if width <= 16 {
		// limit = 2^(8w−1): a positive magnitude must be below it, a
		// negative one at most equal to it.
		var limitLo, limitHi uint64
		if n := uint(8*width - 1); n >= 64 {
			limitHi = 1 << (n - 64)
		} else {
			limitLo = 1 << n
		}
		if hi > limitHi || hi == limitHi && (lo > limitLo || lo == limitLo && !negative) {
			return dst, newError("AppendTwosComplement", ErrIntegerRange)
		}
	}
	fill := byte(0)
	if negative {
		var borrow uint64
		lo, borrow = bits.Sub64(0, lo, 0)
		hi, _ = bits.Sub64(0, hi, borrow)
		fill = 0xff
	}
	start := len(dst)
	dst = slices.Grow(dst, width)[:start+width]
	out := dst[start:]
	if little {
		if width == 16 {
			binary.LittleEndian.PutUint64(out, lo)
			binary.LittleEndian.PutUint64(out[8:], hi)
			return dst, nil
		}
		var le [16]byte
		binary.LittleEndian.PutUint64(le[:8], lo)
		binary.LittleEndian.PutUint64(le[8:], hi)
		n := copy(out, le[:])
		for i := n; i < width; i++ {
			out[i] = fill
		}
		return dst, nil
	}
	if width == 16 {
		binary.BigEndian.PutUint64(out, hi)
		binary.BigEndian.PutUint64(out[8:], lo)
		return dst, nil
	}
	var be [16]byte
	binary.BigEndian.PutUint64(be[:8], hi)
	binary.BigEndian.PutUint64(be[8:], lo)
	n := min(width, 16)
	copy(out[width-n:], be[16-n:])
	for i := range width - n {
		out[i] = fill
	}
	return dst, nil
}

// twosComplementDigitBound is a digit count no fitting coefficient exceeds
// at the given width (2^(8w−1) has at most this many digits). ok is false
// when the bound overflows; the exact check then decides alone.
func twosComplementDigitBound(width int) (uint64, bool) {
	bitCount, ok := arithmeticMul(uint64(width), 8)
	if !ok {
		return 0, false
	}
	scaled, ok := arithmeticMul(bitCount-1, 30103)
	if !ok {
		return 0, false
	}
	return scaled/100000 + 2, true
}

// twosComplementFits reports whether a little-endian magnitude with the given
// sign fits width two's-complement bytes: at most 2^(8w−1)−1 when positive,
// at most 2^(8w−1) when negative.
func twosComplementFits(mag []byte, width int, negative bool) bool {
	if len(mag) < width {
		return true
	}
	if len(mag) > width {
		return false
	}
	top := mag[width-1]
	if top < 0x80 {
		return true
	}
	if !negative || top != 0x80 {
		return false
	}
	for _, b := range mag[:width-1] {
		if b != 0 {
			return false
		}
	}
	return true
}

// limbsToBytes appends the minimal little-endian binary magnitude of
// base-10^9 limbs: Horner accumulation in 64-bit words, two limbs per pass.
// The value is below 2^(30·count), so ⌈30·count/64⌉ words hold it; they are
// on the stack for up to 68 limbs.
func limbsToBytes(dst []byte, v *coefficientView) []byte {
	var stack [32]uint64
	words := stack[:]
	if n := limbWords(v.count); n > len(stack) {
		words = make([]uint64, n)
	}
	used := 0
	i := v.count - 1
	if v.count%2 == 1 {
		words[0], used = uint64(v.limb(i)), 1
		i--
	}
	for ; i >= 1; i -= 2 {
		carry := uint64(v.limb(i))*decimalLimbBase + uint64(v.limb(i-1))
		for j := range used {
			hi, lo := bits.Mul64(words[j], decimalLimbBase*decimalLimbBase)
			var c uint64
			words[j], c = bits.Add64(lo, carry, 0)
			carry = hi + c
		}
		if carry != 0 {
			words[used] = carry
			used++
		}
	}
	for _, w := range words[:used] {
		dst = binary.LittleEndian.AppendUint64(dst, w)
	}
	for len(dst) > 0 && dst[len(dst)-1] == 0 {
		dst = dst[:len(dst)-1]
	}
	return dst
}

// limbWords is ⌈30·count/64⌉, the 64-bit words that hold count base-10^9
// limbs, computed without the product 30·count, which leaves a 32-bit int
// from 71,582,789 limbs.
func limbWords(count int) int {
	return count/32*15 + (count%32*30+63)/64
}

// appendMagnitude appends the minimal big-endian magnitude of d's
// coefficient. When dst lacks room it allocates once, with exactly the
// needed length and capacity.
func appendMagnitude(dst []byte, d Decimal) []byte {
	if d.slow != nil {
		v := coefficientViewOf(d)
		// Every limb is below 2^30, so the magnitude fits ⌈30·count/64⌉
		// words: limbsToBytes never grows this scratch.
		bound := limbWords(v.count) * 8
		var scratch [64]byte
		little := scratch[:0]
		if bound > len(scratch) {
			little = make([]byte, 0, bound)
		}
		little = limbsToBytes(little, &v)
		out, tail := growExact(dst, len(little))
		for i, b := range little {
			tail[len(tail)-1-i] = b
		}
		return out
	}
	hi, lo := d.words.hi, d.words.lo
	n := (bits.Len64(lo) + 7) / 8
	if hi != 0 {
		n = 8 + (bits.Len64(hi)+7)/8
	}
	var be [16]byte
	binary.BigEndian.PutUint64(be[:8], hi)
	binary.BigEndian.PutUint64(be[8:], lo)
	out, tail := growExact(dst, n)
	copy(tail, be[16-n:])
	return out
}

// growExact extends dst by n bytes, returning the extended slice and its
// last n bytes. It reslices dst when the capacity suffices and otherwise
// allocates exactly len(dst)+n bytes once.
func growExact(dst []byte, n int) (out, tail []byte) {
	length := len(dst)
	if cap(dst)-length >= n {
		out = dst[:length+n]
	} else {
		out = make([]byte, length+n)
		copy(out, dst)
	}
	return out, out[length:]
}
