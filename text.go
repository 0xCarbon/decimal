// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"encoding/binary"
	"math"
	"math/bits"
	"slices"
	"strings"
)

// checkedDigitCount refuses a coefficient whose digits cannot fit a Go
// string, before any size calculation casts the length to int64.
func checkedDigitCount(limbCount int, top uint32) (uint64, bool) {
	if limbCount < 1 {
		return 0, false
	}
	topDigits := uint64(limbDigits(top))
	if uint64(limbCount-1) > (uint64(math.MaxInt)-topDigits)/9 {
		return 0, false
	}
	return uint64(limbCount-1)*9 + topDigits, true
}

// Text returns the canonical text for d. A zero maxBytes imposes no caller
// quota; a positive value limits the exact output byte count.
func (d Decimal) Text(maxBytes uint64) (string, error) {
	return d.text(maxBytes, math.MaxInt)
}

// text renders canonical text, refusing a slow coefficient whose exact
// output size exceeds addressLimit. Text passes math.MaxInt, Go's string
// addressability bound; tests pass a smaller limit to reach the checked
// refusal without allocating an unaddressable coefficient. Inline text is
// at most inlineTextMax bytes, far below any real address limit.
func (d Decimal) text(maxBytes, addressLimit uint64) (string, error) {
	if d.slow == nil {
		if e := int64(d.exponent()); d.words.hi == 0 && e <= 0 && -e <= int64(wordDigits(d.words.lo))+5 {
			// One-word plain text is emitted right-aligned in a stack
			// buffer without a size plan: at most a sign, 20
			// digits, a point and 5 leading fraction zeros. The refusal
			// still precedes the one allocation.
			var b [inlineTextMax]byte
			i := emitInlinePlain(b[:], d.words.lo, int(-e), d.negative())
			if maxBytes != 0 && uint64(len(b)-i) > maxBytes {
				return "", newError("Text", ErrInsufficientStorage)
			}
			return string(b[i:]), nil
		}
		// Inline: size exactly, emit once into the stack buffer and convert
		// once.
		var buf [inlineTextMax]byte
		if d.words.hi == 0 {
			n := wordDigits(d.words.lo)
			size := d.inlineTextSize(n)
			if maxBytes != 0 && uint64(size) > maxBytes {
				return "", newError("Text", ErrInsufficientStorage)
			}
			d.emitWordText(buf[:size], n)
			return string(buf[:size]), nil
		}
		c := splitWide(d.words)
		size := d.inlineTextSize(c.n)
		if maxBytes != 0 && uint64(size) > maxBytes {
			return "", newError("Text", ErrInsufficientStorage)
		}
		d.emitWideText(buf[:size], c)
		return string(buf[:size]), nil
	}
	layout, err := d.slowTextLayout(maxBytes, addressLimit)
	if err != nil {
		return "", err
	}
	// The builder holds the one allocation; the digits are staged through
	// a stack chunk.
	var b strings.Builder
	b.Grow(int(layout.size))
	var chunk [512]byte
	i := layout.emit(chunk[:], &b)
	b.Write(chunk[:i])
	return b.String(), nil
}

// slowText is the exact layout of a slow coefficient's canonical text: an
// optional sign, "0." and zeros leading zeros when zeros >= 0, the
// coefficient digits with a point after splitAt of them (none when splitAt
// is zero), and in scientific form E, the exponent sign and expMagnitude.
type slowText struct {
	v            coefficientView
	size         uint64
	splitAt      uint64
	expMagnitude uint64
	zeros        int
	negative     bool
	scientific   bool
	expNegative  bool
}

// slowTextLayout sizes the canonical text of a slow coefficient, refusing
// with Text's storage error when the exact size exceeds a positive maxBytes
// or addressLimit, before any allocation or signed size arithmetic.
func (d Decimal) slowTextLayout(maxBytes, addressLimit uint64) (slowText, error) {
	// Text and numeric equality share one read-only view of either storage
	// band. Zero has a single emitted coefficient digit even though it stores
	// no magnitude limbs.
	t := slowText{v: coefficientViewOf(d), zeros: -1, negative: d.negative()}
	if t.v.count == 0 {
		t.v.inline[0] = 0
		t.v.count = 1
	}
	// Refuse an unaddressable coefficient before allocating a text buffer
	// or converting its digit count to signed arithmetic.
	n, ok := checkedDigitCount(t.v.count, t.v.limb(t.v.count-1))
	if !ok {
		return t, newError("Text", ErrInsufficientStorage)
	}
	if d.exponent() < 0 {
		e := uint64(-int64(d.exponent()))
		if n-1 >= e {
			t.expMagnitude = n - 1 - e
		} else {
			t.expMagnitude = e - (n - 1)
			t.expNegative = true
		}
	} else {
		t.expMagnitude = n - 1 + uint64(d.exponent())
	}
	plain := d.exponent() <= 0 && uint64(-int64(d.exponent())) <= n+5
	t.size = n
	if t.negative {
		t.size++
	}
	if plain {
		pointPos := int64(n) + int64(d.exponent())
		if d.exponent() < 0 {
			if pointPos > 0 {
				t.size++ // decimal point within the coefficient
			} else {
				t.size += 2 + uint64(-pointPos) // 0. and leading zeros
				t.zeros = int(-pointPos)
			}
		}
		if pointPos > 0 && uint64(pointPos) < n {
			t.splitAt = uint64(pointPos)
		}
	} else {
		t.scientific = true
		if n > 1 {
			t.size++ // decimal point after the first digit
			t.splitAt = 1
		}
		t.size += 2 + uint64(wordDigits(t.expMagnitude)) // E, sign, digits
	}
	if maxBytes != 0 && t.size > maxBytes || t.size > addressLimit {
		return t, newError("Text", ErrInsufficientStorage)
	}
	return t, nil
}

// emit writes the text left to right into buf and returns the bytes used
// in its final fill. With a nil sink buf is exactly t.size long; otherwise
// a piece that would overflow buf first flushes it to sink. A piece is at
// most 22 bytes, and the sign and zero prefix at most 8, so a sink's buf
// needs at least 30 bytes.
func (t *slowText) emit(buf []byte, sink *strings.Builder) int {
	i := 0
	if t.negative {
		buf[i] = '-'
		i++
	}
	if t.zeros >= 0 {
		buf[i], buf[i+1] = '0', '.'
		i += 2
		for range t.zeros {
			buf[i] = '0'
			i++
		}
	}
	var emitted uint64
	for k := t.v.count - 1; k >= 0; k-- {
		limb := t.v.limb(k)
		width := 9
		if k == t.v.count-1 {
			width = int(limbDigits(limb))
		}
		// The point falls inside this limb's digits or right after them;
		// splitAt is zero or below n, so neither holds for no point.
		inside := t.splitAt > emitted && t.splitAt < emitted+uint64(width)
		after := t.splitAt == emitted+uint64(width)
		piece := width
		if inside || after {
			piece++
		}
		if sink != nil && len(buf)-i < piece {
			sink.Write(buf[:i])
			i = 0
		}
		if width == 9 {
			emitNine(buf, i+9, limb)
		} else {
			emitWord(buf, i+width, uint64(limb))
		}
		if inside {
			at := i + int(t.splitAt-emitted)
			copy(buf[at+1:i+width+1], buf[at:i+width])
			buf[at] = '.'
		}
		i += piece
		if after {
			buf[i-1] = '.'
		}
		emitted += uint64(width)
	}
	if t.scientific {
		piece := 2 + wordDigits(t.expMagnitude)
		if sink != nil && len(buf)-i < piece {
			sink.Write(buf[:i])
			i = 0
		}
		buf[i], buf[i+1] = 'E', '+'
		if t.expNegative {
			buf[i+1] = '-'
		}
		i += piece
		emitWord(buf, i, t.expMagnitude)
	}
	return i
}

// appendSlowText appends the canonical text of a slow coefficient at its
// exact size, growing dst at most once; on refusal dst is unchanged.
func (d Decimal) appendSlowText(dst []byte) ([]byte, error) {
	layout, err := d.slowTextLayout(0, math.MaxInt)
	if err != nil {
		return dst, err
	}
	start := len(dst)
	dst = slices.Grow(dst, int(layout.size))[:start+int(layout.size)]
	layout.emit(dst[start:], nil)
	return dst, nil
}

// String returns canonical text, or a nonnumeric resource diagnostic when
// the checked output size is not addressable.
func (d Decimal) String() string {
	return diagnoseText(d.Text(0))
}

// resourceLimitDiagnostic is String's nonnumeric result on checked refusal.
const resourceLimitDiagnostic = "%!decimal(resource limit)"

// diagnoseText maps a checked Text refusal to String's diagnostic.
func diagnoseText(s string, err error) string {
	if err != nil {
		return resourceLimitDiagnostic
	}
	return s
}

// inlineTextMax bounds canonical text for an inline coefficient: a sign, at
// most 39 digits, and either "0." plus five leading zeros or a point, "E",
// an exponent sign and ten exponent digits.
const inlineTextMax = 56

// appendInlineText appends Text's canonical form for an inline coefficient,
// refusing before any append when the exact size exceeds a positive quota.
// The text is sized exactly and emitted once, right to left, into the
// appended tail.
func (d Decimal) appendInlineText(dst []byte, maxBytes uint64) ([]byte, error) {
	if d.words.hi == 0 {
		n := wordDigits(d.words.lo)
		size := d.inlineTextSize(n)
		if maxBytes != 0 && uint64(size) > maxBytes {
			return dst, newError("Text", ErrInsufficientStorage)
		}
		start := len(dst)
		dst = slices.Grow(dst, size)[:start+size]
		d.emitWordText(dst[start:], n)
		return dst, nil
	}
	c := splitWide(d.words)
	size := d.inlineTextSize(c.n)
	if maxBytes != 0 && uint64(size) > maxBytes {
		return dst, newError("Text", ErrInsufficientStorage)
	}
	start := len(dst)
	dst = slices.Grow(dst, size)[:start+size]
	d.emitWideText(dst[start:], c)
	return dst, nil
}

// wideCoefficient is a two-word inline coefficient split for right-to-left
// emission: the digits of head, unpadded, then one or two
// zero-padded nineteen-digit groups, mid before low. n is the total digit
// count.
type wideCoefficient struct {
	head, mid, low uint64
	groups, n      int
}

// splitWide splits an inline coefficient of at least 2^64 with one
// hardware division, and a second only at or above 10^19×2^64.
func splitWide(w uint128) wideCoefficient {
	const base = 10_000_000_000_000_000_000 // 10^19, the largest power below 2^64
	// w = q×10^19 + low. q's high word is w.hi/10^19, a division by a
	// constant, and its remainder seeds the one hardware division.
	qhi := w.hi / base
	qlo, low := bits.Div64(w.hi-qhi*base, w.lo, base)
	if qhi == 0 {
		return wideCoefficient{head: qlo, low: low, groups: 1, n: 19 + wordDigits(qlo)}
	}
	// q < 2^128/10^19 < 4×10^19: one leading digit and nineteen more.
	top, mid := bits.Div64(qhi, qlo, base)
	return wideCoefficient{head: top, mid: mid, low: low, groups: 2, n: 39}
}

// emitDigits writes c's n digits so that they end just before dst[end] and
// returns the index of the first digit.
func (c *wideCoefficient) emitDigits(dst []byte, end int) int {
	emitPadded19(dst, end, c.low)
	end -= 19
	if c.groups > 1 {
		emitPadded19(dst, end, c.mid)
		end -= 19
	}
	return emitWord(dst, end, c.head)
}

// inlineTextSize returns the exact canonical text length of an inline
// coefficient of n digits. The plain/scientific choice is Text's: plain
// when the exponent is at most zero and at most n+5 zeros follow the point
// before the coefficient's last digit.
func (d Decimal) inlineTextSize(n int) int {
	e := int64(d.exponent())
	size := 0
	if d.negative() {
		size = 1
	}
	if e <= 0 && -e <= int64(n)+5 {
		return size + plainTextSize(n, int(-e))
	}
	adjusted := int64(n) - 1 + e
	return size + plainTextSize(n, n-1) + 2 + wordDigits(uint64(max(adjusted, -adjusted)))
}

// emitWordText fills dst, exactly inlineTextSize long, with the canonical
// text of a one-word coefficient of n digits.
func (d Decimal) emitWordText(dst []byte, n int) {
	if e := int64(d.exponent()); e <= 0 && -e <= int64(n)+5 {
		emitInlinePlain(dst, d.words.lo, int(-e), d.negative())
		return
	}
	dst, frac := d.emitInlineExponent(dst, n)
	emitInlinePlain(dst, d.words.lo, frac, d.negative())
}

// emitWideText fills dst, exactly inlineTextSize long, with the canonical
// text of the two-word coefficient c.
func (d Decimal) emitWideText(dst []byte, c wideCoefficient) {
	dst, frac := d.emitInlineExponent(dst, c.n)
	end := plainDigitsEnd(len(dst), c.n, frac)
	finishPlain(dst, c.emitDigits(dst, end), end, frac, d.negative())
}

// emitInlineExponent starts the canonical text of an inline coefficient of
// n digits in dst, exactly inlineTextSize long. Scientific text is the
// plain rendering of the coefficient with n-1 fractional digits followed by
// E, the exponent sign and the adjusted exponent's digits: it writes that
// suffix and returns the prefix left for the plain part with its frac.
// Plain text returns dst whole and the exponent's magnitude as frac.
func (d Decimal) emitInlineExponent(dst []byte, n int) ([]byte, int) {
	e := int64(d.exponent())
	if e <= 0 && -e <= int64(n)+5 {
		return dst, int(-e)
	}
	adjusted := int64(n) - 1 + e
	magnitude, sign := uint64(adjusted), byte('+')
	if adjusted < 0 {
		magnitude, sign = uint64(-adjusted), '-'
	}
	i := emitWord(dst, len(dst), magnitude)
	dst[i-2], dst[i-1] = 'E', sign
	return dst[:i-2], n - 1
}

// plainTextSize is the unsigned length of a coefficient of n digits written
// with frac fractional digits: the integer digits (at least "0"), and when
// frac is positive a point and frac digits, zero-padded on the left.
func plainTextSize(n, frac int) int {
	if frac == 0 {
		return n
	}
	return max(n-frac, 1) + 1 + frac
}

// emitInlinePlain fills dst, exactly plainTextSize long plus one byte for a
// sign, right to left with w×10^-frac: frac fractional digits two per
// division (zero once w is exhausted, which writes the left padding), the
// point, then the integer digits, at least one, and '-' when negative.
func emitInlinePlain(dst []byte, w uint64, frac int, negative bool) int {
	i := len(dst)
	if frac > 0 {
		for ; frac >= 2; frac -= 2 {
			q, r := w/100, w%100
			i -= 2
			dst[i], dst[i+1] = twoDigits[2*r], twoDigits[2*r+1]
			w = q
		}
		if frac == 1 {
			q := w / 10
			i--
			dst[i] = byte('0' + w - q*10)
			w = q
		}
		i--
		dst[i] = '.'
	}
	i = emitWord(dst, i, w)
	if negative {
		i--
		dst[i] = '-'
	}
	return i
}

// plainDigitsEnd is where the n coefficient digits of plain text exactly
// size long end before finishPlain places the point: one byte short of the
// end when the point falls within the digits and at most as many digits
// follow it as precede it, so finishPlain moves the shorter side.
func plainDigitsEnd(size, n, frac int) int {
	if frac > 0 && frac <= n-frac {
		return size - 1
	}
	return size
}

// finishPlain completes plain text in dst, exactly plainTextSize long plus
// one byte for a sign, whose coefficient digits fill dst[start:end] with
// end from plainDigitsEnd. With frac fractional digits it moves the
// fraction one byte right (end short of len(dst)) or the integer digits
// one byte left for the point or, when no integer digit remains, writes
// "0." and the zeros between the point and the digits; then '-' when
// negative.
func finishPlain(dst []byte, start, end, frac int, negative bool) {
	if frac > 0 {
		point := end - frac
		switch {
		case end < len(dst):
			for i := end; i > point; i-- {
				dst[i] = dst[i-1]
			}
			dst[point] = '.'
		case point > start:
			for i := start; i < point; i++ {
				dst[i-1] = dst[i]
			}
			dst[point-1] = '.'
			start--
		default:
			for i := point; i < start; i++ {
				dst[i] = '0'
			}
			dst[point-2], dst[point-1] = '0', '.'
			start = point - 2
		}
	}
	if negative {
		dst[start-1] = '-'
	}
}

// emitWord writes the decimal digits of w so that they end just before
// dst[end], eight per 64-bit division and then two per 32-bit division,
// and returns the index of the first digit.
func emitWord(dst []byte, end int, w uint64) int {
	i := end
	for w >= 1e8 {
		q := w / 1e8
		emitEight(dst, i, uint32(w-q*1e8))
		i -= 8
		w = q
	}
	v := uint32(w)
	for v >= 100 {
		q, r := v/100, v%100
		i -= 2
		dst[i], dst[i+1] = twoDigits[2*r], twoDigits[2*r+1]
		v = q
	}
	if v >= 10 {
		i -= 2
		dst[i], dst[i+1] = twoDigits[2*v], twoDigits[2*v+1]
		return i
	}
	i--
	dst[i] = byte('0' + v)
	return i
}

// emitEight writes v < 10^8 as exactly eight digits ending just before
// dst[end] with one store. It splits v into four-digit halves in 32-bit
// lanes, then each lane into two-digit 16-bit lanes and those into digit
// bytes, dividing by 100 and 10 with exact multiply-shift reciprocals
// (x×10486>>20 = x/100 below 10^4, x×103>>10 = x/10 below 100).
func emitEight(dst []byte, end int, v uint32) {
	hi, lo := v/10000, v%10000
	x := uint64(hi) | uint64(lo)<<32
	q := x * 10486 >> 20 & 0x0000007f_0000007f
	y := q | (x-q*100)<<16
	t := y * 103 >> 10 & 0x000f_000f_000f_000f
	z := t | (y-t*10)<<8
	binary.LittleEndian.PutUint64(dst[end-8:end], z|0x3030_3030_3030_3030)
}

// emitNine writes a base-10^9 limb as exactly nine digits ending just
// before dst[end].
func emitNine(dst []byte, end int, v uint32) {
	q := v / 1e8
	emitEight(dst, end, v-q*1e8)
	dst[end-9] = byte('0' + q)
}

// emitPadded19 writes v < 10^19 as exactly nineteen digits ending just
// before dst[end].
func emitPadded19(dst []byte, end int, v uint64) {
	hi := v / 1e8
	emitEight(dst, end, uint32(v-hi*1e8))
	top := hi / 1e8 // below 1000
	emitEight(dst, end-8, uint32(hi-top*1e8))
	t := uint32(top)
	q, r := t/100, t%100
	dst[end-19] = byte('0' + q)
	dst[end-18], dst[end-17] = twoDigits[2*r], twoDigits[2*r+1]
}

// twoDigits holds the two-digit decimal text of 00 through 99.
const twoDigits = "0001020304050607080910111213141516171819" +
	"2021222324252627282930313233343536373839" +
	"4041424344454647484950515253545556575859" +
	"6061626364656667686970717273747576777879" +
	"8081828384858687888990919293949596979899"

// wordDigits is the decimal digit count of w, at least one. 1233/4096
// approximates log10(2), so the bit-length estimate is exact or one low
// and one comparison against pow10Words corrects it.
func wordDigits(w uint64) int {
	n := bits.Len64(w) * 1233 >> 12
	if w >= pow10Words[n] {
		n++
	}
	return max(n, 1)
}

// appendUint128 appends the decimal digits of an unsigned 128-bit value.
func appendUint128(dst []byte, w uint128) []byte {
	var buf [39]byte
	if w.hi == 0 {
		return append(dst, buf[emitWord(buf[:], len(buf), w.lo):]...)
	}
	c := splitWide(w)
	return append(dst, buf[c.emitDigits(buf[:], len(buf)):]...)
}
