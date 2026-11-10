// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"fmt"
	"io"
	"math"
	"math/bits"
	"runtime"
	"slices"
	"strconv"
	"strings"
)

// DisplayOptions selects rounding and a per-call budget. The zero value uses
// TiesToEven with no caller limits.
type DisplayOptions struct {
	// Mode rounds the displayed digits.
	Mode RoundingMode
	// Budget bounds the call.
	Budget Budget
}

func displayFailure(op string, cause ErrorCode) (string, error) {
	return "", newError(op, cause)
}

// Fixed renders exactly fractionalDigits decimal places, rounding once with
// TiesToEven. Zero fractional digits renders an integer.
func (d Decimal) Fixed(fractionalDigits uint64) (string, error) {
	if text, ok := d.fixedTiesToEven(fractionalDigits); ok {
		return text, nil
	}
	var buf [inlineTextMax]byte
	if i, ok := d.fixedInline(&buf, fractionalDigits, TiesToEven, displayLimits{}); ok {
		return string(buf[i:]), nil
	}
	return d.display(displayFixed, fractionalDigits, DisplayOptions{}, "Fixed")
}

// FixedWithOptions renders a fixed number of decimal places with the selected
// rounding mode and per-call budget.
func (d Decimal) FixedWithOptions(fractionalDigits uint64, options DisplayOptions) (string, error) {
	if options.Mode == TiesToEven {
		if text, ok := d.fixedTiesToEvenAdmitted(fractionalDigits, options.Budget.display()); ok {
			return text, nil
		}
	}
	var buf [inlineTextMax]byte
	if i, ok := d.fixedInline(&buf, fractionalDigits, options.Mode, options.Budget.display()); ok {
		return string(buf[i:]), nil
	}
	return d.display(displayFixed, fractionalDigits, options, "FixedWithOptions")
}

// fixedTiesToEven serves Fixed with TiesToEven and no budget for a one-word
// inline value and at most 19 places; ok=false defers to the
// planner, which owns every other case and every error. The
// rendered value is the integer q = round(w×10^(e+places)) written with
// places fractional digits: scaled exactly when e+places >= 0 (deferring
// when the product leaves 64 bits), otherwise divided once by 10^cut and
// rounded ties-to-even by comparing the remainder with half the even
// divisor. Neither path fails, so the planner's refusals, which all need a
// budget, a mode or places beyond this range, never apply. As in the
// planner a value that rounds to zero has no sign.
func (d Decimal) fixedTiesToEven(places uint64) (string, bool) {
	q, negative, ok := d.fixedTiesToEvenRound(places)
	if !ok {
		return "", false
	}
	// q < 2^64 has at most 20 digits, so the text is at most a sign, one
	// integer digit, a point and 19 places, or a sign and 20 digits: 22
	// bytes, emitted right-aligned without a size plan.
	var buf [24]byte
	i := emitInlinePlain(buf[:], q, int(places), negative)
	return string(buf[i:]), true
}

// fixedTiesToEvenAdmitted is fixedTiesToEven under a budget: it also
// defers, before the text is allocated, when the budget does not admit the
// text, whose refusal is the planner's because displayLimits.admits applies
// its checks to the exact digit count and size.
func (d Decimal) fixedTiesToEvenAdmitted(places uint64, budget displayLimits) (string, bool) {
	q, negative, ok := d.fixedTiesToEvenRound(places)
	if !ok {
		return "", false
	}
	var buf [24]byte // as in fixedTiesToEven
	i := emitInlinePlain(buf[:], q, int(places), negative)
	if !budget.admitsWord(d.words.lo, len(buf)-i) {
		return "", false
	}
	return string(buf[i:]), true
}

// appendFixedTiesToEven is fixedTiesToEvenAdmitted appending to dst, which
// it leaves unchanged when it defers.
func (d Decimal) appendFixedTiesToEven(dst []byte, places uint64, budget displayLimits) ([]byte, bool) {
	q, negative, ok := d.fixedTiesToEvenRound(places)
	if !ok {
		return dst, false
	}
	size := plainTextSize(wordDigits(q), int(places))
	if negative {
		size++
	}
	if !budget.admitsWord(d.words.lo, size) {
		return dst, false
	}
	n := len(dst)
	dst = slices.Grow(dst, size)[:n+size]
	emitInlinePlain(dst[n:], q, int(places), negative)
	return dst, true
}

// fixedTiesToEvenRound is the rounded integer q and sign of the
// fixedTiesToEven direct path, or ok=false when the planner owns the call.
func (d Decimal) fixedTiesToEvenRound(places uint64) (q uint64, negative, ok bool) {
	if d.slow != nil || d.words.hi != 0 || places > 19 {
		return 0, false, false
	}
	w := d.words.lo
	switch shift := int64(d.exponent()) + int64(places); {
	case w == 0:
	case shift >= 0:
		if shift > 19 {
			return 0, false, false
		}
		high, low := bits.Mul64(w, pow10Words[shift])
		if high != 0 {
			return 0, false, false
		}
		q = low
	case shift < -19:
		return 0, false, false
	default:
		divisor := pow10Words[-shift]
		q = w / divisor
		// divisor is even, so half is exact and q+1 cannot overflow.
		if r, half := w-q*divisor, divisor/2; r > half || r == half && q&1 == 1 {
			q++
		}
	}
	return q, d.negative() && q != 0, true
}

// displayInlinePlaces bounds the places the inline display paths serve: the
// digits of a coefficient scaled to 10^38, the largest power of ten below
// 2^128.
const displayInlinePlaces = 38

// displayLimits is the display family's view of a Budget: the output-byte
// and work axes, the only ones display reads, small enough to travel in
// registers through the inline paths.
type displayLimits struct {
	MaxOutputBytes uint64
	MaxWork        uint64
}

// display is b's display axes.
func (b Budget) display() displayLimits {
	return displayLimits{MaxOutputBytes: b.MaxOutputBytes, MaxWork: b.MaxWork}
}

// admits reports whether l admits a rendering of size bytes from an
// n-digit source coefficient: the planner's final checks, size against
// MaxOutputBytes and n+size against MaxWork. Its earlier refusals are
// implied, since they compare n alone with MaxWork and a lower bound of
// size with MaxOutputBytes.
func (l displayLimits) admits(n, size uint64) bool {
	return (l.MaxOutputBytes == 0 || size <= l.MaxOutputBytes) && (l.MaxWork == 0 || n+size <= l.MaxWork)
}

// admitsWord is admits for a rendering of the one-word coefficient w, whose
// digits are counted only under a budget.
func (l displayLimits) admitsWord(w uint64, size int) bool {
	return l == (displayLimits{}) || l.admits(uint64(wordDigits(w)), uint64(size))
}

// emitInlineFixed writes q×10^-frac right-aligned in buf[:end] as
// emitInlinePlain does, for a q of either inline width, and returns the
// index of the first byte. The text needs at most a sign, max(39, frac+1)
// digits and a point.
func emitInlineFixed(buf []byte, end int, q uint128, frac int, negative bool) int {
	if q.hi == 0 {
		return emitInlinePlain(buf[:end], q.lo, frac, negative)
	}
	c := splitWide(q)
	size := plainTextSize(c.n, frac)
	if negative {
		size++
	}
	dst := buf[end-size : end]
	digitsEnd := plainDigitsEnd(size, c.n, frac)
	finishPlain(dst, c.emitDigits(dst, digitsEnd), digitsEnd, frac, negative)
	return end - size
}

// fixedInline serves Fixed for an inline value, at most displayInlinePlaces
// places, any rounding mode and any budget, right-aligned in buf from the
// returned index; ok=false defers to the planner. The rendered value is the
// coefficient q of d quantized to exponent −places, which the inline
// quantize kernel rounds as the planner does: the same guard, sticky and
// retained-parity classes under the value's sign, and an unsigned zero when
// nothing is retained. The path defers when that kernel does (a padded
// coefficient leaving 128 bits), on an Exact refusal and on an invalid
// mode, so the planner reports every error; and when the budget does not
// admit the text, whose refusal is the planner's because
// displayLimits.admits applies its checks to the exact digit count and
// size. The text is at most a sign, 39 digits and a point, or a sign, "0."
// and 38 places.
func (d Decimal) fixedInline(buf *[inlineTextMax]byte, places uint64, mode RoundingMode, budget displayLimits) (int, bool) {
	if d.slow != nil || places > displayInlinePlaces || mode > Exact {
		return 0, false
	}
	var q uint128
	n, negative := uint64(1), false
	if !d.isZero() {
		rounded, _, refused, ok := inlineQuantize(d, -int32(places), mode)
		if !ok || refused {
			return 0, false
		}
		q, negative, n = rounded.words, rounded.negative(), inlineDigits(d.words)
	}
	i := emitInlineFixed(buf[:], len(buf), q, int(places), negative)
	if !budget.admits(n, uint64(len(buf)-i)) {
		return 0, false
	}
	return i, true
}

// Scientific renders exactly significantDigits coefficient digits, one before
// the point, an uppercase E, and an explicitly signed exponent.
func (d Decimal) Scientific(significantDigits uint64) (string, error) {
	var buf [scientificInlineMax]byte
	if i, ok := d.scientificTiesToEven(&buf, significantDigits); ok {
		return string(buf[i:]), nil
	}
	var wide [inlineTextMax]byte
	if i, ok := d.scientificInline(&wide, significantDigits, TiesToEven, displayLimits{}); ok {
		return string(wide[i:]), nil
	}
	return d.display(displayScientific, significantDigits, DisplayOptions{}, "Scientific")
}

// ScientificWithOptions renders significantDigits coefficient digits with
// explicit rounding and display budget.
func (d Decimal) ScientificWithOptions(significantDigits uint64, options DisplayOptions) (string, error) {
	if options.Mode == TiesToEven {
		var buf [scientificInlineMax]byte
		if i, ok := d.scientificTiesToEven(&buf, significantDigits); ok && options.Budget.display().admitsWord(d.words.lo, len(buf)-i) {
			return string(buf[i:]), nil
		}
	}
	var wide [inlineTextMax]byte
	if i, ok := d.scientificInline(&wide, significantDigits, options.Mode, options.Budget.display()); ok {
		return string(wide[i:]), nil
	}
	return d.display(displayScientific, significantDigits, options, "ScientificWithOptions")
}

// scientificInlineMax bounds scientificTiesToEven's text: a sign, 19 digits,
// a point, E, an exponent sign and at most 10 exponent digits.
const scientificInlineMax = 33

// scientificTiesToEven serves Scientific with TiesToEven for a one-word
// inline value and 1 to 19 significant digits, right-aligned in buf from
// the returned index; ok=false defers to the planner, which owns every
// other case and every error. A budgeted caller admits the text by
// displayLimits.admitsWord before using it. The coefficient is the
// integer q of exactly places digits: w padded with zeros when it has no
// more digits than places, otherwise divided once by 10^cut and rounded
// ties-to-even by comparing the remainder with half the even divisor, a
// carry to 10^places renormalizing to 10^(places−1) one decade up. The
// exponent is the adjusted exponent of q. Neither path fails, so the
// planner's refusals, which all need a budget, a mode or places beyond this
// range, never apply. A zero renders places zeros at exponent +0.
func (d Decimal) scientificTiesToEven(buf *[scientificInlineMax]byte, places uint64) (int, bool) {
	if d.slow != nil || d.words.hi != 0 || places-1 >= 19 {
		return 0, false
	}
	w := d.words.lo
	var x int64
	if w != 0 {
		n := wordDigits(w)
		x = int64(d.exponent()) + int64(n) - 1
		if n <= int(places) {
			w *= pow10Words[int(places)-n]
		} else {
			divisor := pow10Words[n-int(places)]
			q := w / divisor
			if r, half := w-q*divisor, divisor/2; r > half || r == half && q&1 == 1 {
				if q++; q == pow10Words[places] {
					q /= 10
					x++
				}
			}
			w = q
		}
	}
	magnitude, sign := uint64(x), byte('+')
	if x < 0 {
		magnitude, sign = uint64(-x), '-'
	}
	i := emitWord(buf[:], len(buf), magnitude)
	buf[i-1], buf[i-2] = sign, 'E'
	end := i - 2
	if w == 0 {
		i = end - int(places)
		for k := i; k < end; k++ {
			buf[k] = '0'
		}
	} else {
		i = emitWord(buf[:], end, w) // exactly places digits
	}
	if places > 1 {
		buf[i-1], buf[i] = buf[i], '.'
		i--
	}
	if d.negative() {
		i--
		buf[i] = '-'
	}
	return i, true
}

// emitInlineExponentSuffix writes E, the sign and the digits of the
// exponent x at the end of buf and returns the index of the E.
func emitInlineExponentSuffix(buf []byte, x int64) int {
	magnitude, sign := uint64(x), byte('+')
	if x < 0 {
		magnitude, sign = uint64(-x), '-'
	}
	i := emitWord(buf, len(buf), magnitude)
	buf[i-1], buf[i-2] = sign, 'E'
	return i - 2
}

// scientificInline serves Scientific for an inline value, 1 to
// displayInlinePlaces significant digits, any rounding mode and any budget,
// right-aligned in buf from the returned index; ok=false defers to the
// planner. The coefficient is the integer q of exactly places digits: w
// padded with zeros when it has no more digits than places, and otherwise
// quantized by the inline kernel at the cut that keeps places digits, which
// rounds as the planner does, a carry to 10^places renormalizing to
// 10^(places−1) one decade up. The exponent is the adjusted exponent of q.
// The path defers when the kernel does, on an Exact refusal and on an
// invalid mode, so the planner reports every error; and when the budget
// does not admit the text, whose refusal is the planner's because
// displayLimits.admits applies its checks to the exact digit count and
// size. The text is at most a sign, 38 digits, a point, E, a sign and 10
// exponent digits. A zero renders places zeros at exponent +0.
func (d Decimal) scientificInline(buf *[inlineTextMax]byte, places uint64, mode RoundingMode, budget displayLimits) (int, bool) {
	if d.slow != nil || places-1 >= displayInlinePlaces || mode > Exact {
		return 0, false
	}
	q := pow10Wide[places-1] // a zero's leading digit is overwritten below
	n, zero := uint64(1), d.isZero()
	var x int64
	if !zero {
		n = inlineDigits(d.words)
		x = int64(d.exponent()) + int64(n) - 1
		if n <= places {
			var ok bool
			if q, ok = inlineScale(d.words, places-n); !ok {
				return 0, false
			}
		} else {
			target := int64(d.exponent()) + int64(n-places)
			if target > math.MaxInt32 {
				return 0, false
			}
			rounded, _, refused, ok := inlineQuantize(d, int32(target), mode)
			if !ok || refused {
				return 0, false
			}
			if q = rounded.words; q == pow10Wide[places] {
				q = pow10Wide[places-1]
				x++
			}
		}
	}
	end := emitInlineExponentSuffix(buf[:], x)
	// q has exactly places digits: the point goes after the first.
	i := emitInlineFixed(buf[:], end, q, int(places)-1, d.negative())
	if zero {
		buf[i] = '0'
	}
	if !budget.admits(n, uint64(len(buf)-i)) {
		return 0, false
	}
	return i, true
}

// Engineering renders a numerically equal value with an exponent divisible
// by three. It never rounds.
func (d Decimal) Engineering() (string, error) {
	var buf [inlineTextMax]byte
	if i, ok := d.engineeringInline(&buf, displayLimits{}); ok {
		return string(buf[i:]), nil
	}
	return d.display(displayEngineering, 0, DisplayOptions{}, "Engineering")
}

// EngineeringWithBudget renders engineering notation under a per-call budget.
func (d Decimal) EngineeringWithBudget(budget Budget) (string, error) {
	var buf [inlineTextMax]byte
	if i, ok := d.engineeringInline(&buf, budget.display()); ok {
		return string(buf[i:]), nil
	}
	return d.display(displayEngineering, 0, DisplayOptions{Budget: budget}, "EngineeringWithBudget")
}

// engineeringInline serves Engineering for an inline value under any
// budget, right-aligned in buf from the returned index; ok=false defers to
// the planner. The exponent is the adjusted exponent rounded down to a
// multiple of three, and the one to three integer digits it leaves are the
// coefficient's leading digits, zero-padded when it has fewer; the rest
// follow the point. Nothing is rounded and nothing fails without a budget.
// The path defers when the budget does not admit the text, whose refusal
// is the planner's because displayLimits.admits applies its checks to the
// exact digit count and size. The text is at most a sign, 39 digits, a
// point, E, a sign and 10 exponent digits. A zero renders 0E+0.
func (d Decimal) engineeringInline(buf *[inlineTextMax]byte, budget displayLimits) (int, bool) {
	if d.slow != nil {
		return 0, false
	}
	w := d.words
	n := uint64(1)
	var x int64
	frac := 0
	if !d.isZero() {
		n = inlineDigits(w)
		adjusted := int64(d.exponent()) + int64(n) - 1
		leading := (adjusted%3+3)%3 + 1
		x = adjusted - (leading - 1)
		if pad := leading - int64(n); pad > 0 {
			w.lo *= pow10Words[pad] // one or two digits padded to at most three
		} else {
			frac = int(-pad)
		}
	}
	end := emitInlineExponentSuffix(buf[:], x)
	i := emitInlineFixed(buf[:], end, w, frac, d.negative())
	if !budget.admits(n, uint64(len(buf)-i)) {
		return 0, false
	}
	return i, true
}

// appendInlineRoom reports whether a dst of the given length can take an
// inline display text, at most inlineTextMax bytes, within displayLimit,
// which is at least MaxInt32 on every target. A longer dst defers to the
// planner, which refuses a result the runtime cannot address.
func appendInlineRoom(length int) bool {
	return length <= math.MaxInt32-inlineTextMax
}

// AppendFixed appends FixedWithOptions's text to dst; DisplayOptions{} is
// Fixed. On refusal it returns dst unchanged and the error.
func (d Decimal) AppendFixed(dst []byte, fractionalDigits uint64, options DisplayOptions) ([]byte, error) {
	if !appendInlineRoom(len(dst)) {
		return d.appendDisplay(dst, displayFixed, fractionalDigits, options, "AppendFixed")
	}
	if options.Mode == TiesToEven {
		if out, ok := d.appendFixedTiesToEven(dst, fractionalDigits, options.Budget.display()); ok {
			return out, nil
		}
	}
	var buf [inlineTextMax]byte
	if i, ok := d.fixedInline(&buf, fractionalDigits, options.Mode, options.Budget.display()); ok {
		return append(dst, buf[i:]...), nil
	}
	return d.appendDisplay(dst, displayFixed, fractionalDigits, options, "AppendFixed")
}

// AppendScientific appends ScientificWithOptions's text to dst;
// DisplayOptions{} is Scientific. On refusal it returns dst unchanged and
// the error.
func (d Decimal) AppendScientific(dst []byte, significantDigits uint64, options DisplayOptions) ([]byte, error) {
	if !appendInlineRoom(len(dst)) {
		return d.appendDisplay(dst, displayScientific, significantDigits, options, "AppendScientific")
	}
	if options.Mode == TiesToEven {
		var buf [scientificInlineMax]byte
		if i, ok := d.scientificTiesToEven(&buf, significantDigits); ok && options.Budget.display().admitsWord(d.words.lo, len(buf)-i) {
			return append(dst, buf[i:]...), nil
		}
	}
	var wide [inlineTextMax]byte
	if i, ok := d.scientificInline(&wide, significantDigits, options.Mode, options.Budget.display()); ok {
		return append(dst, wide[i:]...), nil
	}
	return d.appendDisplay(dst, displayScientific, significantDigits, options, "AppendScientific")
}

// AppendEngineering appends EngineeringWithBudget's text to dst; Budget{}
// is Engineering. On refusal it returns dst unchanged and the error.
func (d Decimal) AppendEngineering(dst []byte, budget Budget) ([]byte, error) {
	var buf [inlineTextMax]byte
	if i, ok := d.engineeringInline(&buf, budget.display()); ok && appendInlineRoom(len(dst)) {
		return append(dst, buf[i:]...), nil
	}
	return d.appendDisplay(dst, displayEngineering, 0, DisplayOptions{Budget: budget}, "AppendEngineering")
}

type displayKind uint8

const (
	displayFixed displayKind = iota
	displayScientific
	displayEngineering
)

type displayPlan struct {
	v                                         coefficientView
	digits                                    [39]byte // inline coefficient text
	inline                                    bool
	kind                                      displayKind
	n, size, count, keep, fractional, leading uint64
	negative, zero, carry, roundUp            bool
	changeAt                                  uint64
	expNegative                               bool
	expMagnitude                              uint64
}

func displayAdd(a, b uint64) (uint64, bool) {
	if a > math.MaxUint64-b {
		return 0, false
	}
	return a + b, true
}

func displayExponent(n uint64, e int32) (negative bool, magnitude uint64) {
	if e >= 0 {
		return false, n - 1 + uint64(e)
	}
	m := uint64(-int64(e))
	if n-1 < m {
		return true, m - (n - 1)
	}
	return false, n - 1 - m
}

func (d Decimal) display(kind displayKind, places uint64, options DisplayOptions, op string) (string, error) {
	p, err := d.planDisplay(kind, places, options, op)
	if err != nil {
		return "", err
	}
	return p.render(), nil
}

func (d Decimal) appendDisplay(dst []byte, kind displayKind, places uint64, options DisplayOptions, op string) ([]byte, error) {
	p, err := d.planDisplay(kind, places, options, op)
	if err != nil {
		return dst, err
	}
	if p.size > displayLimit()-min(displayLimit(), uint64(len(dst))) {
		_, err := displayFailure(op, ErrInsufficientStorage)
		return dst, err
	}
	return p.appendTo(dst), nil
}

// displayLimit is the largest text the runtime can be asked for: an int
// length within the target's largest object. Beyond it an allocation
// panics instead of failing.
func displayLimit() uint64 {
	maxObject, _, _ := bigIntRuntimeLimits(runtime.GOOS, runtime.GOARCH, uint64(bits.UintSize))
	return min(maxObject, uint64(math.MaxInt))
}

func (d Decimal) planDisplay(kind displayKind, places uint64, options DisplayOptions, op string) (displayPlan, error) {
	var p displayPlan
	if options.Mode > Exact || kind == displayScientific && places == 0 {
		_, err := displayFailure(op, ErrInvalidContext)
		return p, err
	}
	// Inline coefficients are rendered once; digit reads then index text
	// instead of dividing a limb per digit.
	var n uint64
	if d.slow == nil {
		p.inline = true
		n = uint64(len(appendUint128(p.digits[:0], d.words)))
	} else {
		p.v = coefficientViewOf(d)
		var ok bool
		n, ok = checkedDigitCount(p.v.count, p.v.limb(p.v.count-1))
		if !ok {
			_, err := displayFailure(op, ErrInsufficientStorage)
			return p, err
		}
	}
	p.kind, p.n, p.negative = kind, n, d.negative() && !d.isZero()
	budget := options.Budget
	if budget.MaxWork != 0 && n > budget.MaxWork {
		_, err := displayFailure(op, ErrInsufficientStorage)
		return p, err
	}
	// These bounds need no coefficient scan and precede an Exact cut.
	var lower uint64
	switch kind {
	case displayFixed:
		if places > uint64(math.MaxInt)-2 {
			_, err := displayFailure(op, ErrInsufficientStorage)
			return p, err
		}
		lower = 1
		if places != 0 {
			lower = places + 2
		}
	case displayScientific:
		if places > uint64(math.MaxInt)-4 {
			_, err := displayFailure(op, ErrInsufficientStorage)
			return p, err
		}
		lower = places + 3
		if places > 1 {
			lower++
		}
	case displayEngineering:
		lower = 4
	}
	if budget.MaxOutputBytes != 0 && lower > budget.MaxOutputBytes {
		_, err := displayFailure(op, ErrInsufficientStorage)
		return p, err
	}
	p.zero = d.isZero()
	if err := p.layout(d.exponent(), places, budget, op, func(cut uint64) error { return p.round(cut, options.Mode, op) }); err != nil {
		return displayPlan{}, err
	}
	return p, nil
}

// layout plans the rendered form from the digit count, exponent and places
// (the rounding callback supplies what reading the digits decides) and
// measures it against the budget; shared by planDisplay and the display
// estimators.
func (p *displayPlan) layout(exponent int32, places uint64, budget Budget, op string, round func(cut uint64) error) error {
	n, kind := p.n, p.kind
	switch kind {
	case displayFixed:
		p.fractional = places
		if p.zero {
			p.count = 1
			break
		}
		if exponent >= 0 || places >= uint64(-int64(exponent)) {
			var grow uint64
			if exponent >= 0 {
				grow = places + uint64(exponent)
			} else {
				grow = places - uint64(-int64(exponent))
			}
			p.keep = n
			var ok bool
			p.count, ok = displayAdd(n, grow)
			if !ok {
				_, err := displayFailure(op, ErrInsufficientStorage)
				return err
			}
		} else {
			cut := uint64(-int64(exponent)) - places
			if err := round(cut); err != nil {
				return err
			}
		}
	case displayScientific:
		p.expNegative, p.expMagnitude = displayExponent(n, exponent)
		if p.zero {
			p.expNegative, p.expMagnitude = false, 0
			p.count = places
			break
		}
		if places >= n {
			p.keep, p.count = n, places
		} else {
			if err := round(n - places); err != nil {
				return err
			}
			p.count = places
			if p.carry {
				p.expNegative, p.expMagnitude = displaySignedIncrement(p.expNegative, p.expMagnitude)
			}
		}
	case displayEngineering:
		if p.zero {
			p.count, p.leading = 1, 1
			p.expMagnitude = 0
			break
		}
		negative, magnitude := displayExponent(n, exponent)
		var remainder uint64
		if negative {
			remainder = (3 - magnitude%3) % 3
			p.expNegative = true
			p.expMagnitude = magnitude + remainder
		} else {
			remainder = magnitude % 3
			p.expMagnitude = magnitude - remainder
		}
		if p.expMagnitude == 0 {
			p.expNegative = false
		}
		p.leading = remainder + 1
		p.keep, p.count = n, n
		if p.count < p.leading {
			p.count = p.leading
		}
	}
	if !p.measure() || budget.MaxOutputBytes != 0 && p.size > budget.MaxOutputBytes ||
		!quantizeAdmitted(budget.MaxWork, quantizeCount{lo: n}.addUint(p.size)) {
		_, err := displayFailure(op, ErrInsufficientStorage)
		return err
	}
	return nil
}

func displaySignedIncrement(negative bool, magnitude uint64) (bool, uint64) {
	if negative {
		if magnitude == 1 {
			return false, 0
		}
		return true, magnitude - 1
	}
	return false, magnitude + 1
}

func (p *displayPlan) round(cut uint64, mode RoundingMode, op string) error {
	keep := uint64(0)
	if cut < p.n {
		keep = p.n - cut
	}
	var guard, low uint32
	sticky := false
	if cut > p.n {
		sticky = true
	} else if p.inline {
		guard, sticky, low = p.inlineDiscard(cut)
	} else {
		guard, sticky, low = quantizeDiscard(&p.v, cut)
	}
	if mode == Exact && (guard != 0 || sticky) {
		_, err := displayFailure(op, ErrInexact)
		return err
	}
	p.roundUp = contextRoundUp(mode, p.negative, guard, sticky, low)
	if keep == 0 {
		p.count = 1
		if p.roundUp {
			p.carry = true
		} else {
			p.zero, p.negative = true, false
		}
		return nil
	}
	p.keep, p.count = keep, keep
	if !p.roundUp {
		return nil
	}
	for i := keep; i > 0; i-- {
		if p.sourceDigit(i-1) != '9' {
			p.changeAt = i - 1
			return nil
		}
	}
	p.carry, p.count = true, keep+1
	return nil
}

func (p *displayPlan) sourceDigit(i uint64) byte {
	if p.inline {
		return p.digits[i]
	}
	return byte(quantizeDigit(&p.v, p.n-1-i)) + '0'
}

// inlineDiscard is quantizeDiscard over the rendered inline digits, for
// 0 < cut <= n: the first discarded digit, whether any later discarded digit
// is nonzero, and the lowest retained digit (zero when none is retained).
func (p *displayPlan) inlineDiscard(cut uint64) (guard uint32, sticky bool, retainedLow uint32) {
	at := p.n - cut
	guard = uint32(p.digits[at] - '0')
	for _, digit := range p.digits[at+1 : p.n] {
		if digit != '0' {
			sticky = true
			break
		}
	}
	if at > 0 {
		retainedLow = uint32(p.digits[at-1] - '0')
	}
	return guard, sticky, retainedLow
}

func (p *displayPlan) coefficientDigit(i uint64) byte {
	if p.zero {
		return '0'
	}
	if p.carry {
		if i == 0 {
			return '1'
		}
		return '0'
	}
	if i >= p.keep {
		return '0'
	}
	if p.roundUp {
		if i == p.changeAt {
			return p.sourceDigit(i) + 1
		}
		if i > p.changeAt {
			return '0'
		}
	}
	return p.sourceDigit(i)
}

func (p *displayPlan) measure() bool {
	var size uint64
	limit := displayLimit()
	add := func(v uint64) bool {
		var ok bool
		size, ok = displayAdd(size, v)
		return ok && size <= limit
	}
	if p.negative && !add(1) {
		return false
	}
	switch p.kind {
	case displayFixed:
		integral := uint64(1)
		if p.count > p.fractional {
			integral = p.count - p.fractional
		}
		if !add(integral) {
			return false
		}
		if p.fractional > 0 && (!add(1) || !add(p.fractional)) {
			return false
		}
	case displayScientific, displayEngineering:
		if !add(p.count) {
			return false
		}
		leading := p.leading
		if p.kind == displayScientific {
			leading = 1
		}
		if p.count > leading && !add(1) {
			return false
		}
		if !add(2) {
			return false
		} // E and sign
		var scratch [20]byte
		if !add(uint64(len(strconv.AppendUint(scratch[:0], p.expMagnitude, 10)))) {
			return false
		}
	}
	p.size = size
	return true
}

func (p *displayPlan) render() string {
	// Output of at most 64 bytes stays in the sink's stack chunk and is
	// converted once to an exactly sized string; longer output is flushed
	// in chunks into a builder grown once to the planned size.
	var s displaySink
	var large strings.Builder
	if p.size > uint64(len(s.chunk)) {
		large.Grow(int(p.size))
		s.large = &large
	}
	p.emit(&s)
	if s.large == nil {
		return string(s.chunk[:s.n])
	}
	large.Write(s.chunk[:s.n])
	return large.String()
}

// appendTo appends the planned text to dst, grown once to fit it. The sink
// copies into the reserved region, so neither it nor its builder escapes.
func (p *displayPlan) appendTo(dst []byte) []byte {
	n := len(dst)
	dst = slices.Grow(dst, int(p.size))[:n+int(p.size)]
	s := displaySink{out: dst[n:]}
	p.emit(&s)
	copy(s.out[s.off:], s.chunk[:s.n])
	return dst
}

// emit writes the planned text through s.
func (p *displayPlan) emit(s *displaySink) {
	if p.negative {
		s.put('-')
	}
	switch p.kind {
	case displayFixed:
		if p.count <= p.fractional {
			s.put('0')
			if p.fractional != 0 {
				s.put('.')
				for i := p.count; i < p.fractional; i++ {
					s.put('0')
				}
			}
		}
		for i := uint64(0); i < p.count; i++ {
			if p.count > p.fractional && p.fractional != 0 && i == p.count-p.fractional {
				s.put('.')
			}
			s.put(p.coefficientDigit(i))
		}
	case displayScientific, displayEngineering:
		leading := p.leading
		if p.kind == displayScientific {
			leading = 1
		}
		for i := uint64(0); i < p.count; i++ {
			if i == leading {
				s.put('.')
			}
			s.put(p.coefficientDigit(i))
		}
		s.put('E')
		if p.expNegative {
			s.put('-')
		} else {
			s.put('+')
		}
		var scratch [20]byte
		for _, c := range strconv.AppendUint(scratch[:0], p.expMagnitude, 10) {
			s.put(c)
		}
	}
}

// displaySink collects rendered bytes in a stack chunk, flushing each full
// chunk into dst when appending, else into large, which is set only when the
// planned size exceeds the chunk.
type displaySink struct {
	chunk [64]byte
	n     int
	large *strings.Builder
	out   []byte // the reserved append region, when appending
	off   int    // bytes of out already filled
}

func (s *displaySink) put(c byte) {
	if s.n == len(s.chunk) {
		s.flush()
	}
	s.chunk[s.n] = c
	s.n++
}

// flush stays out of line so that put, inlined at every byte, carries only
// the chunk check.
//
//go:noinline
func (s *displaySink) flush() {
	if s.out != nil {
		s.off += copy(s.out[s.off:], s.chunk[:])
	} else {
		s.large.Write(s.chunk[:])
	}
	s.n = 0
}

// Format implements the closed %v/%s, %f, and %e fmt verb set. An explicit
// %e precision counts total significant digits, unlike float formatting.
// %+v is %v, and %#v is the Go expression decimal.MustParse("text") that
// rebuilds the value and its cohort, because fmt passes those flags to
// every field of a struct printed with them. A *Decimal field prints the
// same expression, which then has the value's type, not the pointer's.
func (d Decimal) Format(state fmt.State, verb rune) {
	sharp := verb == 'v' && state.Flag('#')
	misplaced := verb != 'v' && (state.Flag('+') || state.Flag('#'))
	if misplaced || state.Flag(' ') || state.Flag('0') || state.Flag('\'') {
		_, _ = io.WriteString(state, "%!decimal(unsupported format)")
		return
	}
	precision, explicit := state.Precision()
	var text string
	var err error
	switch verb {
	case 'v', 's':
		if explicit {
			_, _ = io.WriteString(state, "%!decimal(unsupported format)")
			return
		}
		text, err = d.Text(0)
		if sharp && err == nil {
			text = `decimal.MustParse("` + text + `")`
		}
	case 'f':
		places := uint64(precision)
		if !explicit {
			places = 0
			if d.exponent() < 0 {
				places = uint64(-int64(d.exponent()))
			}
		}
		text, err = d.Fixed(places)
	case 'e':
		if explicit && precision == 0 {
			_, _ = io.WriteString(state, "%!decimal(invalid precision)")
			return
		}
		places := uint64(precision)
		if !explicit {
			switch {
			case d.isZero():
				places = 1
			case d.slow == nil:
				places = inlineDigits(d.words)
			default:
				v := coefficientViewOf(d)
				places, _ = checkedDigitCount(v.count, v.limb(v.count-1))
			}
		}
		text, err = d.Scientific(places)
	default:
		_, _ = io.WriteString(state, "%!decimal(unsupported format)")
		return
	}
	if err != nil {
		_, _ = io.WriteString(state, "%!decimal(resource limit)")
		return
	}
	padding := 0
	if width, ok := state.Width(); ok && width > len(text) {
		padding = width - len(text)
	}
	if !state.Flag('-') && !writePadding(state, padding) {
		return
	}
	if _, err = io.WriteString(state, text); err == nil && state.Flag('-') {
		_ = writePadding(state, padding)
	}
}

// formatSpaces bounds each padding write to 4096 bytes; it is built once so
// padding neither allocates nor refills a buffer per call.
var formatSpaces = strings.Repeat(" ", 4096)

// writePadding writes n spaces in bounded chunks, stopping at a write error.
func writePadding(w io.Writer, n int) bool {
	for n > 0 {
		chunk := min(n, len(formatSpaces))
		if _, err := io.WriteString(w, formatSpaces[:chunk]); err != nil {
			return false
		}
		n -= chunk
	}
	return true
}
