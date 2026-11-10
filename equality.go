// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"encoding/binary"
	"hash/maphash"
	"math"
	"math/bits"
	"slices"
)

const decimalLimbBase = uint64(1_000_000_000)

var decimalPowers = [...]uint32{1, 10, 100, 1_000, 10_000, 100_000, 1_000_000, 10_000_000, 100_000_000}

// Hasher supplies Decimal's numeric equality and seeded hash to consumers.
// It has no seed or mutable state; the caller owns the maphash.Hash.
type Hasher struct{}

// Hash appends a canonical binary encoding of value to h.
func (Hasher) Hash(h *maphash.Hash, value Decimal) {
	if value.isZero() {
		_ = h.WriteByte(0)
		return
	}
	if value.slow == nil && value.words.hi == 0 {
		hashWord(h, inlineReduce(value))
		return
	}
	if value.slow == nil {
		// The reduced form of an inline value is inline.
		if reduced := value.Reduce(); reduced.words.hi == 0 {
			hashWord(h, reduced)
		} else {
			hashWide(h, reduced)
		}
		return
	}
	v := coefficientViewOf(value)
	k := removableZeros(&v, value.exponent())
	q, r := int(k/9), uint32(k%9)
	count := reducedLimbCount(&v, q, r)
	// One buffered write per chunk instead of one per limb; maphash hashes
	// the concatenated byte stream, so the hash is unchanged.
	var buf [hashChunk]byte
	buf[0] = 1
	if value.negative() {
		buf[0] = 2
	}
	binary.BigEndian.PutUint32(buf[1:], uint32(int64(value.exponent())+int64(k)))
	n := 5 + binary.PutUvarint(buf[5:], uint64(count))
	cursor := newReducedCursor(&v, q, r)
	for range count {
		if n > len(buf)-4 {
			_, _ = h.Write(buf[:n])
			n = 0
		}
		limb, _ := cursor.next()
		binary.BigEndian.PutUint32(buf[n:], limb)
		n += 4
	}
	_, _ = h.Write(buf[:n])
}

// hashChunk is Hash's stack buffer size: the header (sign, exponent and a
// uvarint count of at most ten bytes) plus every limb of any inline value.
const hashChunk = 128

// hashWord writes Hash's canonical encoding of an already reduced nonzero
// one-word value in one call: sign byte, reduced exponent, uvarint limb
// count (at most three below 2^64) and big-endian base-10^9 limbs.
func hashWord(h *maphash.Hash, reduced Decimal) {
	var limbs [3]uint32
	count := 0
	for w := reduced.words.lo; w != 0; w /= decimalLimbBase {
		limbs[count] = uint32(w % decimalLimbBase)
		count++
	}
	var buf [1 + 4 + 1 + 3*4]byte
	buf[0] = 1
	if reduced.negative() {
		buf[0] = 2
	}
	binary.BigEndian.PutUint32(buf[1:], uint32(reduced.exponent()))
	buf[5] = byte(count) // a one-byte uvarint
	n := 6
	for i := count - 1; i >= 0; i-- {
		binary.BigEndian.PutUint32(buf[n:], limbs[i])
		n += 4
	}
	_, _ = h.Write(buf[:n])
}

// hashWide is hashWord for an already reduced two-word value, of three to
// five limbs.
func hashWide(h *maphash.Hash, reduced Decimal) {
	var limbs [5]uint32
	count := wordLimbs(&limbs, reduced.words.hi, reduced.words.lo)
	var buf [1 + 4 + 1 + 5*4]byte
	buf[0] = 1
	if reduced.negative() {
		buf[0] = 2
	}
	binary.BigEndian.PutUint32(buf[1:], uint32(reduced.exponent()))
	buf[5] = byte(count) // a one-byte uvarint
	n := 6
	for i := count - 1; i >= 0; i-- {
		binary.BigEndian.PutUint32(buf[n:], limbs[i])
		n += 4
	}
	_, _ = h.Write(buf[:n])
}

// Equal reports numeric equality, independent of cohort scale.
func (Hasher) Equal(x, y Decimal) bool { return x.Equal(y) }

// Reduce returns the unique in-domain member of d's numeric cohort.
// It leaves d and any values sharing d's slow coefficient untouched.
func (d Decimal) Reduce() Decimal {
	if d.isZero() {
		return Decimal{}
	}
	if d.slow == nil {
		if d.words.hi == 0 {
			return inlineReduce(d)
		}
		// hi*2^64 + lo is congruent to 6*hi + lo modulo 10, so a nonzero
		// last digit leaves nothing to strip.
		if (6*(d.words.hi%10)+d.words.lo%10)%10 != 0 {
			return d
		}
		if reduced, ok := inlineReduceWide(d); ok {
			return reduced
		}
	}
	return reduceGeneral(d)
}

// inlineReduceWide is Reduce for a two-word coefficient w whose low
// nineteen digits are not all zero; ok is false otherwise. One division
// splits w = q·10^19 + low with q < 2^65. The one-word kernel strips low's
// m ≤ 18 trailing zeros, which are w's, under the same exponent ceiling,
// and the reduced coefficient w/10^m = q·10^(19−m) + low/10^m is at most w,
// so the recombination stays within 128 bits.
func inlineReduceWide(d Decimal) (Decimal, bool) {
	const base = 10_000_000_000_000_000_000 // 10^19
	qhi := d.words.hi / base
	qlo, low := bits.Div64(d.words.hi-qhi*base, d.words.lo, base)
	if low == 0 {
		return Decimal{}, false
	}
	tail := inlineReduce(inlineDecimal(uint128{lo: low}, d.exponent(), false))
	m := int64(tail.exponent()) - int64(d.exponent())
	if m == 0 {
		return d, true
	}
	scale := pow10Words[19-m]
	hi, lo := bits.Mul64(qlo, scale)
	lo, carry := bits.Add64(lo, tail.words.lo, 0)
	return inlineDecimal(uint128{lo, hi + qhi*scale + carry}, tail.exponent(), d.negative()), true
}

// reduceGeneral is Reduce's general path for every nonzero carrier.
func reduceGeneral(d Decimal) Decimal {
	v := coefficientViewOf(d)
	k := removableZeros(&v, d.exponent())
	if k == 0 {
		return d
	}
	q, r := int(k/9), uint32(k%9)
	count := reducedLimbCount(&v, q, r)
	exponent := int32(int64(d.exponent()) + int64(k))
	// The result has no more limbs than its stored input; publication copies
	// or hands over a fresh buffer, so no value copy observes a mutation.
	if count <= slowSmallLimbs {
		var scratch [slowSmallLimbs]uint32
		reducedFill(scratch[:count], &v, q, r)
		return publishScratch(scratch[:count], exponent, d.negative())
	}
	limbs := make([]uint32, count)
	reducedFill(limbs, &v, q, r)
	return publishOwned(limbs, exponent, d.negative())
}

// reducedFill writes the reduced coefficient's limbs, least significant
// first, from the cursor that yields them most significant first.
func reducedFill(limbs []uint32, v *coefficientView, q int, r uint32) {
	cursor := newReducedCursor(v, q, r)
	for i := len(limbs) - 1; i >= 0; i-- {
		limbs[i], _ = cursor.next()
	}
}

// Equal reports whether two Decimals have the same numeric value.
func (d Decimal) Equal(other Decimal) bool { return d.Compare(other) == 0 }

// Compare returns -1, 0, or +1 according to numeric order.
func (d Decimal) Compare(other Decimal) int {
	// Two inline operands with one sign and exponent order as their
	// magnitudes, reversed when negative; a zero is unsigned, so this
	// covers a zero against a positive value too.
	if d.meta == other.meta && d.slow == nil && other.slow == nil {
		cmp := inlineCompare(d.words, other.words)
		if d.negative() {
			return -cmp
		}
		return cmp
	}
	return d.compareGeneral(other)
}

// compareSameScaleLimbs orders two trimmed base-10^9 magnitudes.
func compareSameScaleLimbs(a, b []uint32) int {
	if len(a) != len(b) {
		if len(a) < len(b) {
			return -1
		}
		return 1
	}
	for i, v := range slices.Backward(a) {
		if v != b[i] {
			if v < b[i] {
				return -1
			}
			return 1
		}
	}
	return 0
}

// compareGeneral is Compare over every operand pair.
func (d Decimal) compareGeneral(other Decimal) int {
	if d.isZero() {
		if other.isZero() {
			return 0
		}
		if other.negative() {
			return 1
		}
		return -1
	}
	if other.isZero() {
		if d.negative() {
			return -1
		}
		return 1
	}
	if d.negative() != other.negative() {
		if d.negative() {
			return -1
		}
		return 1
	}
	var cmp int
	if d.slow == nil && other.slow == nil {
		cmp = inlineCompareMagnitude(d.words, d.exponent(), other.words, other.exponent())
	} else if d.slow != nil && other.slow != nil && d.exponent() == other.exponent() {
		// Two limb coefficients at one exponent order as their trimmed
		// limbs: by length, then from the top limb down.
		cmp = compareSameScaleLimbs(d.slow.limbs, other.slow.limbs)
	} else {
		a, b := coefficientViewOf(d), coefficientViewOf(other)
		cmp = compareMagnitude(&a, int64(d.exponent()), &b, int64(other.exponent()))
	}
	if d.negative() {
		return -cmp
	}
	return cmp
}

// coefficientView reads either storage band without changing its cohort or
// creating a coefficient-sized copy. Inline conversion uses five limbs max.
type coefficientView struct {
	inline [5]uint32
	slow   []uint32
	count  int
}

func coefficientViewOf(d Decimal) coefficientView {
	var v coefficientView
	v.load(d)
	return v
}

// load sets an empty view to d's coefficient in place, so a caller that
// embeds the view (an addTerm) avoids copying it.
func (v *coefficientView) load(d Decimal) {
	if d.slow != nil {
		v.slow = d.slow.limbs
		v.count = len(v.slow)
		return
	}
	v.count = wordLimbs(&v.inline, d.words.hi, d.words.lo)
}

// wordLimbs writes the base-10^9 limbs of hi·2^64 + lo, least significant
// first, and returns their count: zero for zero, at most five. Below 2^64
// it divides by the constant 10^9, which compiles to a multiply-high; above
// it, at most two hardware divisions by 10^18 split the value into parts
// below 10^18 that constant divisions finish, instead of a 128-bit
// division per limb.
func wordLimbs(out *[5]uint32, hi, lo uint64) int {
	if hi == 0 {
		n := 0
		for ; lo != 0; n++ {
			out[n] = uint32(lo % decimalLimbBase)
			lo /= decimalLimbBase
		}
		return n
	}
	const base = decimalLimbBase * decimalLimbBase // 10^18
	// hi·2^64 + lo = (qhi·2^64 + qlo)·10^18 + low with qhi = ⌊hi/10^18⌋ ≤ 18,
	// then the quotient splits into top·10^18 + middle with top < 341.
	qhi, rem := hi/base, hi%base
	qlo, low := bits.Div64(rem, lo, base)
	var top, middle uint64
	if qhi == 0 {
		top, middle = qlo/base, qlo%base
	} else {
		top, middle = bits.Div64(qhi, qlo, base)
	}
	out[0], out[1] = uint32(low%decimalLimbBase), uint32(low/decimalLimbBase)
	out[2], out[3] = uint32(middle%decimalLimbBase), uint32(middle/decimalLimbBase)
	out[4] = uint32(top)
	n := 5 // hi != 0 makes the value at least 2^64 > 10^19: three limbs or more
	for out[n-1] == 0 {
		n--
	}
	return n
}

func (v *coefficientView) limb(i int) uint32 {
	if v.slow != nil {
		return v.slow[i]
	}
	return v.inline[i]
}

func limbDigits(limb uint32) uint32 {
	if limb < 10 {
		return 1 // common for the top limb of an inline coefficient
	}
	if uint64(limb) >= decimalLimbBase {
		return 10
	}
	// ⌊log10(2)·bitlen⌋ undercounts by at most one; one table compare
	// fixes it without a division chain.
	d := uint32(bits.Len32(limb)) * 1233 >> 12
	if d < uint32(len(decimalPowers)) && limb >= decimalPowers[d] {
		d++
	}
	return d
}

// adjustedExponent is a signed 128-bit e+digits(c)-1.
type adjustedExponent struct {
	hi int64
	lo uint64
}

func adjusted(v *coefficientView, exponent int64) adjustedExponent {
	hi, lo := bits.Mul64(uint64(v.count-1), 9)
	var carry uint64
	lo, carry = bits.Add64(lo, uint64(limbDigits(v.limb(v.count-1))-1), 0)
	hi += carry
	if exponent >= 0 {
		lo, carry = bits.Add64(lo, uint64(exponent), 0)
		hi += carry
	} else {
		var borrow uint64
		lo, borrow = bits.Sub64(lo, uint64(-exponent), 0)
		hi -= borrow
	}
	return adjustedExponent{hi: int64(hi), lo: lo}
}

func compareAdjusted(a, b adjustedExponent) int {
	if a.hi < b.hi || a.hi == b.hi && a.lo < b.lo {
		return -1
	}
	if a.hi > b.hi || a.hi == b.hi && a.lo > b.lo {
		return 1
	}
	return 0
}

type digitCursor struct {
	v         *coefficientView
	limbIndex int
	current   uint32
	divisor   uint32
	remaining uint32
}

func newDigitCursor(v *coefficientView) digitCursor {
	return digitCursor{v: v, limbIndex: v.count - 1}
}

func (c *digitCursor) next() (uint32, bool) {
	if c.remaining == 0 {
		if c.limbIndex < 0 {
			return 0, false
		}
		c.current = c.v.limb(c.limbIndex)
		if c.limbIndex == c.v.count-1 {
			c.remaining = limbDigits(c.current)
		} else {
			c.remaining = 9
		}
		c.divisor = decimalPowers[c.remaining-1]
		c.limbIndex--
	}
	digit := c.current / c.divisor
	c.current %= c.divisor
	c.divisor /= 10
	c.remaining--
	return digit, true
}

func compareMagnitude(a *coefficientView, ae int64, b *coefficientView, be int64) int {
	if cmp := compareAdjusted(adjusted(a, ae), adjusted(b, be)); cmp != 0 {
		return cmp
	}
	// Equal adjusted exponents align both most significant digits. Shift the
	// shorter coefficient virtually to the longer digit length and compare
	// whole base-10^9 groups from the top.
	da, oka := arithmeticDigits(a)
	db, okb := arithmeticDigits(b)
	if oka && okb {
		length := max(da, db)
		for group := (length-1)/9 + 1; group > 0; {
			group--
			x, y := alignedLimb(a, length-da, group), alignedLimb(b, length-db, group)
			if x != y {
				if x < y {
					return -1
				}
				return 1
			}
		}
		return 0
	}
	return compareDigits(a, b)
}

// compareDigits is the digit-cursor comparison for equal adjusted exponents.
// It serves coefficient lengths whose digit count exceeds uint64.
func compareDigits(a, b *coefficientView) int {
	ac, bc := newDigitCursor(a), newDigitCursor(b)
	for {
		ad, aok := ac.next()
		bd, bok := bc.next()
		if !aok && !bok {
			return 0
		}
		if ad < bd {
			return -1
		}
		if ad > bd {
			return 1
		}
	}
}

// saturatedZeroLimbDigits caps a potentially enormous zero-limb run before
// multiplying it by nine.
func saturatedZeroLimbDigits(zeroLimbs, distance uint64) uint64 {
	if zeroLimbs >= (distance+8)/9 {
		return distance
	}
	return zeroLimbs * 9
}

func removableZeros(v *coefficientView, exponent int32) uint64 {
	distance := uint64(int64(math.MaxInt32) - int64(exponent))
	if distance == 0 {
		return 0
	}
	limit := (distance + 8) / 9
	var lowZeros uint64
	for lowZeros < limit && lowZeros < uint64(v.count) && v.limb(int(lowZeros)) == 0 {
		lowZeros++
	}
	k := saturatedZeroLimbDigits(lowZeros, distance)
	if k == distance {
		return k
	}
	limb := v.limb(int(lowZeros)) // nonzero by the carrier invariant
	for k < distance && limb%10 == 0 {
		limb /= 10
		k++
	}
	return k
}

func reducedLimbCount(v *coefficientView, q int, r uint32) int {
	count := v.count - q
	if r != 0 && v.limb(v.count-1) < decimalPowers[r] {
		count--
	}
	return count
}

type reducedCursor struct {
	v         *coefficientView
	index     int
	floor     int
	divisor   uint64
	remainder uint64
	skipTop   bool
}

func newReducedCursor(v *coefficientView, q int, r uint32) reducedCursor {
	divisor := uint64(1)
	if r != 0 {
		divisor = uint64(decimalPowers[r])
	}
	return reducedCursor{v: v, index: v.count - 1, floor: q, divisor: divisor,
		skipTop: r != 0 && v.limb(v.count-1) < uint32(divisor)}
}

func (c *reducedCursor) next() (uint32, bool) {
	for c.index >= c.floor {
		index := c.index
		c.index--
		if c.divisor == 1 {
			return c.v.limb(index), true
		}
		numerator := c.remainder*decimalLimbBase + uint64(c.v.limb(index))
		quotient := uint32(numerator / c.divisor)
		c.remainder = numerator % c.divisor
		if c.skipTop && index == c.v.count-1 {
			continue
		}
		return quotient, true
	}
	return 0, false
}
