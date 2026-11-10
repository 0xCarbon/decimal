// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"math"
	"math/bits"
	"slices"
)

// Add returns the exact sum at the minimum operand exponent, or Decimal{}
// with a checked resource error. It uses no caller quota and never rounds.
func (d Decimal) Add(other Decimal) (Decimal, error) {
	result, _, err := d.addSubExact(other, exactLimbs)
	return result, err
}

// Sub returns the exact difference at the minimum operand exponent, or
// Decimal{} with a checked resource error. Exact zero is unsigned.
func (d Decimal) Sub(other Decimal) (Decimal, error) {
	result, _, err := d.addSubExact(other, exactLimbs|exactSubtract)
	return result, err
}

// Mul returns the exact product at the checked exponent sum. An out-of-int32
// sum returns Decimal{} and ErrExponentRange, including for a zero operand.
// Checked resource refusal returns Decimal{} and ErrInsufficientStorage.
func (d Decimal) Mul(other Decimal) (Decimal, error) {
	result, _, err := d.mulExact(other, exactLimbs)
	return result, err
}

// exactMode configures the unbudgeted exact dispatchers addSubExact and
// mulExact. One mode byte instead of a budget, an operation name and a
// flag keeps the two operands and the mode within the nine integer
// argument registers.
type exactMode uint8

const (
	// exactSubtract negates the second Add/Sub operand.
	exactSubtract exactMode = 1 << iota
	// exactLimbs continues a declined inline path on the unbudgeted limb
	// path, as the public Add, Sub and Mul do; without it the dispatcher
	// is the inline-only fast path the context and FMA kernels consult.
	exactLimbs
)

// addSubMode is the inline-only Add/Sub mode of a subtract flag.
func addSubMode(subtract bool) exactMode {
	if subtract {
		return exactSubtract
	}
	return 0
}

// addSubExact is the single unbudgeted Add/Sub fast path. For
// two inline operands whose aligned magnitudes and sum stay below 2^128 it
// returns the exact sum at the minimum exponent and true; zero is unsigned.
// Otherwise, under exactLimbs, it returns the limb path's result and error
// and true, and else Decimal{}, false. The inline sum equals the limb path:
//   - A one-word shift of at most 19 digits, every shift of a cent-scale
//     aggregate, is one multiply here; wider shifts go to addSubWide.
//   - Opposite signs subtract with a borrow and negate on underflow
//     instead of comparing first: the magnitude |a-b| and the sign of the
//     larger term are those of the compare-then-subtract form.
//   - Every decline is a tail call on the original operands, so the
//     inline sum makes no call it resumes after.
func (d Decimal) addSubExact(other Decimal, mode exactMode) (Decimal, bool, error) {
	if d.slow != nil || other.slow != nil {
		return d.addSubDeclined(other, mode)
	}
	a, b := d.words, other.words
	ae, e := d.exponent(), other.exponent()
	sign := d.meta & decimalSignBit
	bSign := other.meta & decimalSignBit
	if mode&exactSubtract != 0 {
		bSign ^= decimalSignBit
	}
	if ae > e {
		k := uint64(int64(ae) - int64(e))
		if a.hi != 0 || k >= uint64(len(pow10Words)) {
			return d.addSubWide(other, mode)
		}
		a.hi, a.lo = bits.Mul64(a.lo, pow10Words[k])
	} else if ae < e {
		k := uint64(int64(e) - int64(ae))
		if b.hi != 0 || k >= uint64(len(pow10Words)) {
			return d.addSubWide(other, mode)
		}
		b.hi, b.lo = bits.Mul64(b.lo, pow10Words[k])
		e = ae
	}
	var sum uint128
	if sign == bSign {
		var carry uint64
		sum.lo, carry = bits.Add64(a.lo, b.lo, 0)
		sum.hi, carry = bits.Add64(a.hi, b.hi, carry)
		if carry != 0 {
			return d.addSubDeclined(other, mode)
		}
	} else {
		var borrow uint64
		sum.lo, borrow = bits.Sub64(a.lo, b.lo, 0)
		sum.hi, borrow = bits.Sub64(a.hi, b.hi, borrow)
		if borrow != 0 {
			// b > a: the two's-complement negation is the magnitude b-a.
			sum.lo, borrow = bits.Sub64(0, sum.lo, 0)
			sum.hi, _ = bits.Sub64(0, sum.hi, borrow)
			sign = bSign
		}
	}
	if sum.lo|sum.hi == 0 {
		sign = 0
	}
	return Decimal{words: sum, meta: signExponent(uint32(e)) | sign}, true, nil
}

// addSubWide is addSubExact's out-of-line wide alignment: it scales the
// operand with the larger exponent to the smaller one by inlineScale and
// sums the equal-exponent pair, whose exact value and exponent are those
// of the original pair. A declined scale or sum defers the original pair.
func (d Decimal) addSubWide(other Decimal, mode exactMode) (Decimal, bool, error) {
	x, y := d, other
	ok := false
	if xe, ye := x.exponent(), y.exponent(); xe > ye {
		x.words, ok = inlineScale(x.words, uint64(int64(xe)-int64(ye)))
		x = x.withExponent(ye)
	} else {
		y.words, ok = inlineScale(y.words, uint64(int64(ye)-int64(xe)))
		y = y.withExponent(xe)
	}
	if ok {
		if result, ok, _ := x.addSubExact(y, mode&^exactLimbs); ok {
			return result, true, nil
		}
	}
	return d.addSubDeclined(other, mode)
}

// addSubDeclined is addSubExact's out-of-line decline: the public Add/Sub
// limb path under exactLimbs, so the inline sum does not set up its frame.
func (d Decimal) addSubDeclined(other Decimal, mode exactMode) (Decimal, bool, error) {
	if mode&exactLimbs == 0 {
		return Decimal{}, false, nil
	}
	op, subtract := "Add", mode&exactSubtract != 0
	if subtract {
		op = "Sub"
	}
	result, err := d.addSubLimbs(other, limits{}, op, subtract)
	return result, true, err
}

// mulExact is the single unbudgeted Mul fast path, shaped as addSubExact.
// For two inline operands with an int32 exponent sum and a
// product below 2^128 it returns the exact product and true; zero is
// unsigned. Otherwise, under exactLimbs, it returns Mul's result and error
// and true, and else Decimal{}, false.
func (d Decimal) mulExact(other Decimal, mode exactMode) (Decimal, bool, error) {
	e := int64(d.exponent()) + int64(other.exponent())
	if e < math.MinInt32 || e > math.MaxInt32 || d.slow != nil || other.slow != nil {
		return d.mulDeclined(other, mode)
	}
	a, b := d.words, other.words
	high, low := bits.Mul64(a.lo, b.lo)
	if a.hi|b.hi != 0 {
		// One factor is wider than a word: both cross products must stay
		// in one word and their sum in the high word.
		if a.hi != 0 && b.hi != 0 {
			return d.mulDeclined(other, mode)
		}
		crossA, lowA := bits.Mul64(a.hi, b.lo)
		crossB, lowB := bits.Mul64(a.lo, b.hi)
		var c1, c2 uint64
		high, c1 = bits.Add64(high, lowA, 0)
		high, c2 = bits.Add64(high, lowB, 0)
		if crossA|crossB|c1|c2 != 0 {
			return d.mulDeclined(other, mode)
		}
	}
	sign := (d.meta ^ other.meta) & decimalSignBit
	if low|high == 0 {
		sign = 0
	}
	return Decimal{words: uint128{low, high}, meta: signExponent(uint32(e)) | sign}, true, nil
}

// mulDeclined is mulExact's out-of-line decline: under exactLimbs, Mul's
// exponent check and then its limb path.
func (d Decimal) mulDeclined(other Decimal, mode exactMode) (Decimal, bool, error) {
	if mode&exactLimbs == 0 {
		return Decimal{}, false, nil
	}
	e := int64(d.exponent()) + int64(other.exponent())
	if e < math.MinInt32 || e > math.MaxInt32 {
		result, err := arithmeticFailure("Mul", ErrExponentRange)
		return result, true, err
	}
	result, err := d.multiplyLimbs(other, limits{}, "Mul", int32(e))
	return result, true, err
}

func arithmeticFailure(op string, code ErrorCode) (Decimal, error) {
	return Decimal{}, newError(op, code)
}

func arithmeticAdd(a, b uint64) (uint64, bool) {
	s, carry := bits.Add64(a, b, 0)
	return s, carry == 0
}
func arithmeticMul(a, b uint64) (uint64, bool) {
	hi, lo := bits.Mul64(a, b)
	return lo, hi == 0
}
func admitted(limit, amount uint64, ok bool) bool {
	return limit == 0 || ok && amount <= limit
}
func arithmeticDigits(v *coefficientView) (uint64, bool) {
	if v.count == 0 {
		return 1, true
	}
	base, ok := arithmeticMul(uint64(v.count-1), 9)
	if !ok {
		return 0, false
	}
	return arithmeticAdd(base, uint64(limbDigits(v.limb(v.count-1))))
}

// mulWorkCharge uses logical nine-digit tiles. digits is the checked sum of
// the two positive coefficient digit lengths, already used for result quota.
func mulWorkCharge(d1, d2, digits uint64) (uint64, bool) {
	if d1 == 0 || d2 == 0 {
		return 0, false
	}
	pairs, ok := arithmeticMul(1+(d1-1)/9, 1+(d2-1)/9)
	if !ok {
		return 0, false
	}
	return arithmeticAdd(pairs, digits)
}

// digitLimbs is 1+(d−1)/9, the base-10^9 limbs of a d-digit coefficient,
// for d ≥ 1.
func digitLimbs(d uint64) uint64 { return 1 + (d-1)/9 }

// arithmeticPhysicalLimbCount is the shared Add/Sub/Mul checked allocation
// preflight. It exposes the same typed identity as the public refusal path.
func arithmeticPhysicalLimbCount(limbs uint64, op string) (int, error) {
	if limbs == 0 || limbs > uint64(math.MaxInt)/4 {
		return 0, newError(op, ErrInsufficientStorage)
	}
	return int(limbs), nil
}
func arithmeticLimbCount(digits uint64, op string) (int, error) {
	if digits == 0 {
		return 0, newError(op, ErrInsufficientStorage)
	}
	limbs := 1 + (digits-1)/9
	return arithmeticPhysicalLimbCount(limbs, op)
}

// additionNeedsCarry scans virtual aligned base-10^9 groups high to low.
// A group sum below base-1 kills a lower carry, above base-1 generates one,
// and equal to base-1 propagates it. The top group's base uses its actual
// decimal width; the incoming carry at the lowest group is zero.
func additionNeedsCarry(a *coefficientView, sa uint64, b *coefficientView, sb uint64, length uint64) bool {
	if length == 0 {
		return false
	}
	top := (length - 1) / 9
	topWidth := 1 + (length-1)%9
	topBase := decimalLimbBase
	if topWidth < 9 {
		topBase = uint64(decimalPowers[topWidth])
	}
	for group := top + 1; group > 0; {
		group--
		base := decimalLimbBase
		if group == top {
			base = topBase
		}
		sum := uint64(alignedLimb(a, sa, group)) + uint64(alignedLimb(b, sb, group))
		if sum != base-1 {
			return sum >= base
		}
	}
	return false
}

// alignedLimb reads one base-10^9 limb of a virtually shifted coefficient.
// Both source reads are bounded before their indexes are converted to int.
func alignedLimb(v *coefficientView, shift, index uint64) uint32 {
	whole, rem := shift/9, shift%9
	if index < whole {
		return 0
	}
	j := index - whole
	if rem == 0 {
		if j < uint64(v.count) {
			return v.limb(int(j))
		}
		return 0
	}
	var low, high uint64
	if j < uint64(v.count) {
		low = uint64(v.limb(int(j))) * uint64(decimalPowers[rem]) % decimalLimbBase
	}
	if j > 0 && j-1 < uint64(v.count) {
		high = uint64(v.limb(int(j-1))) / uint64(decimalPowers[9-rem])
	}
	return uint32(low + high)
}

// The Add/Sub work charges, shared by addSubLimbs and the
// estimators: opposite signs precharge the magnitude compare
// d1+d2, then charge 2(d1+d2)+L; same signs charge d1+d2+L+1.
func addSubCompareCharge(da, db uint64) (uint64, bool) { return arithmeticAdd(da, db) }

func addSubOppositeCharge(da, db, L uint64) (uint64, bool) {
	comparison, ok1 := arithmeticAdd(da, db)
	twice, ok2 := arithmeticMul(comparison, 2)
	work, ok3 := arithmeticAdd(twice, L)
	return work, ok1 && ok2 && ok3
}

func addSubSameCharge(da, db, L uint64) (uint64, bool) {
	inputs, ok1 := arithmeticAdd(da, db)
	planned, ok2 := arithmeticAdd(L, 1)
	work, ok3 := arithmeticAdd(inputs, planned)
	return work, ok1 && ok2 && ok3
}

// addSub is the budgeted Add/Sub kernel of the context and FMA paths; a
// call whose budget admits the inline bounds first tries the inline sum.
func (d Decimal) addSub(other Decimal, budget limits, op string, subtract bool) (Decimal, error) {
	if budget.admits(inlineAddSubDigits, inlineAddSubWork) {
		if result, ok := inlineAddSub(d, other, subtract); ok {
			return result, nil
		}
	}
	return d.addSubLimbs(other, budget, op, subtract)
}

// addSubLimbs is the general aligned base-10^9 path. It owns every budget
// charge and refusal; the inline path serves only calls it would admit.
func (d Decimal) addSubLimbs(other Decimal, budget limits, op string, subtract bool) (Decimal, error) {
	e := min(d.exponent(), other.exponent())
	a, b := coefficientViewOf(d), coefficientViewOf(other)
	aZero, bZero := a.count == 0, b.count == 0
	if aZero && bZero {
		if !admitted(budget.MaxDigits, 1, true) || !admitted(budget.MaxWork, 1, true) {
			return arithmeticFailure(op, ErrInsufficientStorage)
		}
		return zeroDecimal(e), nil
	}
	da, oka := arithmeticDigits(&a)
	db, okb := arithmeticDigits(&b)
	if !oka || !okb {
		return arithmeticFailure(op, ErrInsufficientStorage)
	}
	sa := uint64(int64(d.exponent()) - int64(e))
	sb := uint64(int64(other.exponent()) - int64(e))
	spanA, spanB := uint64(0), uint64(0)
	var ok bool
	if !aZero {
		spanA, ok = arithmeticAdd(da, sa)
		if !ok {
			return arithmeticFailure(op, ErrInsufficientStorage)
		}
	}
	if !bZero {
		spanB, ok = arithmeticAdd(db, sb)
		if !ok {
			return arithmeticFailure(op, ErrInsufficientStorage)
		}
	}
	L := max(spanA, spanB)
	bSign := other.negative()
	if subtract && !bZero {
		bSign = !bSign
	}
	negative := d.negative()
	add := d.negative() == bSign
	greaterA := true
	if aZero != bZero {
		add = true // copy the sole nonzero magnitude, perhaps shifted
		negative = d.negative()
		if aZero {
			negative = bSign
		}
		if !admitted(budget.MaxWork, L, true) {
			return arithmeticFailure(op, ErrInsufficientStorage)
		}
	} else if !add {
		comparison, valid := addSubCompareCharge(da, db)
		if !admitted(budget.MaxWork, comparison, valid) {
			return arithmeticFailure(op, ErrInsufficientStorage)
		}
		cmp := compareMagnitude(&a, int64(d.exponent()), &b, int64(other.exponent()))
		if cmp == 0 {
			if !admitted(budget.MaxDigits, 1, true) {
				return arithmeticFailure(op, ErrInsufficientStorage)
			}
			return zeroDecimal(e), nil
		}
		greaterA = cmp > 0
		if !greaterA {
			negative = bSign
		}
		if budget.MaxWork != 0 {
			work, ok := addSubOppositeCharge(da, db, L)
			if !admitted(budget.MaxWork, work, ok) {
				return arithmeticFailure(op, ErrInsufficientStorage)
			}
		}
	} else {
		planned, ok := arithmeticAdd(L, 1)
		if !ok {
			return arithmeticFailure(op, ErrInsufficientStorage)
		}
		if budget.MaxWork != 0 {
			work, ok := addSubSameCharge(da, db, L)
			if !admitted(budget.MaxWork, work, ok) {
				return arithmeticFailure(op, ErrInsufficientStorage)
			}
		}
		if budget.MaxDigits == L {
			if additionNeedsCarry(&a, sa, &b, sb, L) {
				return arithmeticFailure(op, ErrInsufficientStorage)
			}
		} else if budget.MaxDigits == 0 || budget.MaxDigits > L {
			L = planned
		}
	}
	if !admitted(budget.MaxDigits, L, true) {
		return arithmeticFailure(op, ErrInsufficientStorage)
	}
	count, err := arithmeticLimbCount(L, op)
	if err != nil {
		return Decimal{}, err
	}
	if aZero != bZero {
		if aZero && sb == 0 {
			result := other
			result = result.withNegative(bSign)
			return result, nil
		}
		if bZero && sa == 0 {
			return d, nil
		}
	}
	if L <= 38 {
		var inline [5]uint32
		out := inline[:count]
		fillAddSub(out, &a, sa, &b, sb, add, greaterA)
		return publishInlineArithmetic(out, e, negative), nil
	}
	// The plan reserves a carry limb, so an 81-digit result may need
	// slowSmallLimbs+1 limbs of scratch before publishScratch trims it.
	if count <= slowSmallLimbs+1 {
		var scratch [slowSmallLimbs + 1]uint32
		out := scratch[:count]
		fillAddSub(out, &a, sa, &b, sb, add, greaterA)
		return publishScratch(out, e, negative), nil
	}
	out := make([]uint32, count)
	fillAddSub(out, &a, sa, &b, sb, add, greaterA)
	return publishOwned(out, e, negative), nil
}

// addTerm is one Add/Sub operand as the aligned kernels read it: a
// coefficient view at an int64 exponent, with the sign it enters the sum
// with (Sub's nonzero second operand already negated). digits is its plan
// digit count: the exact count for a Decimal, and the dx+dy envelope for
// FMA's unpublished product; a zero plans one digit.
type addTerm struct {
	v        coefficientView
	exponent int64
	digits   uint64
	negative bool
	zero     bool
}

// load sets an empty term to d, negated when negate is set and d is
// nonzero, in place. It reports false when the digit count leaves uint64.
func (t *addTerm) load(d Decimal, negate bool) bool {
	t.v.load(d)
	t.exponent, t.negative, t.zero = int64(d.exponent()), d.negative(), t.v.count == 0
	if negate && !t.zero {
		t.negative = !t.negative
	}
	var valid bool
	t.digits, valid = arithmeticDigits(&t.v)
	return valid
}

// addSubPlan is addSubLimbs's plan in term form, for FMA's unpublished
// product: the aligned spans, the path, and the work already
// admitted. addSubAdmit and addSubFinish follow addSubLimbs's paths,
// charges and refusals exactly (TestAddSubStagesMatchAddKernel pins
// them). The Decimal kernel keeps its inline form, which avoids building
// terms on its limb path.
type addSubPlan struct {
	e              int64
	sa, sb, L      uint64
	pre            uint64 // work charged before the sum (FMA's Mul charge)
	add, negative  bool
	zero, opposite bool
	scan           bool
	count          int // result limbs, once admitted
}

// addSelf names an operand a bare sum returns unchanged (the other is
// zero and no shift applies), so a published operand is returned without
// a copy and a scratch one is published.
type addSelf uint8

const (
	addSelfNone addSelf = iota
	addSelfA
	addSelfB
)

// addSubAdmit plans a bare Add/Sub and makes every refusal the operand
// shapes decide, before either coefficient is read. Every work check adds
// pre, the work the caller has already admitted. Only the opposite-sign
// comparison and the exact carry scan remain for addSubFinish, so FMA can
// build its product between the two stages.
func addSubAdmit(a, b *addTerm, budget limits, pre uint64, op string) (addSubPlan, error) {
	p := addSubPlan{e: min(a.exponent, b.exponent), pre: pre}
	if a.zero && b.zero {
		work, valid := arithmeticAdd(pre, 1)
		if !admitted(budget.MaxDigits, 1, true) || !admitted(budget.MaxWork, work, valid) {
			return p, newError(op, ErrInsufficientStorage)
		}
		p.zero = true
		return p, nil
	}
	p.sa = uint64(a.exponent - p.e)
	p.sb = uint64(b.exponent - p.e)
	var spanA, spanB uint64
	var valid bool
	if !a.zero {
		if spanA, valid = arithmeticAdd(a.digits, p.sa); !valid {
			return p, newError(op, ErrInsufficientStorage)
		}
	}
	if !b.zero {
		if spanB, valid = arithmeticAdd(b.digits, p.sb); !valid {
			return p, newError(op, ErrInsufficientStorage)
		}
	}
	p.L = max(spanA, spanB)
	p.negative = a.negative
	p.add = a.negative == b.negative
	switch {
	case a.zero != b.zero:
		p.add = true // copy the sole nonzero magnitude, perhaps shifted
		if a.zero {
			p.negative = b.negative
		}
		work, valid := arithmeticAdd(pre, p.L)
		if !admitted(budget.MaxWork, work, valid) {
			return p, newError(op, ErrInsufficientStorage)
		}
	case !p.add:
		p.opposite = true
		comparison, valid1 := addSubCompareCharge(a.digits, b.digits)
		work, valid2 := arithmeticAdd(pre, comparison)
		if !admitted(budget.MaxWork, work, valid1 && valid2) {
			return p, newError(op, ErrInsufficientStorage)
		}
		return p, nil
	default:
		planned, valid := arithmeticAdd(p.L, 1)
		if !valid {
			return p, newError(op, ErrInsufficientStorage)
		}
		if budget.MaxWork != 0 {
			charge, valid1 := addSubSameCharge(a.digits, b.digits, p.L)
			work, valid2 := arithmeticAdd(pre, charge)
			if !admitted(budget.MaxWork, work, valid1 && valid2) {
				return p, newError(op, ErrInsufficientStorage)
			}
		}
		if budget.MaxDigits == p.L {
			p.scan = true
		} else if budget.MaxDigits == 0 || budget.MaxDigits > p.L {
			p.L = planned
		}
	}
	if !admitted(budget.MaxDigits, p.L, true) {
		return p, newError(op, ErrInsufficientStorage)
	}
	var err error
	p.count, err = arithmeticLimbCount(p.L, op)
	return p, err
}

// unchanged reports the operand an admitted sum returns unchanged, a
// shape-level decision the caller takes before addSubFinish.
func (p *addSubPlan) unchanged(a, b *addTerm) addSelf {
	switch {
	case p.zero || a.zero == b.zero:
		return addSelfNone
	case a.zero && p.sb == 0:
		return addSelfB
	case b.zero && p.sa == 0:
		return addSelfA
	}
	return addSelfNone
}

// addSubFinish completes an admitted plan over the terms' coefficients: the
// opposite-sign comparison and its charge, the exact carry scan, and the
// one result buffer. The caller has handled an unchanged operand.
func addSubFinish(p *addSubPlan, a, b *addTerm, budget limits, op string) (Decimal, error) {
	if p.zero {
		return zeroDecimal(int32(p.e)), nil
	}
	greaterA := true
	if p.opposite {
		cmp := compareMagnitude(&a.v, a.exponent, &b.v, b.exponent)
		if cmp == 0 {
			if !admitted(budget.MaxDigits, 1, true) {
				return Decimal{}, newError(op, ErrInsufficientStorage)
			}
			return zeroDecimal(int32(p.e)), nil
		}
		greaterA = cmp > 0
		if !greaterA {
			p.negative = b.negative
		}
		if budget.MaxWork != 0 {
			charge, valid1 := addSubOppositeCharge(a.digits, b.digits, p.L)
			work, valid2 := arithmeticAdd(p.pre, charge)
			if !admitted(budget.MaxWork, work, valid1 && valid2) {
				return Decimal{}, newError(op, ErrInsufficientStorage)
			}
		}
		if !admitted(budget.MaxDigits, p.L, true) {
			return Decimal{}, newError(op, ErrInsufficientStorage)
		}
	}
	if p.scan && additionNeedsCarry(&a.v, p.sa, &b.v, p.sb, p.L) {
		return Decimal{}, newError(op, ErrInsufficientStorage)
	}
	count := p.count
	if p.opposite {
		var err error
		if count, err = arithmeticLimbCount(p.L, op); err != nil {
			return Decimal{}, err
		}
	}
	e := int32(p.e)
	if p.L <= 38 {
		var inline [5]uint32
		out := inline[:count]
		fillAddSub(out, &a.v, p.sa, &b.v, p.sb, p.add, greaterA)
		return publishInlineArithmetic(out, e, p.negative), nil
	}
	// The plan reserves a carry limb, so an 81-digit result may need
	// slowSmallLimbs+1 limbs of scratch before publishScratch trims it.
	if count <= slowSmallLimbs+1 {
		var scratch [slowSmallLimbs + 1]uint32
		out := scratch[:count]
		fillAddSub(out, &a.v, p.sa, &b.v, p.sb, p.add, greaterA)
		return publishScratch(out, e, p.negative), nil
	}
	out := make([]uint32, count)
	fillAddSub(out, &a.v, p.sa, &b.v, p.sb, p.add, greaterA)
	return publishOwned(out, e, p.negative), nil
}

func fillAddSub(out []uint32, a *coefficientView, sa uint64, b *coefficientView, sb uint64, add, greaterA bool) {
	var carry uint64
	for i := range out {
		ad := uint64(alignedLimb(a, sa, uint64(i)))
		bd := uint64(alignedLimb(b, sb, uint64(i)))
		if add {
			sum := ad + bd + carry
			out[i] = uint32(sum % decimalLimbBase)
			carry = sum / decimalLimbBase
			continue
		}
		high, low := ad, bd
		if !greaterA {
			high, low = low, high
		}
		if high < low+carry {
			out[i] = uint32(high + decimalLimbBase - low - carry)
			carry = 1
		} else {
			out[i] = uint32(high - low - carry)
			carry = 0
		}
	}
}

func (d Decimal) multiply(other Decimal, budget limits, op string) (Decimal, error) {
	e := int64(d.exponent()) + int64(other.exponent())
	if e < math.MinInt32 || e > math.MaxInt32 {
		return arithmeticFailure(op, ErrExponentRange)
	}
	if budget.MaxDigits|budget.MaxWork == 0 || d.slow == nil && other.slow == nil && inlineMulAdmitted(d, other, budget, 0) {
		if result, ok := inlineMul(d, other); ok {
			return result, nil
		}
	}
	return d.multiplyLimbs(other, budget, op, int32(e))
}

// multiplyLimbs is the general schoolbook path after exponent validation.
func (d Decimal) multiplyLimbs(other Decimal, budget limits, op string, exponent int32) (Decimal, error) {
	e := int64(exponent)
	a, b := coefficientViewOf(d), coefficientViewOf(other)
	if a.count == 0 || b.count == 0 {
		if !admitted(budget.MaxDigits, 1, true) || !admitted(budget.MaxWork, 1, true) {
			return arithmeticFailure(op, ErrInsufficientStorage)
		}
		return zeroDecimal(int32(e)), nil
	}
	da, oka := arithmeticDigits(&a)
	db, okb := arithmeticDigits(&b)
	if !oka || !okb {
		return arithmeticFailure(op, ErrInsufficientStorage)
	}
	digits, ok := arithmeticAdd(da, db)
	if !ok || !admitted(budget.MaxDigits, digits, true) {
		return arithmeticFailure(op, ErrInsufficientStorage)
	}
	if budget.MaxWork != 0 {
		work, ok := mulWorkCharge(da, db, digits)
		if !admitted(budget.MaxWork, work, ok) {
			return arithmeticFailure(op, ErrInsufficientStorage)
		}
	}
	// A full n+m limb output buffer avoids an extra scratch limb during
	// carry propagation. The last limb may be zero when the logical digit
	// envelope packs into fewer limbs; quota admission remains digit-based.
	physical, ok := arithmeticAdd(uint64(a.count), uint64(b.count))
	if !ok {
		return arithmeticFailure(op, ErrInsufficientStorage)
	}
	count, err := arithmeticPhysicalLimbCount(physical, op)
	if err != nil {
		return Decimal{}, err
	}
	if digits <= 38 {
		var inline [6]uint32
		out := inline[:count]
		if !fillMultiply(out, &a, &b) {
			return arithmeticFailure(op, ErrInsufficientStorage)
		}
		return publishInlineArithmetic(out, int32(e), d.negative() != other.negative()), nil
	}
	if count <= slowSmallLimbs+1 {
		var scratch [slowSmallLimbs + 1]uint32
		out := scratch[:count]
		if !fillMultiply(out, &a, &b) {
			return arithmeticFailure(op, ErrInsufficientStorage)
		}
		return publishScratch(out, int32(e), d.negative() != other.negative()), nil
	}
	out := make([]uint32, count)
	if !fillMultiply(out, &a, &b) {
		return arithmeticFailure(op, ErrInsufficientStorage)
	}
	return publishOwned(out, int32(e), d.negative() != other.negative()), nil
}

// publishInlineArithmetic accepts at most 38 logical digits, which always
// fit the unsigned 128-bit inline words; its caller's array stays on stack.
func publishInlineArithmetic(limbs []uint32, exponent int32, negative bool) Decimal {
	for len(limbs) > 0 && limbs[len(limbs)-1] == 0 {
		limbs = limbs[:len(limbs)-1]
	}
	if len(limbs) == 0 {
		return zeroDecimal(exponent)
	}
	var words uint128
	for _, limb := range slices.Backward(limbs) {
		carry, low := bits.Mul64(words.lo, decimalLimbBase)
		_, high := bits.Mul64(words.hi, decimalLimbBase)
		low, lowCarry := bits.Add64(low, uint64(limb), 0)
		high, _ = bits.Add64(high, carry, lowCarry)
		words = uint128{low, high}
	}
	return inlineDecimal(words, exponent, negative)
}
