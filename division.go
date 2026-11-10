// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"math"
	"math/bits"
	"runtime"
	"slices"
)

// Division design: one exact-source kernel produces the truncated coefficient at a chosen
// exponent plus the half class of the discarded part, and one finisher
// applies the mode, guards, conditions, resources and traps.

const divRemedy = "non-terminating quotient: supply a finite-precision context (DivWithContext) or an explicit exponent (DivToExponent)"

// Div returns the exact quotient at the ideal exponent (the dividend's
// exponent minus the divisor's), or the nearest exponent below it that
// holds a terminating quotient: 2.400/2.0 is 1.20 and 1/4 is 0.25. A
// non-terminating quotient such as 1/3 returns a *Error with
// Condition Inexact and a remedy, never a silently chosen scale. A zero
// divisor returns ErrDivisionByZero, or ErrDivisionUndefined for 0/0.
func (d Decimal) Div(other Decimal) (Decimal, error) {
	return d.divExact(other, limits{}, "Div")
}

// DivWithContext rounds the exact quotient once to the context precision
// under its mode, guards and traps. An exact quotient keeps the exponent
// closest to the ideal exponent that fits the precision. A context with
// unlimited precision behaves as Div.
func (d Decimal) DivWithContext(other Decimal, ctx Context) (Decimal, Conditions, error) {
	return d.divContext(other, ctx, ctx.arith, "DivWithContext")
}

// DivToExponent rounds the exact quotient once to exactly targetExponent
// under mode, with unlimited precision and no guards or traps. It is not
// DivWithContext followed by Quantize, which could round twice.
func (d Decimal) DivToExponent(other Decimal, targetExponent int32, mode RoundingMode) (Decimal, Conditions, error) {
	return d.divToExponent(other, targetExponent, mode, limits{}, "DivToExponent")
}

// DivToExponentWithBudget is DivToExponent with checked quotas.
func (d Decimal) DivToExponentWithBudget(other Decimal, targetExponent int32, mode RoundingMode, budget Budget) (Decimal, Conditions, error) {
	return d.divToExponent(other, targetExponent, mode, budget.arith(), "DivToExponentWithBudget")
}

// divHalf classifies the discarded part of a truncated quotient against
// half a unit of the retained last place.
type divHalf uint8

const (
	divExactClass divHalf = iota
	divBelow
	divHalfClass
	divAbove
)

// guardSticky maps a half class onto contextRoundUp's inputs, which makes
// every mode round exactly as the context arithmetic does.
func (c divHalf) guardSticky() (uint32, bool) {
	switch c {
	case divBelow:
		return 1, true
	case divHalfClass:
		return 5, false
	case divAbove:
		return 6, false
	default:
		return 0, false
	}
}

// divCount records kernel work units for the tariff tests. Production calls
// pass nil; the kernel never keeps package state.
type divCount struct{ units uint64 }

func (c *divCount) add(n uint64) {
	if c != nil {
		c.units += n
	}
}

// divSource is the exact quotient x/y of two nonzero coefficients scaled by
// 10^ideal.
type divSource struct {
	x, y     coefficientView
	dx, dy   uint64
	ideal    int64
	negative bool
}

func newDivSource(d, other Decimal) divSource {
	s := divSource{x: coefficientViewOf(d), y: coefficientViewOf(other)}
	s.dx, _ = arithmeticDigits(&s.x)
	s.dy, _ = arithmeticDigits(&s.y)
	s.ideal = int64(d.exponent()) - int64(other.exponent())
	s.negative = d.negative() != other.negative()
	return s
}

// divPath names the kernel path for exponent t.
type divPath uint8

const (
	divTiny   divPath = iota // R = 0, below half, no division
	divHZero                 // k < 0 with no high part: R = 0, class from L = Cx
	divDivide                // long division of an dn-digit numerator
)

type divPlan struct {
	path   divPath
	k      int64  // ideal - t
	dn     uint64 // numerator digits for divDivide
	reads  uint64 // r = dx + max(k,0)
	charge uint64 // B
	ok     bool   // B computed without overflow
}

// plan classifies the path for target exponent t and computes the
// precharge B.
// divUnlimitedTarget is the exact Div's division exponent t = ideal − kMax,
// kMax = ⌈3.322·dy⌉ fractional digits (enough for any terminating
// quotient), or the refusal code; shared with the estimators.
func divUnlimitedTarget(dy uint64, ideal int64) (t int64, kMax uint64, code ErrorCode) {
	kMax, ok := arithmeticMul(dy, 3322)
	if !ok {
		return 0, 0, ErrInsufficientStorage
	}
	kMax = (kMax + 999) / 1000
	if ideal < math.MinInt32 || kMax > uint64(math.MaxInt64/2) || ideal-int64(kMax) > math.MaxInt32 {
		return 0, 0, ErrExponentRange
	}
	return ideal - int64(kMax), kMax, 0
}

// divContextTarget is the context division exponent t′ = (dx−dy)+ideal−p,
// which leaves p or p+1 digits, raised to Etiny under guards.
func divContextTarget(dx, dy uint64, ideal int64, ctx Context) (tPrime, etiny int64) {
	precision := int64(ctx.precision)
	tPrime = int64(dx) - int64(dy) + ideal - precision
	if ctx.guarded {
		etiny = int64(ctx.guards.Emin) - (precision - 1)
		tPrime = max(tPrime, etiny)
	}
	return tPrime, etiny
}

func (s *divSource) plan(t int64) divPlan {
	var p divPlan
	k, ok := subInt64(s.ideal, t)
	if !ok {
		return p
	}
	p.k = k
	lower := min(1+(s.dx-1)/9, 1+(s.dy-1)/9)
	// Tiny shortcut: dx + k <= dy - 2.
	if k < 0 && k != math.MinInt64 && s.dx+2 <= s.dy+uint64(-k) || k >= 0 && s.dx+uint64(k)+2 <= s.dy {
		p.path, p.charge, p.ok = divTiny, lower+1, true
		return p
	}
	if k < 0 && uint64(-k) >= s.dx {
		p.path = divHZero
		p.reads = s.dx
		p.charge, p.ok = checkedSum(p.reads, s.dy, lower)
		return p
	}
	p.path = divDivide
	if k >= 0 {
		p.dn, ok = arithmeticAdd(s.dx, uint64(k))
		if !ok {
			return p
		}
		p.reads = p.dn
	} else {
		p.dn = s.dx - uint64(-k)
		p.reads = s.dx
	}
	tn, n := 1+(p.dn-1)/9, 1+(s.dy-1)/9
	base, ok := checkedSum(p.reads, s.dy, lower)
	if !ok {
		return p
	}
	if tn < n {
		p.charge, p.ok = base, true
		return p
	}
	loop, ok1 := arithmeticMul(tn-n+1, n+1)
	loop, ok2 := arithmeticMul(loop, 2)
	norm, ok3 := checkedSum(tn, n, 1)
	norm, ok4 := arithmeticMul(norm, 2)
	p.charge, ok = checkedSum(loop, norm, base)
	p.ok = ok && ok1 && ok2 && ok3 && ok4
	return p
}

func subInt64(a, b int64) (int64, bool) {
	r := a - b
	if (b > 0 && r > a) || (b < 0 && r < a) {
		return 0, false
	}
	return r, true
}

func checkedSum(values ...uint64) (uint64, bool) {
	var total uint64
	for _, v := range values {
		var ok bool
		if total, ok = arithmeticAdd(total, v); !ok {
			return 0, false
		}
	}
	return total, true
}

// divScratch sizes the numerator (with Knuth's extra limb), divisor and
// quotient (with a carry limb for rounding) buffers of a divDivide plan.
func (s *divSource) divScratch(p divPlan) (num, den, quot uint64) {
	tn, n := 1+(p.dn-1)/9, 1+(s.dy-1)/9
	// The numerator buffer also holds the doubled remainder (n+1 limbs).
	num, den = max(tn, n)+1, n
	if tn >= n {
		quot = tn - n + 2
	} else {
		quot = 2
	}
	return num, den, quot
}

const divStackLimbs = 48

// divDigits computes R = trunc(|x/y| / 10^t) into quot and returns the used
// quotient limbs and the half class of the discarded part. scratch must hold
// the plan's numerator and divisor limbs.
func (s *divSource) divDigits(p divPlan, num, den, quot []uint32, c *divCount) ([]uint32, divHalf) {
	switch p.path {
	case divTiny:
		c.add(1)
		return quot[:0], divBelow
	case divHZero:
		// R = 0; the full remainder is L = Cx against Cy·10^j with D = Cy.
		c.add(s.dx)
		return quot[:0], s.lowClass(p.k, s.y.count == 1 && s.y.limb(0) == 1, false)
	}
	un := s.buildNumerator(p, num, c)
	vn := s.y.count
	for i := range vn {
		den[i] = s.y.limb(i)
	}
	c.add(s.dy)
	q, remZero := divideLimbs(num[:max(un, vn)+1], un, den[:vn], quot, c)
	if p.k >= 0 {
		// Compare twice the remainder (now in num[:vn]) with Cy.
		return q, doubleCompare(num[:vn+1], vn, &s.y, remZero)
	}
	// k < 0: D = Cy - 2·Hrem decides together with the low part L.
	cmp := doubleCompare(num[:vn+1], vn, &s.y, remZero)
	switch cmp {
	case divAbove: // D < 0
		c.add(uint64(-p.k))
		return q, divAbove
	case divHalfClass: // D = 0
		_, sticky, lowNonzero := s.lowParts(p.k, c)
		if sticky || lowNonzero {
			return q, divAbove
		}
		return q, divHalfClass
	}
	// 2·Hrem < Cy: D = 1 exactly when 2·Hrem + 1 = Cy.
	dIsOne := incrementCompareEqual(num[:vn+1], vn, &s.y)
	c.add(uint64(-p.k))
	return q, s.lowClass(p.k, dIsOne, !remZero)
}

// lowParts returns the digit of Cx at position j-1 (j = -k), whether any
// lower digit is nonzero, and whether that digit is nonzero.
func (s *divSource) lowParts(k int64, c *divCount) (top uint32, sticky, topNonzero bool) {
	j := uint64(-k)
	c.add(j)
	top, sticky, _ = quantizeDiscard(&s.x, j)
	return top, sticky, top != 0
}

// lowClass applies the D >= 1 rows: with D = 1 the low part L alone decides
// against half of 10^j; with D >= 2 the remainder is below half unless it
// is zero. hremNonzero reports Hrem != 0.
func (s *divSource) lowClass(k int64, dIsOne, hremNonzero bool) divHalf {
	j := uint64(-k)
	top, sticky, _ := quantizeDiscard(&s.x, j)
	lowZero := top == 0 && !sticky
	if !dIsOne {
		if !hremNonzero && lowZero {
			return divExactClass
		}
		return divBelow
	}
	switch {
	case top < 5:
		if !hremNonzero && lowZero {
			return divExactClass
		}
		return divBelow
	case top == 5 && !sticky:
		return divHalfClass
	default:
		return divAbove
	}
}

// buildNumerator writes Cx·10^k (k >= 0) or trunc(Cx/10^-k) into num and
// returns its limb count; num[count] is zero for Algorithm D.
func (s *divSource) buildNumerator(p divPlan, num []uint32, c *divCount) int {
	clear(num)
	if p.k >= 0 {
		k := uint64(p.k)
		whole, part := k/9, k%9
		factor := uint64(decimalPowers[part])
		var carry uint64
		for i := range s.x.count {
			v := uint64(s.x.limb(i))*factor + carry
			num[uint64(i)+whole] = uint32(v % decimalLimbBase)
			carry = v / decimalLimbBase
		}
		top := uint64(s.x.count) + whole
		if carry != 0 {
			num[top] = uint32(carry)
			top++
		}
		c.add(p.reads)
		return int(top)
	}
	j := uint64(-p.k)
	whole, part := j/9, j%9
	low := uint64(decimalPowers[part])
	high := uint64(0)
	if part != 0 {
		high = uint64(decimalPowers[9-part])
	}
	n := 0
	for i := int(whole); i < s.x.count; i++ {
		v := uint64(s.x.limb(i)) / low
		if high != 0 && i+1 < s.x.count {
			v += uint64(s.x.limb(i+1)) % low * high
		}
		num[n] = uint32(v)
		n++
	}
	for n > 1 && num[n-1] == 0 {
		n--
	}
	c.add(p.dn)
	return n
}

// divideLimbs runs Knuth Algorithm D in base 10^9. u holds un numerator
// limbs plus one zero limb; v is the divisor with a nonzero top limb. The
// quotient is written into q and returned trimmed; the remainder is left in
// u[:len(v)] and remZero reports whether it is zero.
func divideLimbs(u []uint32, un int, v []uint32, q []uint32, c *divCount) ([]uint32, bool) {
	vn := len(v)
	clear(q)
	if un < vn {
		// Quotient zero; the remainder is the numerator itself.
		zero := true
		for i := range un {
			zero = zero && u[i] == 0
		}
		for i := un; i < vn+1 && i < len(u); i++ {
			u[i] = 0
		}
		return q[:0], zero
	}
	if vn == 1 {
		d := uint64(v[0])
		var r uint64
		for i := un - 1; i >= 0; i-- {
			cur := r*decimalLimbBase + uint64(u[i])
			q[i] = uint32(cur / d)
			r = cur % d
			c.add(1)
		}
		clear(u)
		u[0] = uint32(r)
		return trimLimbs(q[:un]), r == 0
	}
	// Normalize so the divisor's top limb is at least base/2.
	norm := decimalLimbBase / (uint64(v[vn-1]) + 1)
	if norm > 1 {
		var carry uint64
		for i := range un {
			t := uint64(u[i])*norm + carry
			u[i] = uint32(t % decimalLimbBase)
			carry = t / decimalLimbBase
		}
		u[un] = uint32(carry)
		carry = 0
		for i := range vn {
			t := uint64(v[i])*norm + carry
			v[i] = uint32(t % decimalLimbBase)
			carry = t / decimalLimbBase
		}
	} else {
		u[un] = 0
	}
	c.add(uint64(un + 1 + vn))
	top, second := uint64(v[vn-1]), uint64(v[vn-2])
	for j := un - vn; j >= 0; j-- {
		num := uint64(u[j+vn])*decimalLimbBase + uint64(u[j+vn-1])
		qhat, rhat := num/top, num%top
		for qhat >= decimalLimbBase || qhat*second > rhat*decimalLimbBase+uint64(u[j+vn-2]) {
			qhat--
			rhat += top
			if rhat >= decimalLimbBase {
				break
			}
		}
		var carry uint64
		var borrow int64
		for i := range vn {
			prod := qhat*uint64(v[i]) + carry
			carry = prod / decimalLimbBase
			t := int64(u[i+j]) - int64(prod%decimalLimbBase) - borrow
			borrow = 0
			if t < 0 {
				t += int64(decimalLimbBase)
				borrow = 1
			}
			u[i+j] = uint32(t)
		}
		t := int64(u[j+vn]) - int64(carry) - borrow
		c.add(uint64(vn + 1))
		if t < 0 {
			qhat--
			var sum uint64
			for i := range vn {
				s := uint64(u[i+j]) + uint64(v[i]) + sum
				u[i+j] = uint32(s % decimalLimbBase)
				sum = s / decimalLimbBase
			}
			t += int64(sum)
			c.add(uint64(vn + 1))
		}
		u[j+vn] = uint32(t)
		q[j] = uint32(qhat)
	}
	// Unnormalize the remainder in u[:vn].
	zero := true
	if norm > 1 {
		var r uint64
		for i := vn - 1; i >= 0; i-- {
			cur := r*decimalLimbBase + uint64(u[i])
			u[i] = uint32(cur / norm)
			r = cur % norm
		}
		// Restore the caller's divisor limbs for the class comparison.
		r = 0
		for i := vn - 1; i >= 0; i-- {
			cur := r*decimalLimbBase + uint64(v[i])
			v[i] = uint32(cur / norm)
			r = cur % norm
		}
		c.add(uint64(2 * vn))
	}
	for i := range vn {
		zero = zero && u[i] == 0
	}
	for i := vn; i < len(u); i++ {
		u[i] = 0
	}
	return trimLimbs(q[:un-vn+1]), zero
}

func trimLimbs(limbs []uint32) []uint32 {
	for len(limbs) > 0 && limbs[len(limbs)-1] == 0 {
		limbs = limbs[:len(limbs)-1]
	}
	return limbs
}

// doubleCompare doubles the remainder r[:vn] in place (r has one spare limb)
// and classifies it against y: below, exactly half or above; a zero
// remainder is exact.
func doubleCompare(r []uint32, vn int, y *coefficientView, remZero bool) divHalf {
	if remZero {
		return divExactClass
	}
	var carry uint64
	for i := range vn {
		t := uint64(r[i])*2 + carry
		r[i] = uint32(t % decimalLimbBase)
		carry = t / decimalLimbBase
	}
	r[vn] = uint32(carry)
	switch compareLimbs(r[:vn+1], y) {
	case -1:
		return divBelow
	case 0:
		return divHalfClass
	default:
		return divAbove
	}
}

// incrementCompareEqual adds one to the doubled remainder and reports
// whether it then equals y (the D = 1 case).
func incrementCompareEqual(r []uint32, vn int, y *coefficientView) bool {
	carry := uint64(1)
	for i := 0; i <= vn && carry != 0; i++ {
		t := uint64(r[i]) + carry
		r[i] = uint32(t % decimalLimbBase)
		carry = t / decimalLimbBase
	}
	return compareLimbs(r[:vn+1], y) == 0
}

// compareLimbs compares little-endian limbs a with the coefficient y.
func compareLimbs(a []uint32, y *coefficientView) int {
	a = trimLimbs(a)
	if len(a) != y.count {
		if len(a) < y.count {
			return -1
		}
		return 1
	}
	for i, v := range slices.Backward(a) {
		if v != y.limb(i) {
			if v < y.limb(i) {
				return -1
			}
			return 1
		}
	}
	return 0
}

func limbsDigits(limbs []uint32) uint64 {
	if len(limbs) == 0 {
		return 0
	}
	return uint64(len(limbs)-1)*9 + uint64(limbDigits(limbs[len(limbs)-1]))
}

// dropDigits divides R by 10^n in place, folding the removed digits into
// the half class of the previously discarded part.
func dropDigits(r []uint32, class divHalf, n uint64) ([]uint32, divHalf) {
	if n == 0 {
		return r, class
	}
	digits := limbsDigits(r)
	if n > digits {
		exact := len(r) == 0 && class == divExactClass
		clear(r)
		if exact {
			return r[:0], divExactClass
		}
		return r[:0], divBelow
	}
	view := coefficientView{slow: r, count: len(r)}
	guard, sticky, _ := quantizeDiscard(&view, n)
	sticky = sticky || class != divExactClass
	shiftRightDigits(r, n)
	r = trimLimbs(r)
	switch {
	case guard == 0 && !sticky:
		return r, divExactClass
	case guard < 5:
		return r, divBelow
	case guard == 5 && !sticky:
		return r, divHalfClass
	default:
		return r, divAbove
	}
}

// shiftRightDigits divides little-endian limbs by 10^n in place.
func shiftRightDigits(r []uint32, n uint64) {
	whole, part := int(n/9), n%9
	low := uint64(decimalPowers[part])
	high := uint64(0)
	if part != 0 {
		high = uint64(decimalPowers[9-part])
	}
	for i := range r {
		src := i + whole
		var v uint64
		if src < len(r) {
			v = uint64(r[src]) / low
			if high != 0 && src+1 < len(r) {
				v += uint64(r[src+1]) % low * high
			}
		}
		r[i] = uint32(v)
	}
}

// trailingZeroDigits counts trailing decimal zeros of nonzero limbs.
func trailingZeroDigits(r []uint32) uint64 {
	var z uint64
	for _, limb := range r {
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

// incrementLimbs adds one; r must have a spare zero limb beyond its length.
func incrementLimbs(r []uint32) []uint32 {
	full := r[:cap(r)]
	carry := uint64(1)
	for i := 0; carry != 0; i++ {
		t := uint64(full[i]) + carry
		full[i] = uint32(t % decimalLimbBase)
		carry = t / decimalLimbBase
		if i >= len(r) {
			r = full[:i+1]
		}
	}
	return r
}

// divScratchBuffers slices the scratch for a plan from the caller's stack
// array when it fits, after physical admission of the heap plan.
// resultDigits bounds the planned final coefficient length. Returning the
// slices, instead of storing them beside the array, keeps the caller's
// array on its stack.
func divScratchBuffers(stack *[divStackLimbs]uint32, s *divSource, p divPlan, resultDigits uint64) (num, den, quot []uint32, ok bool) {
	n, d, q := uint64(0), uint64(0), uint64(2)
	if p.path == divDivide {
		n, d, q = s.divScratch(p)
	}
	total, ok := checkedSum(n, d, q)
	if !ok || !divAdmitted(total, resultDigits) {
		return nil, nil, nil, false
	}
	var buf []uint32
	if total <= divStackLimbs {
		buf = stack[:total]
	} else {
		buf = make([]uint32, total)
	}
	return buf[:n], buf[n : n+d], buf[n+d : total], true
}

// divAdmitted checks the combined live bytes of heap scratch and the result
// coefficient against the target's addressability.
func divAdmitted(scratchLimbs, resultDigits uint64) bool {
	return divAdmittedLive(scratchLimbs, resultDigits, 0)
}

// divScratchHeap checks one arena independently before the combined live
// admission. A caller with a larger stack (Pow) supplies its actual limit.
func divScratchHeap(limbs, stackLimit uint64) (uint64, bool) {
	if limbs <= stackLimit {
		return 0, true
	}
	maxObject, _, ok := bigIntRuntimeLimits(runtime.GOOS, runtime.GOARCH, uint64(bits.UintSize))
	if !ok || limbs > uint64(math.MaxInt)/4 {
		return 0, false
	}
	bytes, ok := bigIntRoundObject(limbs * 4)
	return bytes, ok && bytes <= maxObject
}

// divAdmittedLive also includes a caller's independently checked live heap
// arenas. Splitting Pow's power and division arenas must not bypass the
// aggregate addressability limit.
func divAdmittedLive(scratchLimbs, resultDigits, liveBytes uint64) bool {
	maxObject, maxAddress, ok := bigIntRuntimeLimits(runtime.GOOS, runtime.GOARCH, uint64(bits.UintSize))
	if !ok {
		return false
	}
	scratchBytes, ok := divScratchHeap(scratchLimbs, divStackLimbs)
	if !ok {
		return false
	}
	var resultBytes uint64
	if resultDigits > 38 {
		limbs := 1 + (resultDigits-1)/9
		if limbs > uint64(math.MaxInt)/4 {
			return false
		}
		resultBytes, ok = bigIntRoundObject(limbs*4 + 64)
		if !ok || resultBytes > maxObject {
			return false
		}
	}
	total, ok := checkedSum(liveBytes, scratchBytes, resultBytes)
	return ok && total <= maxAddress
}

// divOutcome carries a finished coefficient to publication.
type divOutcome struct {
	r        []uint32
	exponent int64
	events   Conditions
}

// divPublish checks the int32 exponent, final digit and work quotas, and
// publishes the coefficient. The result never aliases scratch.
func divPublish(o divOutcome, negative bool, charge uint64, budget limits, op string) (Decimal, error) {
	if o.exponent < math.MinInt32 || o.exponent > math.MaxInt32 {
		return Decimal{}, newError(op, ErrExponentRange)
	}
	r := trimLimbs(o.r)
	n := max(limbsDigits(r), 1)
	if !admitted(budget.MaxDigits, n, true) || !contextFinalWork(charge, n, budget.MaxWork) {
		return Decimal{}, newError(op, ErrInsufficientStorage)
	}
	if len(r) == 0 {
		return zeroDecimal(int32(o.exponent)), nil
	}
	if n <= 38 {
		return publishInlineArithmetic(r, int32(o.exponent), negative), nil
	}
	return publishScratch(r, int32(o.exponent), negative), nil
}

// divZero reports the zero-divisor outcomes.
func divZero(d Decimal, op string) error {
	if d.isZero() {
		return newError(op, ErrDivisionUndefined)
	}
	return newError(op, ErrDivisionByZero)
}

func (d Decimal) divExact(other Decimal, budget limits, op string) (Decimal, error) {
	result, _, err := d.divUnlimited(other, budget, op)
	return result, err
}

// divUnlimited is bare Div and a context with unlimited precision. The
// inline quotient is returned under a budget that admits the bound of every
// such division's charges, inlineDivExactWork, or else the general path's
// own charges for this one (divExactInlineAdmitted).
func (d Decimal) divUnlimited(other Decimal, budget limits, op string) (Decimal, Conditions, error) {
	if inlineDivOperands(d, other) {
		if result, ok := inlineDivExact(d, other); ok && (budget.admits(inlineResultDigits, inlineDivExactWork) || divExactInlineAdmitted(d, other, result, budget)) {
			return result, 0, nil
		}
	}
	return d.divUnlimitedLimbs(other, budget, op)
}

// divExactInlineAdmitted reports whether budget admits divUnlimitedLimbs's
// charges for the inline shape whose exact quotient is result: the
// precharge of its plan at the exact division exponent, the scratch that
// plan sizes, and the final W = B + 2N + 1 over the quotient's N digits,
// which implies the precharge's own cap. The inline quotient exists only at
// an ideal exponent inside int32, where that division exponent has no
// refusal, and its plan always divides: the numerator is the dividend with
// more than three digits appended for each digit of the divisor.
//
//go:noinline
func divExactInlineAdmitted(d, other, result Decimal, budget limits) bool {
	s := divSource{dx: inlineDigits(d.words), dy: inlineDigits(other.words), ideal: int64(d.exponent()) - int64(other.exponent())}
	t, _, _ := divUnlimitedTarget(s.dy, s.ideal)
	p := s.plan(t)
	num, den, quot := s.divScratch(p)
	n := inlineDigits(result.words)
	work, ok := contextFinalCharge(p.charge, n)
	return p.ok && ok && budget.admits(n, work) && divAdmitted(num+den+quot, p.dn)
}

// divUnlimitedLimbs is the general exact-division path.
func (d Decimal) divUnlimitedLimbs(other Decimal, budget limits, op string) (Decimal, Conditions, error) {
	if other.isZero() {
		return Decimal{}, 0, divZero(d, op)
	}
	ideal := int64(d.exponent()) - int64(other.exponent())
	if d.isZero() {
		if ideal < math.MinInt32 || ideal > math.MaxInt32 {
			return contextFailure(op, ErrExponentRange)
		}
		if !admitted(budget.MaxDigits, 1, true) || !contextFinalWork(1, 1, budget.MaxWork) {
			return contextFailure(op, ErrInsufficientStorage)
		}
		return zeroDecimal(int32(ideal)), 0, nil
	}
	s := newDivSource(d, other)
	t, kMax, code := divUnlimitedTarget(s.dy, ideal)
	if code != 0 {
		return contextFailure(op, code)
	}
	p := s.plan(t)
	if !p.ok || budget.MaxWork != 0 && p.charge > budget.MaxWork {
		return contextFailure(op, ErrInsufficientStorage)
	}
	var stack [divStackLimbs]uint32
	num, den, quot, admittedPlan := divScratchBuffers(&stack, &s, p, p.dn)
	if !admittedPlan {
		return contextFailure(op, ErrInsufficientStorage)
	}
	r, class := s.divDigits(p, num, den, quot, nil)
	if class != divExactClass {
		return Decimal{}, 0, conditionError(op, Inexact, divRemedy)
	}
	result, err := finishExact(r, t, kMax, s.negative, p.charge, budget, op)
	return result, 0, err
}

// finishExact publishes an exact quotient R at exponent t after stripping
// up to maxStrip trailing zeros toward the ideal exponent. It is shared by
// every exact source; each source refuses a non-terminating value with
// its own remedy message before calling it.
func finishExact(r []uint32, t int64, maxStrip uint64, negative bool, charge uint64, budget limits, op string) (Decimal, error) {
	z := min(trailingZeroDigits(r), maxStrip)
	shiftRightDigits(r, z)
	return divPublish(divOutcome{r: r, exponent: t + int64(z)}, negative, charge, budget, op)
}

func (d Decimal) divToExponent(other Decimal, target int32, mode RoundingMode, budget limits, op string) (Decimal, Conditions, error) {
	if budget.admits(inlineResultDigits, inlineDivWork) && mode <= Exact && inlineDivShape(d, other) {
		if result, events, refused, ok := inlineDivToExponent(d, other, target, mode); ok {
			if refused {
				return contextExactRefusal(op)
			}
			return result, events, nil
		}
	}
	return d.divToExponentLimbs(other, target, mode, budget, op)
}

// divToExponentLimbs is the general DivToExponent path.
func (d Decimal) divToExponentLimbs(other Decimal, target int32, mode RoundingMode, budget limits, op string) (Decimal, Conditions, error) {
	var stack [divStackLimbs]uint32
	o, events, charge, err := d.divToExponentRound(&stack, other, target, mode, budget, op)
	if err != nil {
		return Decimal{}, 0, err
	}
	result, err := divPublish(o, d.negative() != other.negative(), charge, budget, op)
	if err != nil {
		return Decimal{}, 0, err
	}
	return result, events, nil
}

// divToExponentRound is DivToExponent up to publication: the rounded
// coefficient at exponent target with its Conditions and the admitted
// charge, which divPublish completes with W = charge + 2N + 1. A zero
// dividend gives an empty coefficient (RoundToMultiple reuses it).
// The coefficient may alias the caller's stack, which keeps small
// quotients off the heap.
func (d Decimal) divToExponentRound(stack *[divStackLimbs]uint32, other Decimal, target int32, mode RoundingMode, budget limits, op string) (divOutcome, Conditions, uint64, error) {
	if mode > Exact {
		_, _, err := quantizeInvalidMode(op)
		return divOutcome{}, 0, 0, err
	}
	if other.isZero() {
		return divOutcome{}, 0, 0, divZero(d, op)
	}
	if d.isZero() {
		return divOutcome{exponent: int64(target)}, 0, 1, nil
	}
	s := newDivSource(d, other)
	t := int64(target)
	p := s.plan(t)
	if !p.ok || budget.MaxWork != 0 && p.charge > budget.MaxWork {
		return divOutcome{}, 0, 0, newError(op, ErrInsufficientStorage)
	}
	resultDigits := uint64(1)
	if p.path == divDivide && p.dn >= s.dy {
		resultDigits = p.dn - s.dy + 2
		// The quotient has at least dn-dy digits; refuse a result that
		// cannot fit the digit quota before allocating the scratch.
		if budget.MaxDigits != 0 && p.dn-s.dy > budget.MaxDigits {
			return divOutcome{}, 0, 0, newError(op, ErrInsufficientStorage)
		}
	}
	num, den, quot, admittedPlan := divScratchBuffers(stack, &s, p, resultDigits)
	if !admittedPlan {
		return divOutcome{}, 0, 0, newError(op, ErrInsufficientStorage)
	}
	r, class := s.divDigits(p, num, den, quot, nil)
	o, events, err := roundToExponent(r, class, t, s.ideal, s.negative, mode, op)
	return o, events, p.charge, err
}

// finishToExponent rounds a truncated coefficient R with its half class
// once at exactly exponent t under mode. r must have a
// spare zero limb beyond its length for the rounding carry.
func finishToExponent(r []uint32, class divHalf, t, ideal int64, negative bool, mode RoundingMode, charge uint64, budget limits, op string) (Decimal, Conditions, error) {
	o, events, err := roundToExponent(r, class, t, ideal, negative, mode, op)
	if err != nil {
		return Decimal{}, 0, err
	}
	result, err := divPublish(o, negative, charge, budget, op)
	if err != nil {
		return Decimal{}, 0, err
	}
	return result, events, nil
}

// roundToExponent is finishToExponent before publication.
func roundToExponent(r []uint32, class divHalf, t, ideal int64, negative bool, mode RoundingMode, op string) (divOutcome, Conditions, error) {
	inexact := class != divExactClass
	if mode == Exact && inexact {
		_, _, err := contextExactRefusal(op)
		return divOutcome{}, 0, err
	}
	events := Conditions(0)
	if inexact {
		events = Inexact | Rounded
	} else if t > ideal {
		events = Rounded
	}
	guard, sticky := class.guardSticky()
	var low uint32
	if len(r) > 0 {
		low = r[0] % 10
	}
	up := contextRoundUp(mode, negative, guard, sticky, low)
	if inexact {
		events |= roundingDirection(up, negative)
	}
	if up {
		r = incrementLimbs(r)
	}
	return divOutcome{r: r, exponent: t}, events, nil
}

func (d Decimal) divContext(other Decimal, ctx Context, budget limits, op string) (Decimal, Conditions, error) {
	if ctx.precision == 0 {
		return d.divUnlimited(other, budget, op)
	}
	if budget.admits(inlineResultDigits, inlineDivWork) && ctx.precision <= inlineDivMaxPrecision && inlineDivShape(d, other) {
		if result, conditions, err, ok := inlineDivContext(d, other, &ctx, op); ok {
			return result, conditions, err
		}
	}
	return d.divContextLimbs(other, ctx, budget, op)
}

// divContextLimbs is the general finite-precision DivWithContext path.
func (d Decimal) divContextLimbs(other Decimal, ctx Context, budget limits, op string) (Decimal, Conditions, error) {
	if other.isZero() {
		return Decimal{}, 0, divZero(d, op)
	}
	ideal := int64(d.exponent()) - int64(other.exponent())
	if d.isZero() {
		if ideal < math.MinInt32 || ideal > math.MaxInt32 {
			return contextFailure(op, ErrExponentRange)
		}
		if !admitted(budget.MaxDigits, 1, true) || !contextFinalWork(1, 1, budget.MaxWork) {
			return contextFailure(op, ErrInsufficientStorage)
		}
		return zeroDecimal(int32(ideal)), 0, nil
	}
	s := newDivSource(d, other)
	tPrime, etiny := divContextTarget(s.dx, s.dy, s.ideal, ctx)
	p := s.plan(tPrime)
	if !p.ok || budget.MaxWork != 0 && p.charge > budget.MaxWork {
		return contextFailure(op, ErrInsufficientStorage)
	}
	return s.contextQuotient(p, tPrime, etiny, &ctx, p.charge, budget, op, nil, 0, true)
}

// exactProbe chooses an exact-first target without adopting bare Div's
// int32-exponent restrictions. Every terminating reduced denominator has
// at most ceil(3.322*dy) fractional places. The plan reserves at least
// lower+tn-n+1 units beyond a conservative counted-work bound, so a probe
// within that slack plus a full fallback still obeys the tariff.
func (s *divSource) exactProbe(p divPlan, target int64) (divPlan, int64, bool) {
	if !p.ok || p.path != divDivide || p.k < 0 || p.dn < s.dy {
		return divPlan{}, 0, false
	}
	k, ok := arithmeticMul(s.dy, 3322)
	if ok {
		k, ok = arithmeticAdd(k, 999)
	}
	if !ok || k/1000 > math.MaxInt64 {
		return divPlan{}, 0, false
	}
	t, ok := subInt64(s.ideal, int64(k/1000))
	if !ok || t <= target {
		return divPlan{}, 0, false
	}
	trial := s.plan(t)
	tn, n := 1+(p.dn-1)/9, 1+(s.dy-1)/9
	lower := min(1+(s.dx-1)/9, n)
	slack, ok := checkedSum(lower, tn-n, 1)
	return trial, t, ok && trial.ok && trial.charge <= slack
}

func (s *divSource) scratchTotal(p divPlan) uint64 {
	if p.path != divDivide {
		return 2
	}
	n, d, q := s.divScratch(p)
	return n + d + q // each <= the checked digit plan; inputs fit int64
}

// probeResultDigits covers exact publication, including guarded overflow's
// genuinely p-digit maximum finite value. A probe returns only when exact
// (or refusing Exact), so its prefix never owns an inexact rounding decision.
func (s *divSource) probeResultDigits(p divPlan, ctx *Context) uint64 {
	n := uint64(1)
	if p.dn >= s.dy {
		n = p.dn - s.dy + 1
	}
	if ctx.guarded && ctx.rounding != Exact {
		adjusted, ok := subInt64(s.ideal, int64(s.dy)-int64(s.dx))
		if !ok || adjusted > int64(ctx.guards.Emax) {
			return uint64(ctx.precision)
		}
	}
	return min(n, uint64(ctx.precision))
}

// tryExactContext has its own frame: an unsuccessful probe's scratch is
// unreachable before fallback allocates. Heap estimates count both allocations.
func (s *divSource) tryExactContext(p divPlan, target, etiny int64, ctx *Context, charge uint64, budget limits, op string, cnt *divCount, liveBytes uint64) (Decimal, Conditions, error, bool) {
	bound := s.probeResultDigits(p, ctx)
	if !divAdmittedLive(s.scratchTotal(p), bound, liveBytes) {
		return Decimal{}, 0, nil, false
	}
	var stack [divStackLimbs]uint32
	num, den, quot, ok := divScratchBuffers(&stack, s, p, bound)
	if !ok {
		return Decimal{}, 0, nil, false
	}
	r, class := s.divDigits(p, num, den, quot, cnt)
	if class == divExactClass {
		v, c, err := finishContext(r, class, target, etiny, s.ideal, s.negative, ctx, charge, budget, op)
		return v, c, err, true
	}
	if ctx.rounding == Exact {
		v, c, err := contextExactRefusal(op)
		return v, c, err, true
	}
	return Decimal{}, 0, nil, false
}

// contextQuotient computes the context quotient under the plan's
// precharge, target and finisher. probe is a test seam; production always
// enables it.
func (s *divSource) contextQuotient(p divPlan, target, etiny int64, ctx *Context, charge uint64, budget limits, op string, cnt *divCount, liveBytes uint64, probe bool) (Decimal, Conditions, error) {
	if !p.ok || !admitted(budget.MaxWork, charge, true) {
		return contextFailure(op, ErrInsufficientStorage)
	}
	if trial, t, ok := s.exactProbe(p, target); probe && ok {
		if v, c, err, done := s.tryExactContext(trial, t, etiny, ctx, charge, budget, op, cnt, liveBytes); done {
			return v, c, err
		}
	}
	bound := uint64(ctx.precision) + 1
	if !divAdmittedLive(s.scratchTotal(p), bound, liveBytes) {
		return contextFailure(op, ErrInsufficientStorage)
	}
	var stack [divStackLimbs]uint32
	num, den, quot, ok := divScratchBuffers(&stack, s, p, bound)
	if !ok {
		return contextFailure(op, ErrInsufficientStorage)
	}
	r, class := s.divDigits(p, num, den, quot, cnt)
	return finishContext(r, class, target, etiny, s.ideal, s.negative, ctx, charge, budget, op)
}

// finishContext rounds a truncated coefficient R′ computed at t′ (holding
// at least p digits, or empty when the value lies below 10^Etiny, or an
// exact R′ of fewer than p digits from an exact-first source, published at
// t′) once to the context precision with guards, conditions and traps.
// r must have a spare zero limb for the rounding carry.
func finishContext(r []uint32, class divHalf, tPrime, etiny, ideal int64, negative bool, ctx *Context, charge uint64, budget limits, op string) (Decimal, Conditions, error) {
	out, verdict := roundContext(r, class, tPrime, etiny, ideal, negative, ctx)
	switch verdict {
	case contextOverflows:
		return contextOverflow(charge, negative, *ctx, budget, op)
	case contextRefusesExact:
		return contextExactRefusal(op)
	case contextBroken:
		return contextFailure(op, ErrInsufficientStorage)
	}
	result, err := divPublish(divOutcome{r: out.r, exponent: out.exponent}, negative, charge, budget, op)
	if err != nil {
		return Decimal{}, 0, err
	}
	return contextOutcome(result, out.events, ctx.traps, op)
}

// contextVerdict is roundContext's non-publishing outcome.
type contextVerdict uint8

const (
	contextPublishes contextVerdict = iota
	contextOverflows
	contextRefusesExact
	contextBroken // an internal invariant failed
)

// roundContext is the finisher's numerical core, shared by every producer
// of a truncated prefix and class: it rounds once in the context's mode,
// applies guards and returns the coefficient, exponent and conditions to
// publish, or the overflow or Exact refusal that replaces publication.
func roundContext(r []uint32, class divHalf, tPrime, etiny, ideal int64, negative bool, ctx *Context) (divOutcome, contextVerdict) {
	precision := int64(ctx.precision)
	// An empty R' means the value lies below 10^t' = 10^Etiny: tiny.
	adjusted := tPrime + int64(limbsDigits(r)) - 1
	if len(r) == 0 {
		adjusted = tPrime - 1
	}
	var tiny bool
	t := adjusted - precision + 1
	if ctx.guarded {
		if adjusted > int64(ctx.guards.Emax) {
			if ctx.rounding == Exact {
				return divOutcome{}, contextRefusesExact
			}
			return divOutcome{}, contextOverflows
		}
		tiny = adjusted < int64(ctx.guards.Emin)
		t = max(t, etiny)
	}
	drop, ok := subInt64(t, tPrime)
	if ok && drop < 0 && class == divExactClass {
		// An exact R′ shorter than p digits (an exact-first source) is
		// already the result at t′; there is nothing to round or pad.
		t, drop = tPrime, 0
	}
	if !ok || drop < 0 {
		return divOutcome{}, contextBroken // invariant: t′ never exceeds t
	}
	r, class = dropDigits(r, class, uint64(drop))
	inexact := class != divExactClass
	if ctx.rounding == Exact && inexact {
		return divOutcome{}, contextRefusesExact
	}
	events := Conditions(0)
	switch {
	case inexact:
		events = Inexact | Rounded
	case t > ideal:
		events = Rounded
	case t < ideal && len(r) > 0:
		z := min(trailingZeroDigits(r), uint64(ideal-t))
		shiftRightDigits(r, z)
		r = trimLimbs(r)
		t += int64(z)
	}
	guard, sticky := class.guardSticky()
	var low uint32
	if len(r) > 0 {
		low = r[0] % 10
	}
	up := contextRoundUp(ctx.rounding, negative, guard, sticky, low)
	if inexact {
		events |= roundingDirection(up, negative)
	}
	if up {
		r = incrementLimbs(r)
		if limbsDigits(r) > uint64(precision) {
			shiftRightDigits(r, 1)
			r = trimLimbs(r)
			t++
		}
	}
	if ctx.guarded {
		if len(r) > 0 && t+int64(limbsDigits(r))-1 > int64(ctx.guards.Emax) {
			return divOutcome{}, contextOverflows
		}
		if tiny {
			events |= Subnormal
			if inexact {
				events |= Underflow
			}
		}
	}
	return divOutcome{r: r, exponent: t, events: events}, contextPublishes
}

// Inline division fast paths. They serve calls whose budget admits
// inlineDivWork and whose operands are nonzero inline coefficients, and
// they report ok=false for every case they do not prove equal to the
// general path, which keeps the documented semantics.

// inlineDivMaxPrecision bounds the context precision the inline path
// serves: the general path's physical admission of a p+1-digit result never
// refuses at or below it, so only the numerical outcome remains to match.
const inlineDivMaxPrecision = 38

// inlineDivOperands reports whether d / other has the inline fast-path shape.
func inlineDivOperands(d, other Decimal) bool {
	return d.slow == nil && other.slow == nil && other.words.hi == 0 && other.words.lo != 0 && d.words != (uint128{})
}

// inlineDivShape is inlineDivOperands without the one-word divisor: the
// shape of the rounding fast paths, whose two-word divisors divide a
// 256-bit numerator.
func inlineDivShape(d, other Decimal) bool {
	return d.slow == nil && other.slow == nil && other.words != (uint128{}) && d.words != (uint128{})
}

// inlineDivTruncWide is inlineDivTrunc for a two-word divisor, served for
// 0 ≤ k ≤ 38 when the quotient of the 256-bit numerator x·10^k is inline
// with room for a rounding increment.
func inlineDivTruncWide(x, y uint128, k int64) (uint128, divHalf, bool) {
	if k < 0 || k > 38 {
		return uint128{}, 0, false
	}
	q, r, ok := divWide(mulWide(x, pow10Wide[k]), y)
	if !ok {
		return uint128{}, 0, false
	}
	return q, inlineHalf(r, y), true
}

// divWide is the truncated quotient and remainder of a 256-bit numerator
// by a two-word divisor (v.hi ≠ 0): Knuth's algorithm D over 64-bit digits,
// three quotient digits from a normalized divisor. ok is false when the
// quotient reaches 2^127.
func divWide(u wide256, v uint128) (q, r uint128, ok bool) {
	s := uint(bits.LeadingZeros64(v.hi))
	v1, v0 := v.hi<<s|v.lo>>(64-s), v.lo<<s
	un := [5]uint64{u[0] << s, u[1]<<s | u[0]>>(64-s), u[2]<<s | u[1]>>(64-s), u[3]<<s | u[2]>>(64-s), u[3] >> (64 - s)}
	var quotient [3]uint64
	for j := 2; j >= 0; j-- {
		// Estimate from the top two words; the remainder invariant keeps
		// un[j+2] ≤ v1, and equality means the digit is 2^64−1 or one less.
		var qhat, rhat uint64
		settled := false
		if un[j+2] >= v1 {
			qhat = ^uint64(0)
			var carry uint64
			rhat, carry = bits.Add64(un[j+1], v1, 0)
			settled = carry != 0
		} else {
			qhat, rhat = bits.Div64(un[j+2], un[j+1], v1)
		}
		// With a two-digit divisor the test against the third numerator
		// digit is exact: q̂·v0 ≤ r̂·2^64 + un[j] is q̂·v ≤ un[j..j+2], so
		// the subtraction below never borrows and needs no add-back.
		for !settled {
			ph, pl := bits.Mul64(qhat, v0)
			if ph < rhat || ph == rhat && pl <= un[j] {
				break
			}
			qhat--
			var carry uint64
			rhat, carry = bits.Add64(rhat, v1, 0)
			settled = carry != 0
		}
		ph0, pl0 := bits.Mul64(qhat, v0)
		ph1, pl1 := bits.Mul64(qhat, v1)
		mid, carry := bits.Add64(pl1, ph0, 0)
		var borrow uint64
		un[j], borrow = bits.Sub64(un[j], pl0, 0)
		un[j+1], borrow = bits.Sub64(un[j+1], mid, borrow)
		un[j+2] -= ph1 + carry + borrow
		quotient[j] = qhat
	}
	if quotient[2] != 0 || quotient[1]>>63 != 0 {
		return uint128{}, uint128{}, false
	}
	return uint128{quotient[0], quotient[1]}, uint128{un[0]>>s | un[1]<<(64-s), un[1] >> s}, true
}

// inlineDivWord divides a two-word magnitude by a nonzero word.
func inlineDivWord(x uint128, y uint64) (q uint128, r uint64) {
	if x.hi == 0 {
		return uint128{lo: x.lo / y}, x.lo % y
	}
	q.hi, r = bits.Div64(0, x.hi, y)
	q.lo, r = bits.Div64(r, x.lo, y)
	return q, r
}

// inlineHalf classifies a remainder r of a division by d (0 <= r < d)
// against half of d without forming 2r, which could overflow.
func inlineHalf(r, d uint128) divHalf {
	if r == (uint128{}) {
		return divExactClass
	}
	var rest uint128
	var borrow uint64
	rest.lo, borrow = bits.Sub64(d.lo, r.lo, 0)
	rest.hi, _ = bits.Sub64(d.hi, r.hi, borrow)
	switch inlineCompare(r, rest) {
	case -1:
		return divBelow
	case 0:
		return divHalfClass
	default:
		return divAbove
	}
}

// inlineDivTrunc is divDigits for an inline dividend x and one-word divisor
// y: R = trunc(x·10^k / y) and the half class of the discarded part, with
// k = ideal − t. It reports ok=false when x·10^k leaves 128 bits or a
// negative k needs a divisor y·10^-k wider than the kernel covers.
func inlineDivTrunc(x uint128, y uint64, k int64) (uint128, divHalf, bool) {
	switch {
	case k >= 0:
		if k > 38 {
			return uint128{}, 0, false
		}
		n, fits := inlineScale(x, uint64(k))
		if !fits {
			return inlineDivTruncScaled(x, y, k)
		}
		q, r := inlineDivWord(n, y)
		return q, inlineHalf(uint128{lo: r}, uint128{lo: y}), true
	case k <= -39:
		// x < 2^128 and 2x < 10^39 <= y·10^-k: R = 0 below half.
		return uint128{}, divBelow, true
	case k < -19:
		return uint128{}, 0, false
	}
	// x = q1·y + r1 and q1 = q·10^j + r2, so x = q·(y·10^j) + r2·y + r1
	// with 0 <= r2·y + r1 < y·10^j.
	p := pow10Words[-k]
	q1, r1 := inlineDivWord(x, y)
	q, r2 := inlineDivWord(q1, p)
	var rem uint128
	var carry uint64
	rem.hi, rem.lo = bits.Mul64(r2, y)
	rem.lo, carry = bits.Add64(rem.lo, r1, 0)
	rem.hi += carry
	var divisor uint128
	divisor.hi, divisor.lo = bits.Mul64(y, p)
	return q, inlineHalf(rem, divisor), true
}

// inlineDivTruncScaled is inlineDivTrunc for 0 ≤ k ≤ 38 when x·10^k leaves
// two words but not four: word divisions of the 256-bit numerator, served
// when the quotient is inline with room for a rounding increment. It stays
// out of line so that the two-word case keeps a small frame.
//
//go:noinline
func inlineDivTruncScaled(x uint128, y uint64, k int64) (uint128, divHalf, bool) {
	w := mulWide(x, pow10Wide[k])
	r := w.divSmall(y)
	if w[2]|w[3] != 0 || w[1]>>63 != 0 {
		return uint128{}, 0, false
	}
	return uint128{w[0], w[1]}, inlineHalf(uint128{lo: r}, uint128{lo: y}), true
}

// inlineDivToExponent is divToExponentRound and divPublish over two words:
// the same truncated coefficient and class, rounded by roundToExponent's
// rule. The parity of the retained coefficient is the parity of its low
// limb because the limb base is even.
func inlineDivToExponent(d, other Decimal, target int32, mode RoundingMode) (result Decimal, events Conditions, exactRefusal, ok bool) {
	ideal := int64(d.exponent()) - int64(other.exponent())
	var q uint128
	var class divHalf
	if other.words.hi == 0 {
		q, class, ok = inlineDivTrunc(d.words, other.words.lo, ideal-int64(target))
	} else {
		q, class, ok = inlineDivTruncWide(d.words, other.words, ideal-int64(target))
	}
	if !ok {
		return Decimal{}, 0, false, false
	}
	inexact := class != divExactClass
	if mode == Exact && inexact {
		return Decimal{}, 0, true, true
	}
	if inexact {
		events = Inexact | Rounded
	} else if int64(target) > ideal {
		events = Rounded
	}
	negative := d.negative() != other.negative()
	guard, sticky := class.guardSticky()
	up := contextRoundUp(mode, negative, guard, sticky, uint32(q.lo&1))
	if inexact {
		events |= roundingDirection(up, negative)
	}
	if up {
		// A rounded quotient has a divisor y >= 2 or a scale-down k < 0,
		// so q < 2^127 and the increment stays inline.
		var carry uint64
		q.lo, carry = bits.Add64(q.lo, 1, 0)
		q.hi += carry
	}
	return inlineDecimal(q, target, negative), events, false, true
}

// inlineDivExact is divUnlimited for the inline shape. With y = 2^a·5^b·m
// and gcd(m, 10) = 1, x/y terminates exactly when m divides x, and then
// the least k >= 0 with y | x·10^k is at most max(a, b) <= kMax. The
// general path's result is x·10^k/y at exponent ideal − k: its trailing-zero
// strip stops at the ideal exponent or at a nonzero digit. Long division
// finds k one digit at a time. Nontermination, a quotient leaving 128 bits
// and exponents outside int32 defer to the general path.
func inlineDivExact(d, other Decimal) (Decimal, bool) {
	ideal := int64(d.exponent()) - int64(other.exponent())
	if ideal < math.MinInt32 || ideal > math.MaxInt32 {
		return Decimal{}, false
	}
	y := other.words.lo
	q, r := inlineDivWord(d.words, y)
	k := int64(0)
	if r != 0 {
		a := bits.TrailingZeros64(y)
		m, b := y>>a, 0
		for m%5 == 0 {
			m, b = m/5, b+1
		}
		if r%m != 0 {
			return Decimal{}, false // m | y, so x ≡ r (mod m): nonterminating
		}
		for r != 0 {
			if k == int64(max(a, b)) {
				return Decimal{}, false // unreachable: y | x·10^max(a,b)
			}
			// r < y, so the high word of 10r is below y and Div64 is safe.
			hi, lo := bits.Mul64(r, 10)
			var digit uint64
			digit, r = bits.Div64(hi, lo, y)
			high, low := bits.Mul64(q.lo, 10)
			overflow, top := bits.Mul64(q.hi, 10)
			var c1, c2, c3 uint64
			top, c1 = bits.Add64(top, high, 0)
			low, c2 = bits.Add64(low, digit, 0)
			top, c3 = bits.Add64(top, 0, c2)
			if overflow != 0 || c1 != 0 || c3 != 0 {
				return Decimal{}, false
			}
			q = uint128{low, top}
			k++
		}
		if ideal-k < math.MinInt32 {
			return Decimal{}, false
		}
	}
	return inlineDecimal(q, int32(ideal-k), d.negative() != other.negative()), true
}

// inlineStripWide removes trailing decimal zeros from a two-word q below
// 2^127, at most limit of them and at most the 19 of its low part: q is
// h·10^19 + l with h below 2^64, the zeros of l are counted in one word,
// and q/10^m is h·10^(19−m) + l/10^m. It returns the quotient and m; a
// caller continues on a one-word quotient, which is h when m is 19.
//
//go:noinline
func inlineStripWide(q uint128, limit int64) (uint128, int64) {
	high, low := bits.Div64(q.hi, q.lo, pow10Words[19])
	m := int64(0)
	for m < 19 && m < limit && low%10 == 0 {
		low /= 10
		m++
	}
	if m == 19 {
		return uint128{lo: high}, m
	}
	hi, lo := bits.Mul64(high, pow10Words[19-m])
	lo, carry := bits.Add64(lo, low, 0)
	return uint128{lo, hi + carry}, m
}

// finishContextInline is finishContext, unbudgeted, for a nonzero truncated
// coefficient R′ held in two words: roundContext's steps in word
// arithmetic, published inline. ok is false, deferring to finishContext,
// for an overflow, an Exact refusal, a drop of more than 19 digits or of
// every digit, and an exponent outside int32.
func finishContextInline(q uint128, class divHalf, tPrime, etiny, ideal int64, negative bool, ctx *Context, op string) (Decimal, Conditions, error, bool) {
	if q == (uint128{}) || q.hi>>63 != 0 {
		return Decimal{}, 0, nil, false
	}
	precision := int64(ctx.precision)
	n := int64(inlineDigits(q))
	adjusted := tPrime + n - 1
	t := adjusted - precision + 1
	tiny := false
	if ctx.guarded {
		if adjusted > int64(ctx.guards.Emax) {
			return Decimal{}, 0, nil, false
		}
		tiny = adjusted < int64(ctx.guards.Emin)
		t = max(t, etiny)
	}
	drop := t - tPrime
	if drop < 0 {
		if class != divExactClass {
			return Decimal{}, 0, nil, false
		}
		t, drop = tPrime, 0
	}
	if drop > 0 {
		if drop > 19 || drop > n {
			return Decimal{}, 0, nil, false
		}
		var rem uint64
		q, rem = inlineDivWord(q, pow10Words[drop])
		guard := rem / pow10Words[drop-1]
		sticky := class != divExactClass || rem%pow10Words[drop-1] != 0
		switch {
		case guard == 0 && !sticky:
			class = divExactClass
		case guard < 5:
			class = divBelow
		case guard == 5 && !sticky:
			class = divHalfClass
		default:
			class = divAbove
		}
	}
	inexact := class != divExactClass
	if inexact && ctx.rounding == Exact {
		return Decimal{}, 0, nil, false
	}
	var events Conditions
	switch {
	case inexact:
		events = Inexact | Rounded
	case t > ideal:
		events = Rounded
	case t < ideal && q != (uint128{}):
		if q.hi != 0 {
			var stripped int64
			q, stripped = inlineStripWide(q, ideal-t)
			t += stripped
			if q.hi != 0 {
				break
			}
		}
		w := q.lo
		for t < ideal && w%10 == 0 {
			w /= 10
			t++
		}
		q.lo = w
	}
	guard, sticky := class.guardSticky()
	up := contextRoundUp(ctx.rounding, negative, guard, sticky, uint32(q.lo&1))
	if inexact {
		events |= roundingDirection(up, negative)
	}
	if up {
		var carry uint64
		q.lo, carry = bits.Add64(q.lo, 1, 0)
		q.hi += carry
		if int64(inlineDigits(q)) > precision {
			q, _ = inlineDivWord(q, 10)
			t++
		}
	}
	if ctx.guarded {
		if q != (uint128{}) && t+int64(inlineDigits(q))-1 > int64(ctx.guards.Emax) {
			return Decimal{}, 0, nil, false
		}
		if tiny {
			events |= Subnormal
			if inexact {
				events |= Underflow
			}
		}
	}
	if t < math.MinInt32 || t > math.MaxInt32 {
		return Decimal{}, 0, nil, false
	}
	result, conditions, err := contextOutcome(inlineDecimal(q, int32(t), negative), events, ctx.traps, op)
	return result, conditions, err, true
}

// inlineDivContext computes divContext's truncated coefficient R′ at t′
// with inlineDivTrunc and hands it, as limbs with a spare carry limb, to the
// shared finisher. The general path reaches the same finisher with the same
// R′, class, t′ and Etiny, or publishes an exact-first probe that
// TestDivExactProbeMatchesGeneral pins to it; unbudgeted charges never
// refuse.
func inlineDivContext(d, other Decimal, ctx *Context, op string) (Decimal, Conditions, error, bool) {
	ideal := int64(d.exponent()) - int64(other.exponent())
	tPrime, etiny := divContextTarget(inlineDigits(d.words), inlineDigits(other.words), ideal, *ctx)
	var q uint128
	var class divHalf
	var ok bool
	if other.words.hi == 0 {
		q, class, ok = inlineDivTrunc(d.words, other.words.lo, ideal-tPrime)
	} else {
		q, class, ok = inlineDivTruncWide(d.words, other.words, ideal-tPrime)
	}
	if !ok {
		return Decimal{}, 0, nil, false
	}
	negative := d.negative() != other.negative()
	if result, conditions, err, ok := finishContextInline(q, class, tPrime, etiny, ideal, negative, ctx, op); ok {
		return result, conditions, err, true
	}
	var buf [6]uint32
	n := 0
	for q != (uint128{}) {
		var rem, digit uint64
		q.hi, rem = bits.Div64(0, q.hi, decimalLimbBase)
		q.lo, digit = bits.Div64(rem, q.lo, decimalLimbBase)
		buf[n] = uint32(digit)
		n++
	}
	result, conditions, err := finishContext(buf[:n], class, tPrime, etiny, ideal, negative, ctx, 0, limits{}, op)
	return result, conditions, err, true
}
