// SPDX-License-Identifier: Apache-2.0

package decimal

import "math/bits"

// Certified enclosures of exp, ln and ln 10. Each helper takes its scratch from
// the stage arena in stack order, writes its result into a caller buffer and
// returns the scratch. Directions: up = true encloses from above (toward +∞).

// evalStage is one working precision: L retained limbs for results and
// buffers of size limbs each.
type evalStage struct {
	ar   evalArena
	L    int
	size int
}

func (st *evalStage) buf(ev *evaluator) []uint32 { return ev.take(&st.ar, st.size) }

// scope returns a restore point for the stage's scratch.
func (st *evalStage) scope() []uint32 { return st.ar.free }

func (st *evalStage) restore(free []uint32) { st.ar.free = free }

// evalOne writes the exact endpoint 1 into dst.
func evalOne(dst []uint32) evalNum {
	dst[0] = 1
	return evalNum{m: dst[:1]}
}

// atanhInverse encloses atanh(1/q) = Σ 1/((2j+1)·q^(2j+1)) for q ≥ 3 at L
// limbs. After the last added term P_N/(2N+1) the tail is at most
// Σ_{i>N} P_i = P_N/(q²−1) ≤ P_N, which the upper bound adds. Every sum
// stays in the limb below one, on one grid of unit u, and the loop stops
// on the power P_N < u, so the last term is at most P_N/3 and the tail
// below u/40: the last addition's upward unit already covers both. Without
// the tail addend the bound is one unit tighter and still sound, so no
// enclosure test can detect its omission.
func (ev *evaluator) atanhInverse(st *evalStage, dst []uint32, q uint64, L int, up bool) evalNum {
	mark := st.scope()
	defer st.restore(mark)
	var one [3]uint32
	pb, tb, sb, nb := st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev)
	if !ev.ok() {
		return evalNum{}
	}
	p := ev.divSmall(pb, evalOne(one[:]), q, L, up)
	sum := ev.round(sb, p, L, up)
	for j := uint64(1); ev.ok(); j++ {
		if !ev.charge(1) {
			break
		}
		p = ev.divSmall(pb, p, q*q, L, up)
		term := ev.divSmall(tb, p, 2*j+1, L, up)
		sum = ev.add(nb, sum, term, L, up)
		sb, nb = nb, sb
		if p.top() <= sum.top()-int64(L) {
			break
		}
	}
	if up {
		sum = ev.add(nb, sum, p, L, up)
	}
	return ev.round(dst, sum, L, up)
}

// ln10Fraction and ln2Fraction are the first 1008 fractional digits of
// ln 10 and ln 2 as big-endian base-10⁹ limbs. They are constants, not a
// cache: an enclosure truncates them and adds one unit of the last kept
// limb (the omitted digits of an irrational constant are nonzero), and
// TestLogConstantTables certifies them against the series below and the
// independent oracle. Longer enclosures come from the series.
var ln10Fraction = [evalConstantLimbs]uint32{
	302585092, 994045684, 17991454, 684364207, 601101488, 628772976, 33327900, 967572609,
	677352480, 235997205, 89598298, 341967784, 42286248, 633409525, 465082806, 756666287,
	369098781, 689482907, 208325554, 680843799, 894826233, 198528393, 505308965, 377732628,
	846163366, 222287698, 219886746, 543667474, 404243274, 365155048, 934314939, 391479619,
	404400222, 105101714, 174800368, 808401264, 708068556, 774321622, 835522011, 480466371,
	565912137, 345074785, 694768346, 361679210, 180644507, 64800027, 750268491, 674655058,
	685693567, 342067058, 113642922, 455440575, 892572420, 824131469, 568901675, 894025677,
	631135691, 929203337, 658714166, 23010570, 308963457, 207544037, 84746994, 16826928,
	280848118, 428931484, 852494864, 487192780, 967627127, 577539702, 766860595, 249671667,
	418348570, 442250719, 796500471, 495105049, 221477656, 763693866, 297697952, 211071826,
	454973477, 266242570, 942932258, 279850258, 550978526, 538320760, 672631716, 430950599,
	508780752, 371033310, 119785754, 733154142, 180842754, 386359177, 811705430, 982748238,
	504564801, 909561029, 929182431, 823752535, 770975053, 956518769, 751037497, 88869218,
	20518933, 950723853, 920514463, 419726528, 728696511, 86257149, 219884997, 874887377,
}

var ln2Fraction = [evalConstantLimbs]uint32{
	693147180, 559945309, 417232121, 458176568, 75500134, 360255254, 120680009, 493393621,
	969694715, 605863326, 996418687, 542001481, 20570685, 733685520, 235758130, 557032670,
	751635075, 961930727, 570828371, 435190307, 38623891, 673471123, 350115364, 497955239,
	120475172, 681574932, 65155524, 734139525, 882950453, 7095326, 366642654, 104239157,
	814952043, 740430385, 500801944, 170641671, 518644712, 839968171, 784546957, 26271631,
	64546150, 257207402, 481637773, 389638550, 695260668, 341137273, 873722928, 956493547,
	25762652, 98859693, 201965058, 554764703, 306793654, 432547632, 744951250, 406069438,
	147104689, 946506220, 167720424, 524529612, 687946546, 193165174, 681392672, 504103802,
	546259656, 869144192, 871608293, 803172714, 367782654, 877566485, 85674077, 648451464,
	439940461, 422603193, 96735402, 574446070, 308096085, 47486638, 523138181, 676751438,
	667476647, 890881437, 141985494, 231519973, 548803751, 658612753, 529166100, 71053558,
	249879414, 729509293, 113897155, 998205654, 392871700, 72180857, 610252368, 892132449,
	713893203, 784393530, 887748259, 701715591, 70882368, 362758984, 258918535, 302436342,
	143670611, 892367891, 923723146, 723217205, 340164925, 687274778, 234453534, 764811494,
}

const evalConstantLimbs = 112

// piFraction is the first 1008 fractional digits of π, a constant
// certified like the logarithm tables (TestLogConstantTables).
var piFraction = [evalConstantLimbs]uint32{
	141592653, 589793238, 462643383, 279502884, 197169399, 375105820, 974944592, 307816406,
	286208998, 628034825, 342117067, 982148086, 513282306, 647093844, 609550582, 231725359,
	408128481, 117450284, 102701938, 521105559, 644622948, 954930381, 964428810, 975665933,
	446128475, 648233786, 783165271, 201909145, 648566923, 460348610, 454326648, 213393607,
	260249141, 273724587, 6606315, 588174881, 520920962, 829254091, 715364367, 892590360,
	11330530, 548820466, 521384146, 951941511, 609433057, 270365759, 591953092, 186117381,
	932611793, 105118548, 74462379, 962749567, 351885752, 724891227, 938183011, 949129833,
	673362440, 656643086, 21394946, 395224737, 190702179, 860943702, 770539217, 176293176,
	752384674, 818467669, 405132000, 568127145, 263560827, 785771342, 757789609, 173637178,
	721468440, 901224953, 430146549, 585371050, 792279689, 258923542, 19956112, 129021960,
	864034418, 159813629, 774771309, 960518707, 211349999, 998372978, 49951059, 731732816,
	96318595, 24459455, 346908302, 642522308, 253344685, 35261931, 188171010, 3137838,
	752886587, 533208381, 420617177, 669147303, 598253490, 428755468, 731159562, 863882353,
	787593751, 957781857, 780532171, 226806613, 1927876, 611195909, 216420198, 938095257,
}

// evalConstantKind selects a constant table.
type evalConstantKind uint8

const (
	evalLn10 evalConstantKind = iota
	evalLn2
	evalPi
)

// evalConstant encloses a tabled constant at L limbs.
func (ev *evaluator) evalConstant(dst []uint32, kind evalConstantKind, L int, up bool) evalNum {
	var whole uint32
	switch kind {
	case evalLn10:
		whole = 2
	case evalPi:
		whole = 3
	}
	n := L
	if whole != 0 {
		n--
	}
	if !ev.charge(uint64(n) + 1) {
		return evalNum{}
	}
	for i := range n {
		switch kind {
		case evalLn10:
			dst[i] = ln10Fraction[n-1-i]
		case evalLn2:
			dst[i] = ln2Fraction[n-1-i]
		default:
			dst[i] = piFraction[n-1-i]
		}
	}
	count := n
	if whole != 0 {
		dst[n] = whole
		count++
	}
	return ev.settle(dst, count, -int64(n), false, true, L, up)
}

// ln10 encloses ln 10 at L limbs: from the table, or as
// 6·atanh(1/3) + 2·atanh(1/9) under the shared meter.
func (ev *evaluator) ln10(st *evalStage, dst []uint32, L int, up bool) evalNum {
	if L < evalConstantLimbs {
		return ev.evalConstant(dst, evalLn10, L, up)
	}
	mark := st.scope()
	defer st.restore(mark)
	a3, a9, t3, t9, sum := st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev)
	if !ev.ok() {
		return evalNum{}
	}
	var six, two [3]uint32
	x := ev.atanhInverse(st, a3, 3, L+1, up)
	y := ev.atanhInverse(st, a9, 9, L+1, up)
	x = ev.mul(t3, x, evalSmall(six[:], 6, false), L+1, up)
	y = ev.mul(t9, y, evalSmall(two[:], 2, false), L+1, up)
	return ev.round(dst, ev.add(sum, x, y, L+1, up), L, up)
}

// ln2 encloses ln 2 at L limbs: from the table, or as 2·atanh(1/3).
func (ev *evaluator) ln2(st *evalStage, dst []uint32, L int, up bool) evalNum {
	if L < evalConstantLimbs {
		return ev.evalConstant(dst, evalLn2, L, up)
	}
	mark := st.scope()
	defer st.restore(mark)
	a, s := st.buf(ev), st.buf(ev)
	if !ev.ok() {
		return evalNum{}
	}
	x := ev.atanhInverse(st, a, 3, L+1, up)
	return ev.round(dst, ev.add(s, x, x, L+1, up), L, up)
}

// evalExpDepth is h: arguments are halved to at most 2^−h before the
// Taylor sum, trading about 3.3L/h terms for h squarings.
func evalExpDepth(L int) int64 {
	h := int64(1)
	for (h+1)*(h+1) <= int64(8*L) {
		h++
	}
	return h
}

// expPositive encloses exp(a) for an exact a ≥ 0 at L limbs. With
// u = a/2^s ≤ 2^−h ≤ 1/2, the Taylor tail after the last added term
// t_N = u^N/N! is at most t_N·(u/(N+1))/(1−u/(N+2)) ≤ t_N, which the upper
// bound adds; the sum is then squared s times in the same direction. The
// loop stops on a term below one unit of the sum, which the tail can carry
// the true value past (TestExpSeriesEnclosesTailCriticalArguments).
func (ev *evaluator) expPositive(st *evalStage, dst []uint32, a evalNum, L int, up bool) evalNum {
	if a.isZero() {
		dst[0] = 1
		return evalNum{m: dst[:1]}
	}
	h := evalExpDepth(L)
	// a < 10^(adj+1) < 2^(10(adj+1)/3), so s halvings give u < 2^−h.
	adj := a.adjusted()
	var s int64
	if adj >= -1 {
		s = h + (10*(adj+1)+2)/3
	} else {
		s = max(0, h-3*(-adj-1))
	}
	// The s squarings amplify the relative error by 2^s, almost one limb per
	// 30 squarings. Rounding that to the nearest limb leaves at most 2^15
	// uncovered, which the stage's spare digits absorb; truncating would
	// leave up to 2^29 and force a second stage at precisions of several
	// hundred digits.
	W := L + int((s+14)/30)
	mark := st.scope()
	defer st.restore(mark)
	ub, sb, nb, tb, pb := st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev)
	if !ev.ok() || !ev.charge(uint64(s)) {
		return evalNum{}
	}
	u := ev.round(ub, a, W, up)
	for left := s; left > 0 && ev.ok(); left -= 30 {
		u = ev.divSmall(ub, u, 1<<min(left, 30), W, up)
	}
	var one [3]uint32
	sum := ev.add(sb, evalOne(one[:]), u, W, up)
	term := ev.round(tb, u, W, up)
	for j := uint64(2); ev.ok(); j++ {
		if !ev.charge(1) {
			break
		}
		term = ev.divSmall(tb, ev.mul(pb, term, u, W, up), j, W, up)
		sum = ev.add(nb, sum, term, W, up)
		sb, nb = nb, sb
		if term.isZero() || term.top() <= sum.top()-int64(W) {
			break
		}
	}
	if up {
		sum = ev.add(nb, sum, term, W, up)
		sb, nb = nb, sb
	}
	for range s {
		if !ev.charge(1) {
			break
		}
		sum = ev.mul(pb, sum, sum, W, up)
		sum = ev.round(sb, sum, W, up)
	}
	return ev.round(dst, sum, L, up)
}

// expDirected encloses exp(a) for an exact signed a: exp(−b) = 1/exp(b)
// with the opposite inner direction.
func (ev *evaluator) expDirected(st *evalStage, dst []uint32, a evalNum, L int, up bool) evalNum {
	if !a.neg {
		return ev.expPositive(st, dst, a, L, up)
	}
	mark := st.scope()
	defer st.restore(mark)
	eb, sb := st.buf(ev), st.buf(ev)
	if !ev.ok() {
		return evalNum{}
	}
	e := ev.expPositive(st, eb, a.negate(), L+1, !up)
	var one [3]uint32
	return ev.div(dst, sb, evalOne(one[:]), e, L, up)
}

// evalRange reports a value certainly outside every representable
// magnitude, before any reduction proportional to its exponent.
type evalRange uint8

const (
	evalInRange evalRange = iota
	evalHuge              // exp(z) > 10^(4·10^10)
	evalTiny              // exp(z) < 10^(−4·10^10)
	evalWide              // the enclosure is too wide to reduce; refine
)

// evalRangeDigits is the adjusted exponent at which |z| ≥ 10^11 puts
// exp(z) beyond 10^±(4·10^10): no p-digit result of a uint32 precision has
// a stored or guarded exponent there.
const evalRangeDigits = 11

// expEnclose encloses exp(z) for z in [zlo, zhi] at L limbs: z = k·ln10+r
// with an integer k chosen from zlo, exp(z) = 10^k·exp(r).
func (ev *evaluator) expEnclose(st *evalStage, lo, hi []uint32, zlo, zhi evalNum, L int) (evalNum, evalNum, evalRange) {
	switch {
	case !zlo.isZero() && !zlo.neg && zlo.adjusted() >= evalRangeDigits:
		return evalNum{}, evalNum{}, evalHuge
	case !zhi.isZero() && zhi.neg && zhi.adjusted() >= evalRangeDigits:
		return evalNum{}, evalNum{}, evalTiny
	case !zlo.isZero() && zlo.adjusted() >= evalRangeDigits, !zhi.isZero() && zhi.adjusted() >= evalRangeDigits:
		return evalNum{}, evalNum{}, evalWide
	}
	mark := st.scope()
	defer st.restore(mark)
	rl, rh, cl, ch, kl, kh := st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev)
	el, eh := st.buf(ev), st.buf(ev)
	if !ev.ok() {
		return evalNum{}, evalNum{}, evalInRange
	}
	k := evalNearestLn10(zlo)
	rlo, rhi := zlo, zhi
	if k != 0 {
		var kb [3]uint32
		K := evalSmall(kb[:], uint64(max(k, -k)), k < 0)
		// |k| < 5·10^10 spans at most two limbs of the absolute error.
		Lc := L + len(K.m)
		c0 := ev.ln10(st, cl, Lc, false)
		c1 := ev.ln10(st, ch, Lc, true)
		// k·ln10 ∈ [K·c0, K·c1] for k > 0 and [K·c1, K·c0] for k < 0.
		klo, khi := ev.mul(kl, K, c0, Lc+3, false), ev.mul(kh, K, c1, Lc+3, true)
		if k < 0 {
			klo, khi = ev.mul(kl, K, c1, Lc+3, false), ev.mul(kh, K, c0, Lc+3, true)
		}
		rlo = ev.add(rl, zlo, khi.negate(), L+1, false)
		rhi = ev.add(rh, zhi, klo.negate(), L+1, true)
	}
	elo := ev.expDirected(st, el, rlo, L, false)
	ehi := ev.expDirected(st, eh, rhi, L, true)
	return ev.scale(lo, elo, k), ev.scale(hi, ehi, k), evalInRange
}

// evalNearestLn10 is an integer near z/ln 10 for |z| < 10^11, from z's
// micro units in exact integer arithmetic; any nearby integer is correct,
// since the enclosure of z − k·ln 10 is certified independently.
func evalNearestLn10(z evalNum) int64 {
	if z.isZero() || z.adjusted() < 0 {
		return 0
	}
	var whole, frac uint64
	for i := z.top() - 1; i >= max(z.e, -1); i-- {
		limb := uint64(z.m[i-z.e])
		switch {
		case i >= 0:
			for range i {
				limb *= decimalLimbBase
			}
			whole += limb
		default:
			frac = limb
		}
	}
	micro := whole*1_000_000 + frac/1000
	// k = round(micro·1000/2302585093), with ln 10 ≈ 2.302585093.
	hi, lo := bits.Mul64(micro, 1000)
	lo, carry := bits.Add64(lo, 1_151_292_546, 0)
	k, _ := bits.Div64(hi+carry, lo, 2_302_585_093)
	if z.neg {
		return -int64(k)
	}
	return int64(k)
}

// atanhDirected encloses atanh(z) for an exact |z| ≤ 0.52 at L limbs: the
// series at one guard limb, rounded once.
func (ev *evaluator) atanhDirected(st *evalStage, dst []uint32, z evalNum, L int, up bool) evalNum {
	if z.isZero() {
		return evalNum{}
	}
	if z.neg {
		return ev.atanhDirected(st, dst, z.negate(), L, !up).negate()
	}
	mark := st.scope()
	defer st.restore(mark)
	return ev.round(dst, ev.atanhSeries(st, z, L+1, up), L, up)
}

// atanhSeries encloses atanh(z) for an exact 0 < z ≤ 0.52 at W limbs in
// the stage's scratch, which the caller scopes. After the last added term
// z^(2N+1)/(2N+1) the tail is at most that term·z²/(1−z²), below the term
// itself, which the upper bound adds: the loop stops on a term below one
// unit of the sum, not on the power, so that term can lie just below the
// unit and the tail can carry the true value past it
// (TestAtanhSeriesEnclosesTailCriticalArguments).
func (ev *evaluator) atanhSeries(st *evalStage, z evalNum, W int, up bool) evalNum {
	zb, pb, qb, tb, sb, nb := st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev)
	if !ev.ok() {
		return evalNum{}
	}
	z2 := ev.mul(zb, z, z, W, up)
	p := ev.round(pb, z, W, up)
	sum := ev.round(sb, z, W, up)
	var term evalNum
	for j := uint64(1); ev.ok(); j++ {
		if !ev.charge(1) {
			break
		}
		p = ev.round(pb, ev.mul(qb, p, z2, W, up), W, up)
		term = ev.divSmall(tb, p, 2*j+1, W, up)
		sum = ev.add(nb, sum, term, W, up)
		sb, nb = nb, sb
		if term.isZero() || term.top() <= sum.top()-int64(W) {
			break
		}
	}
	if up {
		sum = ev.add(nb, sum, term, W, up)
	}
	return sum
}

// lnInput is the scale-free logarithm reduction of x = C·10^e10 > 0:
// x = t·2^j·10^k with t·2^j = C·10^tExp in [1/√10, √10), j ∈ {−1, 0, 1}
// placing t in [0.632, 1.582), and the number of zero limbs that t − 1 has
// below its point, so its significant limbs load exactly without expanding
// any exponent gap.
type lnInput struct {
	v      coefficientView
	digits uint64
	tExp   int64
	k      int64
	j      int64
	zeros  int // leading zero limbs of |t − 1|
	unit   bool
}

// newLnInput reduces x = C·10^e10 > 0, charging its digit scan.
func (ev *evaluator) newLnInput(v coefficientView, digits uint64, e10 int64) lnInput {
	in := lnInput{v: v, digits: digits, k: e10 + int64(digits) - 1, tExp: -int64(digits) + 1}
	lead := evalLead9(&in.v, digits)
	below := lead >= 316_227_767 // t ≥ √10: use t/10 in [0.316, 1)
	if below {
		in.k++
		in.tExp--
	}
	switch {
	case !below && lead > 141_421_356:
		in.j = 1 // t in (1.414, 3.163): halve
	case below && lead < 707_106_781:
		in.j = -1 // t in [0.316, 0.708): double
	}
	// Count the leading zero digits of |t−1| after the point: zeros after a
	// leading 1, or nines below one. Stop at the first other digit.
	var run uint64
	if below || lead < 200_000_000 {
		want := uint32(0)
		first := digits - 1 // position below the leading 1
		if below {
			want, first = 9, digits
		}
		if !ev.charge(first + 1) { // one step per digit visited
			return in
		}
		for pos := first; pos > 0 && quantizeDigit(&in.v, pos-1) == want; pos-- {
			run++
		}
		in.unit = !below && run == digits-1
	}
	in.zeros = int(run / 9)
	return in
}

// evalLead9 is C's leading nine digits, zero padded.
func evalLead9(v *coefficientView, digits uint64) uint64 {
	var lead uint64
	for i := range uint64(9) {
		lead *= 10
		if i < digits {
			lead += uint64(quantizeDigit(v, digits-1-i))
		}
	}
	return lead
}

// lnEnclose encloses ln x = ln t + j·ln 2 + k·ln 10 at L limbs. With
// d = t−1 and z = d/(2+d), ln t = 2·atanh(z) and |z| < 0.226 (the atanh
// tail needs only z² ≤ 1/2); z is increasing in d.
func (ev *evaluator) lnEnclose(st *evalStage, lo, hi []uint32, in *lnInput, L int) (evalNum, evalNum) {
	mark := st.scope()
	defer st.restore(mark)
	tl, th, dl, dh, nl, nh, ql, qh, sb := st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev)
	al, ah := st.buf(ev), st.buf(ev)
	if !ev.ok() {
		return evalNum{}, evalNum{}
	}
	var alo, ahi evalNum
	if !in.unit {
		Lt := L + in.zeros + 1
		var one, two [3]uint32
		minus := evalSmall(one[:], 1, true)
		tlo := ev.load(tl, &in.v, in.digits, in.tExp, false, Lt, false)
		thi := ev.load(th, &in.v, in.digits, in.tExp, false, Lt, true)
		switch in.j {
		case 1:
			tlo, thi = ev.divSmall(tl, tlo, 2, Lt, false), ev.divSmall(th, thi, 2, Lt, true)
		case -1:
			tlo, thi = ev.add(dl, tlo, tlo, Lt, false), ev.add(dh, thi, thi, Lt, true)
			tlo, thi = ev.round(tl, tlo, Lt, false), ev.round(th, thi, Lt, true)
		}
		dlo := ev.add(dl, tlo, minus, L+1, false)
		dhi := ev.add(dh, thi, minus, L+1, true)
		twoN := evalSmall(two[:], 2, false)
		// z(dlo) from below: a larger denominator when dlo ≥ 0.
		den := ev.add(nl, twoN, dlo, L+1, !dlo.neg)
		zlo := ev.div(ql, sb, dlo, den, L, false)
		den = ev.add(nh, twoN, dhi, L+1, dhi.neg)
		zhi := ev.div(qh, sb, dhi, den, L, true)
		alo = ev.atanhDirected(st, al, zlo, L, false)
		ahi = ev.atanhDirected(st, ah, zhi, L, true)
		alo = ev.add(tl, alo, alo, L, false)
		ahi = ev.add(th, ahi, ahi, L, true)
	}
	if in.j != 0 {
		// j·ln 2 lies in [j·c0, j·c1] for j = 1 and [j·c1, j·c0] for j = −1.
		c0, c1 := ev.ln2(st, dl, L+1, false), ev.ln2(st, dh, L+1, true)
		if in.j < 0 {
			c0, c1 = c1.negate(), c0.negate()
		}
		alo = ev.add(nl, alo, c0, L+1, false)
		ahi = ev.add(nh, ahi, c1, L+1, true)
		alo, ahi = ev.round(tl, alo, L+1, false), ev.round(th, ahi, L+1, true)
	}
	if in.k == 0 {
		return ev.round(lo, alo, L, false), ev.round(hi, ahi, L, true)
	}
	var kb [3]uint32
	K := evalSmall(kb[:], uint64(max(in.k, -in.k)), false)
	Lc := L + len(K.m)
	c0 := ev.ln10(st, dl, Lc, false)
	c1 := ev.ln10(st, dh, Lc, true)
	klo, khi := ev.mul(nl, K, c0, Lc+3, false), ev.mul(nh, K, c1, Lc+3, true)
	if in.k < 0 {
		klo, khi = ev.mul(nl, K, c1, Lc+3, true).negate(), ev.mul(nh, K, c0, Lc+3, false).negate()
	}
	return ev.add(lo, alo, klo, L, false), ev.add(hi, ahi, khi, L, true)
}

// log10Enclose encloses log10 x = k + ln t / ln 10 at L limbs.
func (ev *evaluator) log10Enclose(st *evalStage, lo, hi []uint32, in *lnInput, L int) (evalNum, evalNum) {
	mark := st.scope()
	defer st.restore(mark)
	ll, lh, cl, ch, ql, qh, sb := st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev), st.buf(ev)
	if !ev.ok() {
		return evalNum{}, evalNum{}
	}
	t := *in
	t.k = 0
	llo, lhi := ev.lnEnclose(st, ll, lh, &t, L)
	c0 := ev.ln10(st, cl, L+1, false)
	c1 := ev.ln10(st, ch, L+1, true)
	// A nonnegative numerator is smallest over the larger ln 10.
	den := c1
	if llo.neg {
		den = c0
	}
	qlo := ev.div(ql, sb, llo, den, L, false)
	den = c0
	if lhi.neg {
		den = c1
	}
	qhi := ev.div(qh, sb, lhi, den, L, true)
	var kb [3]uint32
	K := evalSmall(kb[:], uint64(max(in.k, -in.k)), in.k < 0)
	return ev.add(lo, qlo, K, L, false), ev.add(hi, qhi, K, L, true)
}

// evalCmp compares signed endpoints; the caller charges the scan.
func evalCmp(a, b evalNum) int {
	sa, sb := evalSign(a), evalSign(b)
	if sa != sb {
		if sa < sb {
			return -1
		}
		return 1
	}
	c := cmpMag(a, b)
	if sa < 0 {
		return -c
	}
	return c
}

func evalSign(x evalNum) int {
	switch {
	case x.isZero():
		return 0
	case x.neg:
		return -1
	default:
		return 1
	}
}
