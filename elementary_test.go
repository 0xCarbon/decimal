// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"fmt"
	"math/big"
	"math/rand/v2"
	"testing"
)

// The independent evaluation oracle. It shares no code
// with the production evaluator: Exp reduces by powers of three and bounds
// exp(−u) by alternating partial sums; Ln takes eight directed square roots
// of the normalized mantissa and bounds log(1+t) by alternating partial
// sums; every binary rounding is outward and the final rounding compares
// exact rationals with the decimal grid. An ambiguous oracle interval
// refines; agreement at two precisions is never used as a certificate.

// oracleRat is d as an exact rational.
func oracleRat(d Decimal) *big.Rat {
	r, ok := new(big.Rat).SetString(d.String())
	if !ok {
		panic("oracle: unparsable " + d.String())
	}
	return r
}

func oracleFloat(prec uint, mode big.RoundingMode) *big.Float {
	return new(big.Float).SetPrec(prec).SetMode(mode)
}

func oracleFloatRat(f *big.Float) *big.Rat {
	r, _ := f.Rat(nil)
	return r
}

// oracleExp encloses e^x for |x| ≤ 10^4 at about prec bits.
func oracleExp(x *big.Rat, prec uint) (lo, hi *big.Rat) {
	if x.Sign() == 0 {
		return big.NewRat(1, 1), big.NewRat(1, 1)
	}
	u := new(big.Rat).Abs(x)
	half := big.NewRat(1, 2)
	s := 0
	for u.Cmp(half) > 0 {
		u.Quo(u, big.NewRat(3, 1))
		s++
	}
	// exp(−u) for 0 < u ≤ 1/2 in big.Float at w bits: its alternating terms
	// decrease, so the first omitted term (below the last added one) bounds
	// the tail; trigOracleSeriesError bounds every rounding, and u's own
	// rounding moves exp(−u) by at most 2^−w.
	w := prec + uint(4*s) + 64
	eps := new(big.Float).SetMantExp(big.NewFloat(1), -int(prec)-4*s-16)
	uf := new(big.Float).SetPrec(w).SetRat(u)
	term := new(big.Float).SetPrec(w).SetInt64(1)
	sum := new(big.Float).SetPrec(w).SetInt64(1)
	var n int64
	for n = 1; ; n++ {
		term = new(big.Float).SetPrec(w).Quo(new(big.Float).SetPrec(w).Mul(term, uf), big.NewFloat(float64(n)))
		term.Neg(term)
		sum.Add(sum, term)
		if new(big.Float).Abs(term).Cmp(eps) < 0 {
			break
		}
	}
	t, _ := new(big.Float).Abs(term).Rat(nil)
	bound := new(big.Rat).Add(t, trigOracleSeriesError(3*n+2, w))
	c, _ := sum.Rat(nil)
	below, above := new(big.Rat).Sub(c, bound), new(big.Rat).Add(c, bound)
	work := prec + uint(4*s) + 64
	l := oracleFloat(work, big.ToNegativeInf).SetRat(below)
	h := oracleFloat(work, big.ToPositiveInf).SetRat(above)
	for range s {
		l2 := oracleFloat(work, big.ToNegativeInf).Mul(l, l)
		l = oracleFloat(work, big.ToNegativeInf).Mul(l2, l)
		h2 := oracleFloat(work, big.ToPositiveInf).Mul(h, h)
		h = oracleFloat(work, big.ToPositiveInf).Mul(h2, h)
	}
	if x.Sign() < 0 {
		return oracleFloatRat(l), oracleFloatRat(h)
	}
	one := big.NewFloat(1)
	return oracleFloatRat(oracleFloat(work, big.ToNegativeInf).Quo(one, h)),
		oracleFloatRat(oracleFloat(work, big.ToPositiveInf).Quo(one, l))
}

// oracleSqrt returns a directed square root, verified by exact squaring.
func oracleSqrt(x *big.Float, prec uint, up bool) *big.Float {
	s := oracleFloat(prec, big.ToNearestEven).Sqrt(x)
	ulp := new(big.Float).SetMantExp(big.NewFloat(1), s.MantExp(nil)-int(prec)+1)
	for {
		sq := new(big.Float).SetPrec(2*prec+8).Mul(s, s)
		if c := sq.Cmp(x); up && c >= 0 || !up && c <= 0 {
			return s
		}
		if up {
			s = new(big.Float).SetPrec(prec+8).Add(s, ulp)
		} else {
			s = new(big.Float).SetPrec(prec+8).Sub(s, ulp)
		}
	}
}

// oracleLnMantissa encloses ln m for a rational m in [1, 10] from
// ln m = 256·ln(m^(1/256)) and the alternating series of log(1+t).
func oracleLnMantissa(m *big.Rat, prec uint) (lo, hi *big.Rat) {
	work := prec + 96
	l := oracleFloat(work, big.ToNegativeInf).SetRat(m)
	h := oracleFloat(work, big.ToPositiveInf).SetRat(m)
	for range 8 {
		l = oracleSqrt(l, work, false)
		h = oracleSqrt(h, work, true)
	}
	k := big.NewFloat(256)
	lo = oracleFloatRat(oracleFloat(work, big.ToNegativeInf).Mul(oracleLog1p(l, work, false), k))
	hi = oracleFloatRat(oracleFloat(work, big.ToPositiveInf).Mul(oracleLog1p(h, work, true), k))
	return lo, hi
}

// oracleLog1p bounds log r for r in [1, 2) by the alternating series of
// log(1+t), t = r−1: even partial sums lie below, odd ones above. Each
// term's magnitude is rounded against the bound's direction.
func oracleLog1p(r *big.Float, work uint, upper bool) *big.Float {
	down, up := big.ToNegativeInf, big.ToPositiveInf
	sumMode := down
	if upper {
		sumMode = up
	}
	t := oracleFloat(work, sumMode).Sub(r, big.NewFloat(1))
	sum := oracleFloat(work, sumMode)
	if t.Sign() <= 0 {
		return sum
	}
	eps := new(big.Float).SetMantExp(big.NewFloat(1), -int(work)-16)
	powLo, powHi := oracleFloat(work, down).Set(t), oracleFloat(work, up).Set(t)
	for n := int64(1); ; n++ {
		if n > 1 {
			powLo = oracleFloat(work, down).Mul(powLo, t)
			powHi = oracleFloat(work, up).Mul(powHi, t)
		}
		positive := n%2 == 1
		// A term added to a lower bound, or subtracted from an upper one,
		// is rounded down; the others are rounded up.
		var term *big.Float
		if positive != upper {
			term = oracleFloat(work, up).Quo(powHi, big.NewFloat(float64(n)))
		} else {
			term = oracleFloat(work, down).Quo(powLo, big.NewFloat(float64(n)))
		}
		if positive {
			sum = oracleFloat(work, sumMode).Add(sum, term)
		} else {
			sum = oracleFloat(work, sumMode).Sub(sum, term)
		}
		if term.Cmp(eps) < 0 && positive == upper {
			return sum
		}
	}
}

// oracleLn10 caches ln 10's enclosure per precision within the test run.
var oracleLn10 = map[uint][2]*big.Rat{}

func oracleLnTen(prec uint) (lo, hi *big.Rat) {
	if c, ok := oracleLn10[prec]; ok {
		return c[0], c[1]
	}
	lo, hi = oracleLnMantissa(big.NewRat(10, 1), prec)
	oracleLn10[prec] = [2]*big.Rat{lo, hi}
	return lo, hi
}

// oracleLn encloses ln x for x > 0 with the power of ten kept symbolic.
func oracleLn(x Decimal, prec uint) (lo, hi *big.Rat) {
	v := coefficientViewOf(x)
	digits, _ := arithmeticDigits(&v)
	k := int64(x.exponent()) + int64(digits) - 1
	m := new(big.Rat).SetFrac(oracleCoefficient(x), new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(digits)-1), nil))
	lo, hi = oracleLnMantissa(m, prec+uint(4*digits))
	if k != 0 {
		tl, th := oracleLnTen(prec + 64)
		kr := big.NewRat(k, 1)
		if k > 0 {
			lo.Add(lo, new(big.Rat).Mul(kr, tl))
			hi.Add(hi, new(big.Rat).Mul(kr, th))
		} else {
			lo.Add(lo, new(big.Rat).Mul(kr, th))
			hi.Add(hi, new(big.Rat).Mul(kr, tl))
		}
	}
	return lo, hi
}

// oracleCoefficient is x's coefficient as a big.Int magnitude.
func oracleCoefficient(x Decimal) *big.Int {
	v := coefficientViewOf(x)
	c := new(big.Int)
	base := big.NewInt(1_000_000_000)
	for i := v.count - 1; i >= 0; i-- {
		c.Mul(c, base).Add(c, big.NewInt(int64(v.limb(i))))
	}
	return c
}

// oracleLog10 encloses log10 x as ln x / ln 10.
func oracleLog10(x Decimal, prec uint) (lo, hi *big.Rat) {
	l, h := oracleLn(x, prec)
	tl, th := oracleLnTen(prec + 64)
	if l.Sign() >= 0 {
		lo = new(big.Rat).Quo(l, th)
	} else {
		lo = new(big.Rat).Quo(l, tl)
	}
	if h.Sign() >= 0 {
		hi = new(big.Rat).Quo(h, tl)
	} else {
		hi = new(big.Rat).Quo(h, th)
	}
	return lo, hi
}

// oracleRounded is a correctly rounded unguarded result: sign, coefficient
// and exponent, with the direction relative to the value.
type oracleRounded struct {
	coefficient *big.Int
	exponent    int64
	negative    bool
	increased   bool
}

func (o oracleRounded) String() string {
	s := "+"
	if o.negative {
		s = "-"
	}
	return fmt.Sprintf("%s%sE%d", s, o.coefficient, o.exponent)
}

// enclosureRound rounds a value v in [lo, hi], v different from every decimal
// grid point and midpoint, to p digits in mode; false while the interval
// does not decide it.
func enclosureRound(lo, hi *big.Rat, p int64, mode RoundingMode) (oracleRounded, bool) {
	if lo.Sign() != hi.Sign() || lo.Sign() == 0 {
		return oracleRounded{}, false
	}
	negative := lo.Sign() < 0
	a, b := new(big.Rat).Abs(lo), new(big.Rat).Abs(hi)
	if negative {
		a, b = b, a
	}
	e := oracleAdjusted(a)
	if oracleAdjusted(b) != e {
		return oracleRounded{}, false
	}
	q := oraclePow10(e - p + 1)
	na, fa := oracleFloorFrac(a, q)
	nb, fb := oracleFloorFrac(b, q)
	half := big.NewRat(1, 2)
	if na.Cmp(nb) != 0 || (fa.Cmp(half) < 0) != (fb.Cmp(half) < 0) || fa.Cmp(half) == 0 || fb.Cmp(half) == 0 || fa.Sign() == 0 {
		return oracleRounded{}, false
	}
	above := fa.Cmp(half) > 0
	var away bool
	switch mode {
	case TowardZero:
	case AwayFromZero:
		away = true
	case TowardPositiveInfinity:
		away = !negative
	case TowardNegativeInfinity:
		away = negative
	default: // nearest modes: no ties for these values
		away = above
	}
	n := na
	if away {
		n = new(big.Int).Add(na, big.NewInt(1))
	}
	exponent := e - p + 1
	if n.Cmp(new(big.Int).Exp(big.NewInt(10), big.NewInt(p), nil)) == 0 {
		n.Quo(n, big.NewInt(10))
		exponent++
	}
	return oracleRounded{coefficient: n, exponent: exponent, negative: negative, increased: away != negative}, true
}

// oracleAdjusted is ⌊log10 a⌋ for a > 0.
func oracleAdjusted(a *big.Rat) int64 {
	num, den := a.Num(), a.Denom()
	e := int64(len(num.String())) - int64(len(den.String()))
	for oraclePow10(e).Cmp(a) > 0 {
		e--
	}
	for oraclePow10(e+1).Cmp(a) <= 0 {
		e++
	}
	return e
}

func oraclePow10(e int64) *big.Rat {
	if e >= 0 {
		return new(big.Rat).SetInt(new(big.Int).Exp(big.NewInt(10), big.NewInt(e), nil))
	}
	return new(big.Rat).SetFrac(big.NewInt(1), new(big.Int).Exp(big.NewInt(10), big.NewInt(-e), nil))
}

// oracleFloorFrac is ⌊a/q⌋ and the fraction a/q − ⌊a/q⌋.
func oracleFloorFrac(a, q *big.Rat) (*big.Int, *big.Rat) {
	r := new(big.Rat).Quo(a, q)
	n := new(big.Int).Quo(r.Num(), r.Denom())
	return n, r.Sub(r, new(big.Rat).SetInt(n))
}

// oracleDecide refines an enclosure until it rounds.
func oracleDecide(t *testing.T, enclose func(prec uint) (lo, hi *big.Rat), p int64, mode RoundingMode) oracleRounded {
	t.Helper()
	for prec := uint(4*p + 64); prec < 1<<16; prec *= 2 {
		lo, hi := enclose(prec)
		if lo.Cmp(hi) > 0 {
			t.Fatalf("oracle: inverted enclosure")
		}
		if r, ok := enclosureRound(lo, hi, p, mode); ok {
			return r
		}
	}
	t.Fatalf("oracle: undecided")
	return oracleRounded{}
}

// oracleMatch checks a library result against the oracle's rounding.
func oracleMatch(t *testing.T, name string, got Decimal, conditions Conditions, err error, want oracleRounded) {
	t.Helper()
	if err != nil {
		t.Fatalf("%s: error %v, want %v", name, err, want)
	}
	coefficient := oracleCoefficient(got)
	stripped := new(big.Int).Set(want.coefficient)
	if got.negative() != want.negative || coefficient.Cmp(stripped) != 0 || int64(got.exponent()) != want.exponent {
		t.Fatalf("%s: got %s (coefficient %s E%d), want %s", name, got, coefficient, got.exponent(), want)
	}
	direction := Decreased
	if want.increased {
		direction = Increased
	}
	if conditions != Inexact|Rounded|direction {
		t.Fatalf("%s: conditions %v, want %v", name, conditions, Inexact|Rounded|direction)
	}
}

// TestOracleSelfChecks pins the oracle itself on hand-derived values, so a
// wrong oracle cannot vacuously agree with the evaluator.
func TestOracleSelfChecks(t *testing.T) {
	check := func(name string, lo, hi *big.Rat, want string) {
		t.Helper()
		r, ok := enclosureRound(lo, hi, 20, TowardZero)
		if !ok || r.String() != want {
			t.Fatalf("%s: %v %v, want %s", name, r, ok, want)
		}
	}
	lo, hi := oracleExp(big.NewRat(1, 1), 200)
	check("e", lo, hi, "+27182818284590452353E-19")
	lo, hi = oracleExp(big.NewRat(-1, 1), 200)
	check("1/e", lo, hi, "+36787944117144232159E-20")
	lo, hi = oracleLn(New(2, 0), 200)
	check("ln2", lo, hi, "+69314718055994530941E-20")
	lo, hi = oracleLn(New(1, -3), 200)
	check("ln 0.001", lo, hi, "-69077552789821370520E-19")
	lo, hi = oracleLog10(New(2, 0), 200)
	check("log10 2", lo, hi, "+30102999566398119521E-20")
}

// TestLogConstantTables certifies the ln 10, ln 2 and π
// tables: at every table length each directed enclosure contains the
// oracle's value and agrees with the series fallback's enclosure.
func TestLogConstantTables(t *testing.T) {
	c10lo, c10hi := oracleLnTen(4000)
	c2lo, c2hi := oracleLnMantissa(big.NewRat(2, 1), 4000)
	pilo, pihi := trigOraclePi(4000)
	ev := newEvaluator(Budget{})
	size := 3*(evalConstantLimbs+8) + 64
	st := evalStage{ar: ev.arena(uint64(size * 40)), L: evalConstantLimbs, size: size}
	for L := 1; L < evalConstantLimbs; L++ {
		for _, up := range []bool{false, true} {
			mark := st.scope()
			for _, tc := range []struct {
				name   string
				got    evalNum
				lo, hi *big.Rat
			}{
				{"ln10", ev.ln10(&st, st.buf(&ev), L, up), c10lo, c10hi},
				{"ln2", ev.ln2(&st, st.buf(&ev), L, up), c2lo, c2hi},
				{"pi", ev.pi(&st, st.buf(&ev), L, up), pilo, pihi},
			} {
				g := enclosureRat(tc.got)
				if up && g.Cmp(tc.hi) < 0 || !up && g.Cmp(tc.lo) > 0 {
					t.Fatalf("%s L=%d up=%v excludes the oracle value", tc.name, L, up)
				}
			}
			st.restore(mark)
		}
	}
	// The series fallback beyond the table encloses the same constants.
	lo := ev.ln10(&st, st.buf(&ev), evalConstantLimbs+2, false)
	hi := ev.ln10(&st, st.buf(&ev), evalConstantLimbs+2, true)
	if !ev.ok() || enclosureRat(lo).Cmp(c10lo) > 0 || enclosureRat(hi).Cmp(c10hi) < 0 {
		t.Fatalf("ln10 series excludes the oracle value: %+v", ev.status)
	}
	lo = ev.pi(&st, st.buf(&ev), evalConstantLimbs+2, false)
	hi = ev.pi(&st, st.buf(&ev), evalConstantLimbs+2, true)
	if !ev.ok() || enclosureRat(lo).Cmp(pilo) > 0 || enclosureRat(hi).Cmp(pihi) < 0 {
		t.Fatalf("Machin π excludes the oracle value: %+v", ev.status)
	}
}

// TestSeriesKernelsEncloseOracle checks the directed series kernels at one
// and two limbs, where an omitted analytic tail or a reversed direction is
// a visible fraction of the last place: expPositive, expDirected and
// atanhDirected must enclose the oracle's exp and atanh from the requested
// side.
func TestSeriesKernelsEncloseOracle(t *testing.T) {
	rng := rand.New(rand.NewPCG(66, 7))
	ev := newEvaluator(Budget{})
	size := 64
	st := evalStage{ar: ev.arena(uint64(size * 64)), L: 2, size: size}
	for i := range 3000 {
		L := 1 + i%2
		// a = n/10^k in (0, 1.2] and z in (−0.52, 0.52) with a few digits.
		k := 1 + rng.IntN(12)
		n := 1 + rng.Int64N(int64(12*decimalPowers[min(k, 8)]/10))
		a := New(n, -int32(k))
		if a.Compare(New(12, -1)) > 0 {
			continue
		}
		av := coefficientViewOf(a)
		ad, _ := arithmeticDigits(&av)
		mark := st.scope()
		ab := st.buf(&ev)
		x := ev.load(ab, &av, ad, int64(a.exponent()), rng.IntN(2) == 0, 8, false)
		xr := enclosureRat(x)
		elo, ehi := oracleExp(xr, 200)
		lo := ev.expDirected(&st, st.buf(&ev), x, L, false)
		hi := ev.expDirected(&st, st.buf(&ev), x, L, true)
		if enclosureRat(lo).Cmp(elo) > 0 || enclosureRat(hi).Cmp(ehi) < 0 {
			t.Fatalf("exp(%s) at L=%d: [%s, %s] excludes the oracle", xr.FloatString(20), L, enclosureRat(lo).FloatString(20), enclosureRat(hi).FloatString(20))
		}
		if a.Compare(New(52, -2)) < 0 {
			// atanh z = ln((1+z)/(1−z))/2 from the oracle's logarithm.
			one := big.NewRat(1, 1)
			m := new(big.Rat).Quo(new(big.Rat).Add(one, new(big.Rat).Abs(xr)), new(big.Rat).Sub(one, new(big.Rat).Abs(xr)))
			llo, lhi := oracleLnMantissa(m, 200)
			alo, ahi := new(big.Rat).Quo(llo, big.NewRat(2, 1)), new(big.Rat).Quo(lhi, big.NewRat(2, 1))
			if x.neg {
				alo, ahi = ahi.Neg(ahi), alo.Neg(alo)
			}
			lo := ev.atanhDirected(&st, st.buf(&ev), x, L, false)
			hi := ev.atanhDirected(&st, st.buf(&ev), x, L, true)
			if enclosureRat(lo).Cmp(alo) > 0 || enclosureRat(hi).Cmp(ahi) < 0 {
				t.Fatalf("atanh(%s) at L=%d: [%s, %s] excludes the oracle", xr.FloatString(20), L, enclosureRat(lo).FloatString(20), enclosureRat(hi).FloatString(20))
			}
		}
		st.restore(mark)
	}
	if !ev.ok() {
		t.Fatalf("status %+v", ev.status)
	}
}

// TestExpSeriesEnclosesTailCriticalArguments checks certification at the Taylor
// kernel. For
// u = ⌊√(2·10^(9(L−1)))⌋·10^(−9(L−1)) no halving applies, 1 + u and u²/2
// are exact at L limbs and u²/2 lies just below one unit 10^(−9(L−1)) of
// the sum, so the loop stops there and rounds the sum up by that unit; the
// tail u³/6 + … alone decides whether exp(u) lies above it. expPositive
// must enclose exp(u) from both sides. At L = 7 and 13 the upper bound lies
// within one unit of exp(u), so a bound without the tail excludes it.
func TestExpSeriesEnclosesTailCriticalArguments(t *testing.T) {
	ev := newEvaluator(Budget{})
	size := 64
	st := evalStage{ar: ev.arena(uint64(size * 16)), L: 16, size: size}
	critical := 0
	for L := 2; L <= 16; L++ {
		E := int64(L - 1)
		m := new(big.Int).Sqrt(new(big.Int).Mul(big.NewInt(2), enclosurePow10(E)))
		mark := st.scope()
		u := enclosureNum(st.buf(&ev), m, -E)
		lo, hi := oracleExp(enclosureRat(u), uint(64*L+128))
		gl := ev.expPositive(&st, st.buf(&ev), u, L, false)
		gh := ev.expPositive(&st, st.buf(&ev), u, L, true)
		if !ev.ok() || enclosureRat(gl).Cmp(lo) > 0 || enclosureRat(gh).Cmp(hi) < 0 {
			t.Fatalf("exp(%s·10^-%d) at L=%d: [%s, %s] excludes the oracle (%+v)", m, 9*E, L, enclosureRat(gl).FloatString(9*L), enclosureRat(gh).FloatString(9*L), ev.status)
		}
		if new(big.Rat).Sub(enclosureRat(gh), enclosureUnit(gh, L)).Cmp(lo) < 0 {
			critical++
		}
		st.restore(mark)
	}
	if critical < 2 {
		t.Fatalf("%d tail-critical arguments, want the L = 7 and 13 witnesses", critical)
	}
}

// oracleAtanhSeries encloses atanh z for a rational 0 < z ≤ 1/2 by eight
// exact terms and the geometric remainder z^17/(17·(1 − z²)).
func oracleAtanhSeries(z *big.Rat) (lo, hi *big.Rat) {
	lo = new(big.Rat)
	p, z2 := new(big.Rat).Set(z), new(big.Rat).Mul(z, z)
	for k := range int64(8) {
		lo.Add(lo, new(big.Rat).Quo(p, big.NewRat(2*k+1, 1)))
		p.Mul(p, z2)
	}
	rest := new(big.Rat).Quo(p, new(big.Rat).Mul(big.NewRat(17, 1), new(big.Rat).Sub(big.NewRat(1, 1), z2)))
	return lo, new(big.Rat).Add(lo, rest)
}

// TestAtanhSeriesEnclosesTailCriticalArguments checks certification at the
// guard-limb atanh sum. On the grid
// u = 10^(9(T−W)) of a sum whose top limb lies below 10^(9T), z = m·u with
// m the largest integer such that z³/3 ≤ K·u, for the few K at which z⁵/5
// approaches u: z + z³/3 rounds up to z + K·u with almost no slack, z⁵/5
// lies below u, and the loop stops there with the sum z + (K+1)·u. The
// omitted z⁷/7 + … then decides the bound, and at (L, T) = (12, −2) and
// (14, −3) it carries atanh z past that sum. atanhSeries and atanhDirected
// must enclose atanh z from both sides.
func TestAtanhSeriesEnclosesTailCriticalArguments(t *testing.T) {
	ev := newEvaluator(Budget{})
	size := 64
	st := evalStage{ar: ev.arena(uint64(size * 32)), L: 15, size: size}
	critical := 0
	for _, c := range []struct{ L, T int64 }{{12, -2}, {14, -3}} {
		W := c.L + 1
		inv := enclosurePow10(W - c.T) // 1/u
		inv2, inv4 := new(big.Int).Mul(inv, inv), new(big.Int).Exp(inv, big.NewInt(4), nil)
		// z0 = m0·u with z0⁵/5 ≤ u, and K0 = ⌊z0³/(3u)⌋.
		m0 := enclosureRoot(new(big.Int).Mul(big.NewInt(5), inv4), 5)
		K0 := new(big.Int).Quo(new(big.Int).Exp(m0, big.NewInt(3), nil), new(big.Int).Mul(big.NewInt(3), inv2))
		for dk := int64(-2); dk <= 2; dk++ {
			K := new(big.Int).Add(K0, big.NewInt(dk))
			m := enclosureRoot(new(big.Int).Mul(new(big.Int).Mul(big.NewInt(3), K), inv2), 3)
			mark := st.scope()
			z := enclosureNum(st.buf(&ev), m, c.T-W)
			if z.top() != c.T {
				t.Fatalf("construction: z = %s·10^%d has top %d, want %d", m, 9*(c.T-W), z.top(), c.T)
			}
			lo, hi := oracleAtanhSeries(enclosureRat(z))
			sl := ev.atanhSeries(&st, z, int(W), false)
			sh := ev.atanhSeries(&st, z, int(W), true)
			dl := ev.atanhDirected(&st, st.buf(&ev), z, int(c.L), false)
			dh := ev.atanhDirected(&st, st.buf(&ev), z, int(c.L), true)
			if !ev.ok() || enclosureRat(sl).Cmp(lo) > 0 || enclosureRat(sh).Cmp(hi) < 0 || enclosureRat(dl).Cmp(lo) > 0 || enclosureRat(dh).Cmp(hi) < 0 {
				t.Fatalf("atanh(%s·10^%d) at L=%d excludes the oracle: W sum [%s, %s], L bound [%s, %s] (%+v)", m, 9*(c.T-W), c.L,
					enclosureRat(sl).FloatString(int(9*(W-c.T))), enclosureRat(sh).FloatString(int(9*(W-c.T))),
					enclosureRat(dl).FloatString(int(9*(W-c.T))), enclosureRat(dh).FloatString(int(9*(W-c.T))), ev.status)
			}
			if new(big.Rat).Sub(enclosureRat(sh), enclosureUnit(sh, int(W))).Cmp(lo) < 0 {
				critical++
			}
			st.restore(mark)
		}
	}
	if critical < 2 {
		t.Fatalf("%d tail-critical arguments, want the (12, −2) and (14, −3) witnesses", critical)
	}
}
