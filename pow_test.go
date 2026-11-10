// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"errors"
	"fmt"
	"math"
	"math/big"
	"math/rand/v2"
	"strings"
	"testing"
)

// powGuardsOracle is the oracle's view of optional exponent guards.
type powGuardsOracle struct {
	on         bool
	emin, emax int64
}

// powExactRat is x^n as an exact rational for x = coefficient·10^e
// (coefficient signed, nonzero), computed with big.Int.Exp.
func powExactRat(coefficient *big.Int, e int64, n int64) *big.Rat {
	m := n
	if m < 0 {
		m = -m
	}
	power := new(big.Int).Exp(new(big.Int).Abs(coefficient), big.NewInt(m), nil)
	v := new(big.Rat).Mul(new(big.Rat).SetInt(power), pow10Rat(m*e))
	if n < 0 {
		v.Inv(v)
	}
	if coefficient.Sign() < 0 && m%2 == 1 {
		v.Neg(v)
	}
	return v
}

// powAdjusted is ⌊log10 |v|⌋ for a nonzero rational, from digit lengths
// and one comparison.
func powAdjusted(v *big.Rat) int64 {
	a := new(big.Rat).Abs(v)
	num, den := a.Num(), a.Denom()
	guess := int64(len(num.String())) - int64(len(den.String()))
	// 10^guess ≤ a < 10^(guess+1) or one below.
	if a.Cmp(pow10Rat(guess)) < 0 {
		guess--
	}
	return guess
}

// powOracle rounds the exact rational q = x^n to p digits in mode under
// optional guards, independently of the library: the rounding exponent
// from the adjusted exponent, one rounding of |q|·10^−t with big.Rat, the
// GDA ideal-exponent rule for exact results (strip toward ideal, Rounded
// above it), exponent guards (Bmax on overflow, Subnormal and Underflow),
// and the reported rounding direction.
func powOracle(q *big.Rat, ideal, p int64, mode RoundingMode, g powGuardsOracle) divExpect {
	v := new(big.Rat).Abs(q)
	a := powAdjusted(v)
	bmax := func() divExpect {
		if mode == Exact {
			return divExpect{refused: true}
		}
		nines := new(big.Int).Sub(new(big.Int).Exp(big.NewInt(10), big.NewInt(p), nil), big.NewInt(1))
		return divExpect{coefficient: nines, exponent: g.emax - p + 1, conditions: Overflow | Inexact | Rounded | divOracleDirection(q, nines, g.emax-p+1)}
	}
	if g.on && a > g.emax {
		return bmax()
	}
	t := a - p + 1
	if g.on {
		t = max(t, g.emin-(p-1))
	}
	r, inexact := oracleRound(new(big.Rat).Mul(v, pow10Rat(-t)), mode, q.Sign() < 0)
	if mode == Exact && inexact {
		return divExpect{refused: true}
	}
	var c Conditions
	switch {
	case inexact:
		c = Inexact | Rounded
	case t > ideal:
		c = Rounded
	}
	if !inexact {
		for t < ideal && r.Sign() != 0 && new(big.Int).Mod(r, big.NewInt(10)).Sign() == 0 {
			r.Quo(r, big.NewInt(10))
			t++
		}
	}
	if divDigitsOf(r) > p {
		r.Quo(r, big.NewInt(10))
		t++
	}
	if g.on && r.Sign() != 0 && t+divDigitsOf(r)-1 > g.emax {
		return bmax()
	}
	if inexact {
		c |= divOracleDirection(q, r, t)
	}
	if g.on && a < g.emin {
		c |= Subnormal
		if inexact {
			c |= Underflow
		}
	}
	return divExpect{coefficient: r, exponent: t, conditions: c}
}

// powOracleBare is bare Pow: C^n at n·e for n ≥ 0 (the unstripped
// repeated-multiplication cohort). For n = −m < 0 it factors C = 2^i·5^j·r:
// the reciprocal terminates iff r = 1, and then 1/x^m = 5^(im)·2^(jm) /
// 10^(im+jm+me), whose coefficient with its min(im, jm) factors of ten
// removed sits at the largest exponent not above the ideal −m·e (Div's
// rule), −max(im, jm) − m·e.
func powOracleBare(coefficient *big.Int, e, n int64) (divExpect, bool) {
	c := new(big.Int).Abs(coefficient)
	if n >= 0 {
		return divExpect{coefficient: new(big.Int).Exp(c, big.NewInt(n), nil), exponent: n * e}, true
	}
	m := -n
	var i, j int64
	two, five := big.NewInt(2), big.NewInt(5)
	for new(big.Int).Mod(c, two).Sign() == 0 {
		c.Quo(c, two)
		i++
	}
	for new(big.Int).Mod(c, five).Sign() == 0 {
		c.Quo(c, five)
		j++
	}
	if c.Cmp(big.NewInt(1)) != 0 {
		return divExpect{}, false
	}
	common := min(i*m, j*m)
	k := new(big.Int).Mul(new(big.Int).Exp(five, big.NewInt(i*m-common), nil), new(big.Int).Exp(two, big.NewInt(j*m-common), nil))
	return divExpect{coefficient: k, exponent: -max(i*m, j*m) - m*e}, true
}

// powIdeal is the exponent exact context results strip toward: n·e, the
// cohort exponent for n ≥ 0 and the ideal −|n|·e of 1/x^|n| for n < 0.
func powIdeal(e, n int64) int64 { return n * e }

func powDecimal(c *big.Int, e int64) Decimal {
	return MustParse(fmt.Sprintf("%sE%d", c, e))
}

// powOperandFor draws a signed coefficient: random digits, a power of 2
// or 5 (terminating reciprocals), a value near a power of ten, or one of
// those with trailing zeros.
func powOperandFor(r *rand.Rand, maxDigits int) *big.Int {
	var c *big.Int
	switch r.IntN(6) {
	case 0:
		c = new(big.Int).Exp(big.NewInt(2), big.NewInt(int64(r.IntN(60))), nil)
	case 1:
		c = new(big.Int).Exp(big.NewInt(5), big.NewInt(int64(r.IntN(30))), nil)
	case 2:
		c = new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(1+r.IntN(maxDigits))), nil)
		c.Add(c, big.NewInt(int64(r.IntN(5)-2)))
		if c.Sign() <= 0 {
			c.SetInt64(1)
		}
	default:
		c = randomDigits(r, 1+r.IntN(maxDigits))
	}
	if r.IntN(4) == 0 {
		c.Mul(c, new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(r.IntN(6))), nil))
	}
	if r.IntN(3) == 0 {
		c.Neg(c)
	}
	return c
}

// powCheck compares one context outcome with the oracle.
func powCheck(t *testing.T, label string, got Decimal, conditions Conditions, err error, want divExpect, negative bool) {
	t.Helper()
	checkDivOutcome(t, label, got, conditions, err, want, negative)
}

var allModes = []RoundingMode{TiesToEven, TiesAwayFromZero, TiesTowardZero, TowardZero, AwayFromZero, TowardPositiveInfinity, TowardNegativeInfinity, Exact}

// TestPowAgainstBigOracle checks Pow in every mode against math/big:
// over random operands (random digits, powers of 2 and 5, values near
// powers of ten, trailing zeros, negatives) and exponents −40…40 with a
// few up to ±400, in all eight modes at random precisions, PowWithContext
// equals the big.Int.Exp / big.Rat oracle rounded independently in value,
// exponent, Conditions and direction, and bare Pow equals the exact
// cohort or refuses exactly when the reciprocal does not terminate. At
// least 20% of the context cases are decided by a truncated level and at
// least 10% by the exact path, so neither is vacuous.
func TestPowAgainstBigOracle(t *testing.T) {
	r := rand.New(rand.NewPCG(53, 41))
	cases := 8000
	if testing.Short() {
		cases = 1500
	}
	var ziv, exact int
	for i := range cases {
		c := powOperandFor(r, 25)
		e := int64(r.IntN(21) - 10)
		n := int64(r.IntN(81) - 40)
		if r.IntN(20) == 0 {
			n = int64(r.IntN(801) - 400)
		}
		p := int64(1 + r.IntN(40))
		mode := allModes[r.IntN(len(allModes))]
		x := powDecimal(c, e)
		label := fmt.Sprintf("case %d: (%v)^%d p=%d %v", i, x, n, p, mode)
		ctx := mustContext(t, uint32(p), mode)
		cnt := &powCount{}
		got, conditions, err := x.powContext(int32(n), ctx, limits{}, "PowWithContext", cnt)
		switch {
		case c.Sign() == 0:
		case len(cnt.levels) > 0 && !cnt.exact:
			ziv++
		case cnt.exact:
			exact++
		}
		negative := c.Sign() < 0 && n%2 != 0
		if n < 0 && c.Sign() == 0 {
			if !errors.Is(err, ErrDivisionByZero) {
				t.Fatalf("%s: %v", label, err)
			}
			continue
		}
		q := powExactRat(c, e, n)
		want := powOracle(q, powIdeal(e, n), p, mode, powGuardsOracle{})
		powCheck(t, label, got, conditions, err, want, negative)
		bare, err := x.Pow(int32(n))
		wantBare, terminates := powOracleBare(c, e, n)
		if !terminates {
			var ce *Error
			if !errors.As(err, &ce) || ce.Code != 0 || ce.Condition != Inexact || !strings.Contains(ce.Remedy, "PowWithContext") || !isZeroValue(bare) {
				t.Fatalf("%s bare: (%v, %v), want the PowWithContext refusal", label, bare, err)
			}
			continue
		}
		powCheck(t, label+" bare", bare, 0, err, wantBare, negative)
	}
	if ziv < cases/5 || exact < cases/10 {
		t.Fatalf("vacuous mix: %d truncated, %d exact of %d", ziv, exact, cases)
	}
}

func mustGuarded(t *testing.T, p uint32, mode RoundingMode, emin, emax int32, traps Conditions) Context {
	t.Helper()
	ctx, err := NewContext(p, mode, &ExponentGuards{Emin: emin, Emax: emax}, traps)
	if err != nil {
		t.Fatal(err)
	}
	return ctx
}

// powRoot is ⌊v^(1/n)⌋ by bisection on big.Int.
func powRoot(v *big.Int, n int64) *big.Int {
	lo, hi := big.NewInt(0), new(big.Int).Lsh(big.NewInt(1), uint(v.BitLen()/int(n)+1))
	one := big.NewInt(1)
	for new(big.Int).Sub(hi, lo).Cmp(one) > 0 {
		mid := new(big.Int).Rsh(new(big.Int).Add(lo, hi), 1)
		if new(big.Int).Exp(mid, big.NewInt(n), nil).Cmp(v) <= 0 {
			lo = mid
		} else {
			hi = mid
		}
	}
	return lo
}

// TestPowWitnesses covers hard cases that double rounding or a short guard
// gets wrong, in all eight modes against the oracle, with the named mode's
// value pinned: 15000000000001² at p=2 is 2.3E+26, not 2.2E+26;
// 9999999999999² toward zero at p=3 is 9.99E+25, not 1.00E+26, which lies
// above the exact value; 449999² with ties away from zero at p=3 is
// 2.02E+11, not the double-rounded 2.03E+11;
// 1.0000000000001² away from zero at p=14 is 1.0000000000003; and
// 1.0000000000000001⁵ at p=16 is 1.000000000000001, from a guard digit 5
// with a nonzero tail. The adversarial family x = ⌈(k·10^j)^(1/n)⌉ (and
// ⌊…⌋), whose powers sit just above (below) k·10^j behind a run of zeros
// (nines) about j/n digits long, is checked at precisions around the run,
// and at least one member must need more than one truncated level.
func TestPowWitnesses(t *testing.T) {
	for _, tc := range []struct {
		x    string
		n    int32
		p    uint32
		mode RoundingMode
		want string
	}{
		{"15000000000001", 2, 2, TiesToEven, "2.3E+26"},
		{"9999999999999", 2, 3, TowardZero, "9.99E+25"},
		{"449999", 2, 3, TiesAwayFromZero, "2.02E+11"},
		{"1.0000000000001", 2, 14, AwayFromZero, "1.0000000000003"},
		{"1.0000000000000001", 5, 16, TiesToEven, "1.000000000000001"},
	} {
		x := MustParse(tc.x)
		got, _, err := x.PowWithContext(tc.n, mustContext(t, tc.p, tc.mode))
		if err != nil || got.String() != tc.want {
			t.Fatalf("%s^%d p=%d %v = %v %v, want %s", tc.x, tc.n, tc.p, tc.mode, got, err, tc.want)
		}
		c, e := divOracleParts(t, x)
		for _, mode := range allModes {
			got, conditions, err := x.PowWithContext(tc.n, mustContext(t, tc.p, mode))
			want := powOracle(powExactRat(c, e, int64(tc.n)), powIdeal(e, int64(tc.n)), int64(tc.p), mode, powGuardsOracle{})
			powCheck(t, fmt.Sprintf("%s^%d p=%d %v", tc.x, tc.n, tc.p, mode), got, conditions, err, want, false)
		}
	}
	escalated := 0
	for _, n := range []int64{2, 3, 5, 7, 13} {
		for _, j := range []int64{12, 30, 60} {
			for _, k := range []int64{1, 2, 3, 7, 12, 99, 314} {
				target := new(big.Int).Mul(big.NewInt(k), new(big.Int).Exp(big.NewInt(10), big.NewInt(j), nil))
				floor := powRoot(target, n)
				for _, c := range []*big.Int{floor, new(big.Int).Add(floor, big.NewInt(1))} {
					scale := -int64(len(c.String()) - 1)
					x := powDecimal(c, scale)
					kd := int64(len(big.NewInt(k).String()))
					for _, pp := range []int64{kd, kd + 1, kd + 2, kd + 4, j/n - 1, j / n, j/n + 2} {
						if pp < 1 {
							continue
						}
						p := uint32(pp)
						for _, mode := range allModes {
							cnt := &powCount{}
							got, conditions, err := x.powContext(int32(n), mustContext(t, p, mode), limits{}, "PowWithContext", cnt)
							if len(cnt.levels) > 1 {
								escalated++
							}
							want := powOracle(powExactRat(c, scale, n), powIdeal(scale, n), int64(p), mode, powGuardsOracle{})
							powCheck(t, fmt.Sprintf("(%v)^%d p=%d %v", x, n, p, mode), got, conditions, err, want, false)
						}
					}
				}
			}
		}
	}
	if escalated == 0 {
		t.Fatal("no adversarial power needed a second level")
	}
}

// TestPowNegativeExponents covers termination with negative exponents:
// a terminating reciprocal is exact at the reciprocal-then-multiply
// cohort, which equals both Div(1, x)^|n| and Div(1, x^|n|) (2⁻³ = 0.125,
// 8⁻² = 0.015625, 0.5⁻² = 4, 1.25⁻² = 0.64, 100⁻² = 0.0001, 1.00⁻² = 1,
// −2⁻³ = −0.125); a non-terminating one refuses in the bare forms with a
// *Error{Condition: Inexact} whose remedy names PowWithContext
// (n = −1 included), and the context form rounds 1/x^|n| once.
func TestPowNegativeExponents(t *testing.T) {
	for _, tc := range []struct {
		x    string
		n    int32
		want string
	}{
		{"2", -3, "0.125"}, {"8", -2, "0.015625"}, {"0.5", -2, "4"}, {"1.25", -2, "0.64"},
		{"100", -2, "0.0001"}, {"1.00", -2, "1"}, {"-2", -3, "-0.125"}, {"-2", -2, "0.25"},
		{"2E+3", -2, "2.5E-7"}, {"1.6", -4, "0.152587890625"}, {"5", -1, "0.2"}, {"4096", -3, "1.4551915228366851806640625E-11"},
	} {
		x := MustParse(tc.x)
		got, err := x.Pow(tc.n)
		if err != nil || got.String() != tc.want {
			t.Fatalf("%s^%d = %v %v, want %s", tc.x, tc.n, got, err, tc.want)
		}
		m := -tc.n
		reciprocal, err := One().Div(x)
		if err != nil {
			t.Fatal(err)
		}
		thenMultiply := One()
		for range m {
			if thenMultiply, err = thenMultiply.Mul(reciprocal); err != nil {
				t.Fatal(err)
			}
		}
		power := One()
		for range m {
			if power, err = power.Mul(x); err != nil {
				t.Fatal(err)
			}
		}
		divided, err := One().Div(power)
		if err != nil {
			t.Fatal(err)
		}
		if thenMultiply.Exponent() != got.Exponent() || divided.Exponent() != got.Exponent() || !thenMultiply.Equal(got) || !divided.Equal(got) {
			t.Fatalf("%s^%d = %v, reciprocal-then-multiply %v, Div(1, x^n) %v", tc.x, tc.n, got, thenMultiply, divided)
		}
	}
	for _, tc := range []struct {
		x string
		n int32
	}{{"3", -2}, {"3", -1}, {"6", -2}, {"0.3", -5}, {"2.7E+7", -3}, {"12", -2}, {strings.Repeat("7", 90), -2}} {
		x := MustParse(tc.x)
		for _, form := range []struct {
			op  string
			run func() (Decimal, error)
		}{
			{"Pow", func() (Decimal, error) { return x.Pow(tc.n) }},
			{"PowWithContext", func() (Decimal, error) {
				res, _, resErr := x.PowWithContext(tc.n, Context{}.WithBudget(Budget{MaxWork: 1 << 40}))
				return res, resErr
			}},
			{"PowWithContext", func() (Decimal, error) { d, _, err := x.PowWithContext(tc.n, Context{}); return d, err }},
		} {
			got, err := form.run()
			var ce *Error
			if !errors.As(err, &ce) || ce.Code != 0 || ce.Condition != Inexact || ce.Op != form.op || !strings.Contains(ce.Remedy, "PowWithContext") || !errors.Is(err, ErrInexact) || !isZeroValue(got) {
				t.Fatalf("%s(%s, %d) = (%v, %v), want the rounding-refused error naming PowWithContext", form.op, tc.x, tc.n, got, err)
			}
		}
		c, e := divOracleParts(t, x)
		for _, mode := range allModes {
			for _, p := range []uint32{1, 5, 34} {
				got, conditions, err := x.PowWithContext(tc.n, mustContext(t, p, mode))
				want := powOracle(powExactRat(c, e, int64(tc.n)), powIdeal(e, int64(tc.n)), int64(p), mode, powGuardsOracle{})
				powCheck(t, fmt.Sprintf("%s^%d p=%d %v", tc.x, tc.n, p, mode), got, conditions, err, want, false)
			}
		}
	}
}

// TestPowZeroCases covers the zeroth power and negative exponents of
// zero: x⁰ is 1E0 for every x, zero included, with no Conditions
// in every form; 0ⁿ for n > 0 is an unsigned zero at n·e, checked
// (ErrExponentRange outside int32, in the bare and the context forms);
// 0ⁿ for n < 0 is ErrDivisionByZero, and −0 behaves as 0.
func TestPowZeroCases(t *testing.T) {
	for _, in := range []string{"0", "0E+5", "-0E-7", "5", "-3.25", strings.Repeat("9", 100)} {
		x := MustParse(in)
		got, err := x.Pow(0)
		if err != nil || got.coefficientDigits() != "1" || got.Exponent() != 0 || got.negative() {
			t.Fatalf("(%s)^0 = %v %v", in, got, err)
		}
		for _, ctx := range []Context{{}, Decimal32Context(), mustContext(t, 1, Exact)} {
			got, conditions, err := x.PowWithContext(0, ctx)
			if err != nil || conditions != 0 || got.coefficientDigits() != "1" || got.Exponent() != 0 {
				t.Fatalf("(%s)^0 in %v = %v %v %v", in, ctx, got, conditions, err)
			}
		}
	}
	for _, tc := range []struct {
		x        string
		n        int32
		exponent int32
	}{{"0", 3, 0}, {"0E-3", 4, -12}, {"-0E+2", 3, 6}, {"0E+1", math.MaxInt32, math.MaxInt32}, {"0E-1", math.MaxInt32, -math.MaxInt32}} {
		x := MustParse(tc.x)
		got, err := x.Pow(tc.n)
		if err != nil || !got.isZero() || got.negative() || got.Exponent() != tc.exponent {
			t.Fatalf("(%s)^%d = %v %v", tc.x, tc.n, got, err)
		}
		got, conditions, err := x.PowWithContext(tc.n, Decimal64Context())
		if err != nil || conditions != 0 || !got.isZero() || got.negative() || got.Exponent() != tc.exponent {
			t.Fatalf("(%s)^%d in context = %v %v %v", tc.x, tc.n, got, conditions, err)
		}
	}
	for _, n := range []int32{-1, -2, math.MinInt32} {
		for _, in := range []string{"0", "-0E-5"} {
			x := MustParse(in)
			if _, err := x.Pow(n); !errors.Is(err, ErrDivisionByZero) {
				t.Fatalf("(%s)^%d: %v", in, n, err)
			}
			if _, _, err := x.PowWithContext(n, Decimal128Context()); !errors.Is(err, ErrDivisionByZero) {
				t.Fatalf("(%s)^%d in context: %v", in, n, err)
			}
		}
	}
	for _, x := range []Decimal{MustParse("0E+2"), MustParse("0E-2")} {
		if _, err := x.Pow(math.MaxInt32); !errors.Is(err, ErrExponentRange) {
			t.Fatalf("(%v)^MaxInt32: %v", x, err)
		}
		if _, _, err := x.PowWithContext(math.MaxInt32, Decimal128Context()); !errors.Is(err, ErrExponentRange) {
			t.Fatalf("(%v)^MaxInt32 in context: %v", x, err)
		}
	}
}

// powInterval returns the leading digits+1 digits of c^m·10^−K (or of
// 10^K/c^m when reciprocal) and K, from two big.Float chains of binary
// exponentiation at 800 bits, one rounded toward zero and one away, each
// kept in [1, 10) with its own decimal exponent. It fails when the chains
// disagree on the leading digits, so any result it returns is proved.
func powInterval(t *testing.T, c *big.Int, m uint64, digits int, reciprocal bool) (*big.Int, int64) {
	t.Helper()
	const prec = 800
	ten := new(big.Float).SetPrec(prec).SetInt64(10)
	chain := func(mode big.RoundingMode) (*big.Float, int64) {
		f := func() *big.Float { return new(big.Float).SetPrec(prec).SetMode(mode) }
		base := f().SetInt(c)
		var kb int64
		for base.Cmp(ten) >= 0 {
			base = f().Quo(base, ten)
			kb++
		}
		y, k := f().Set(base), kb
		for i := 62; i >= 0; i-- {
			if m>>uint(i) == 0 {
				continue
			}
			if m>>uint(i) != 1 {
				y, k = f().Mul(y, y), 2*k
				if y.Cmp(ten) >= 0 {
					y, k = f().Quo(y, ten), k+1
				}
				if m>>uint(i)&1 == 1 {
					y, k = f().Mul(y, base), k+kb
					if y.Cmp(ten) >= 0 {
						y, k = f().Quo(y, ten), k+1
					}
				}
			}
		}
		return y, k
	}
	lo, klo := chain(big.ToZero)
	hi, khi := chain(big.AwayFromZero)
	if reciprocal {
		// 1/(y·10^k) = (10/y)·10^(−k−1), with the rounding sides swapped.
		lo, hi = new(big.Float).SetPrec(prec).SetMode(big.ToZero).Quo(ten, hi), new(big.Float).SetPrec(prec).SetMode(big.AwayFromZero).Quo(ten, lo)
		klo, khi = -khi-1, -klo-1
	}
	scale := new(big.Float).SetPrec(prec).SetInt(new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(digits)), nil))
	ql, _ := new(big.Float).SetPrec(prec).SetMode(big.ToZero).Mul(lo, scale).Int(nil)
	qh, _ := new(big.Float).SetPrec(prec).SetMode(big.AwayFromZero).Mul(hi, scale).Int(nil)
	if klo != khi || ql.Cmp(qh) != 0 || len(ql.String()) != digits+1 {
		t.Fatalf("interval oracle undecided for %v^%d: %v·10^%d, %v·10^%d", c, m, ql, klo, qh, khi)
	}
	return ql, klo
}

// TestPowInt32Extremes covers n = MinInt32 and MaxInt32 (|n| carried in
// 64 bits): (±1)^n, (1E±1)^n at the edges of the exponent range and one
// past them (ErrExponentRange), 2^MaxInt32 and 2^MinInt32 at p=34 against
// a big.Float interval oracle (the truncated levels decide), 2^MaxInt32
// and 0.5^MaxInt32 under Decimal128 guards (overflow and underflow decided
// before any level), and the Exact refusal of 3^MaxInt32 without work.
func TestPowInt32Extremes(t *testing.T) {
	for _, tc := range []struct {
		x    string
		n    int32
		want string
	}{
		{"1", math.MaxInt32, "1"}, {"1", math.MinInt32, "1"}, {"-1", math.MaxInt32, "-1"}, {"-1", math.MinInt32, "1"},
		{"1E+1", math.MaxInt32, "1E+2147483647"}, {"1E+1", math.MinInt32, "1E-2147483648"}, {"1E-1", math.MaxInt32, "1E-2147483647"},
	} {
		got, err := MustParse(tc.x).Pow(tc.n)
		if err != nil || got.String() != tc.want {
			t.Fatalf("(%s)^%d = %v %v, want %s", tc.x, tc.n, got, err, tc.want)
		}
		got, conditions, err := MustParse(tc.x).PowWithContext(tc.n, Decimal128Context().withoutGuards(t))
		if err != nil || conditions != 0 || got.String() != tc.want {
			t.Fatalf("(%s)^%d at p=34 = %v %v %v, want %s", tc.x, tc.n, got, conditions, err, tc.want)
		}
	}
	for _, tc := range []struct {
		x string
		n int32
	}{{"1E-1", math.MinInt32}, {"1E+2", math.MaxInt32}, {"1E-2", math.MinInt32}} {
		if _, err := MustParse(tc.x).Pow(tc.n); !errors.Is(err, ErrExponentRange) {
			t.Fatalf("(%s)^%d: %v", tc.x, tc.n, err)
		}
		if _, _, err := MustParse(tc.x).PowWithContext(tc.n, mustContext(t, 34, TiesToEven)); !errors.Is(err, ErrExponentRange) {
			t.Fatalf("(%s)^%d in context: %v", tc.x, tc.n, err)
		}
	}
	for _, n := range []int32{math.MaxInt32, math.MinInt32, math.MaxInt32 - 1} {
		m := powMagnitude(n)
		for _, mode := range []RoundingMode{TiesToEven, TowardZero, AwayFromZero} {
			cnt := &powCount{}
			got, conditions, err := MustParse("2").powContext(n, mustContext(t, 34, mode), limits{}, "PowWithContext", cnt)
			if err != nil || len(cnt.levels) != 1 || cnt.exact {
				t.Fatalf("2^%d: %v levels %v exact %v", n, err, cnt.levels, cnt.exact)
			}
			prefix, k := powInterval(t, big.NewInt(2), m, 40, n < 0)
			// The 41-digit prefix truncates a value with a nonzero tail, so
			// prefix + 1/10 rounds exactly as the value does at 34 digits.
			stand := new(big.Rat).SetFrac(new(big.Int).Add(new(big.Int).Mul(prefix, big.NewInt(10)), big.NewInt(1)), big.NewInt(10))
			want := powOracle(stand, math.MinInt64/2, 34, mode, powGuardsOracle{})
			if got.coefficientDigits() != want.coefficient.String() || int64(got.Exponent()) != want.exponent+k-40 || conditions != want.conditions {
				t.Fatalf("2^%d %v = %s·10^%d %v, want %s·10^%d %v", n, mode, got.coefficientDigits(), got.Exponent(), conditions, want.coefficient, want.exponent+k-40, want.conditions)
			}
		}
	}
	for _, tc := range []struct {
		x    string
		want Conditions
	}{{"2", Overflow | Inexact | Rounded | Decreased}, {"0.5", Subnormal | Underflow | Inexact | Rounded | Decreased}} {
		cnt := &powCount{}
		got, conditions, err := MustParse(tc.x).powContext(math.MaxInt32, Decimal128Context(), limits{}, "PowWithContext", cnt)
		if err != nil || conditions != tc.want || len(cnt.levels) != 0 || cnt.exact {
			t.Fatalf("%s^MaxInt32 guarded: %v %v %v (levels %v)", tc.x, got, conditions, err, cnt.levels)
		}
	}
	// A result that rounds up across the lower exponent edge: (99999999999E−1073741831)²
	// has adjusted exponent −2147483641, so at p=9 its rounding exponent is
	// MinInt32 − 1, and a carry lands exactly on MinInt32. The unguarded
	// range pre-check must not refuse it.
	edge := powDecimal(big.NewInt(99999999999), -1073741831)
	for _, mode := range []RoundingMode{AwayFromZero, TiesToEven, TowardZero} {
		got, conditions, err := edge.PowWithContext(2, mustContext(t, 9, mode))
		if mode == TowardZero {
			if !errors.Is(err, ErrExponentRange) {
				t.Fatalf("edge² p=9 %v: %v %v %v, want ErrExponentRange", mode, got, conditions, err)
			}
			continue
		}
		if err != nil || got.coefficientDigits() != "100000000" || got.Exponent() != math.MinInt32 || conditions != Inexact|Rounded|Increased {
			t.Fatalf("edge² p=9 %v: %s·10^%d %v %v", mode, got.coefficientDigits(), got.Exponent(), conditions, err)
		}
	}
	cnt := &powCount{}
	if _, _, err := MustParse("3").powContext(math.MaxInt32, mustContext(t, 34, Exact), limits{}, "PowWithContext", cnt); !errors.Is(err, ErrInexact) || cnt.work != powTestScan(0) || len(cnt.levels) != 0 {
		// Only the one-limb trailing-zero scan runs before the refusal.
		t.Fatalf("3^MaxInt32 under Exact: %v, work %d", err, cnt.work)
	}
}

// withoutGuards is the context's precision and mode, unguarded.
func (c Context) withoutGuards(t *testing.T) Context {
	t.Helper()
	return mustContext(t, c.precision, c.rounding)
}

// TestPowGuards covers the guarded context and the pre-decided overflow
// and underflow of Pow: hand-derived vectors
// (2¹⁰⁰⁰ and 0.5¹⁰⁰⁰ in Decimal32 decided before any level, the
// substitution of Bmax, Exact refusing an overflow, a trapped Underflow,
// 1 above a negative Emax, a reciprocal overflowing and underflowing) and
// random guarded operands in all eight modes against the oracle.
func TestPowGuards(t *testing.T) {
	for _, tc := range []struct {
		x    string
		n    int32
		ctx  Context
		want string
		cond Conditions
	}{
		{"2", 1000, Decimal32Context(), "9.999999E+96", Overflow | Inexact | Rounded | Decreased},
		{"-2", 1001, Decimal32Context(), "-9.999999E+96", Overflow | Inexact | Rounded | Increased},
		{"0.5", 1000, Decimal32Context(), "0E-101", Subnormal | Underflow | Inexact | Rounded | Decreased},
		{"0.5", 1000, mustGuarded(t, 7, TowardPositiveInfinity, -95, 96, 0), "1E-101", Subnormal | Underflow | Inexact | Rounded | Increased},
		{"2", -1000, Decimal32Context(), "0E-101", Subnormal | Underflow | Inexact | Rounded | Decreased},
		{"0.5", -1000, Decimal32Context(), "9.999999E+96", Overflow | Inexact | Rounded | Decreased},
		{"7", 0, mustGuarded(t, 5, TiesToEven, -9, -1, 0), "0.99999", Overflow | Inexact | Rounded | Decreased},
		{"1.1", 700, mustGuarded(t, 7, TiesToEven, -95, 96, 0), "9.437992E+28", Inexact | Rounded | Decreased},
	} {
		cnt := &powCount{}
		got, conditions, err := MustParse(tc.x).powContext(tc.n, tc.ctx, limits{}, "PowWithContext", cnt)
		if err != nil || got.String() != tc.want || conditions != tc.cond {
			t.Fatalf("(%s)^%d = %v %v %v, want %s %v", tc.x, tc.n, got, conditions, err, tc.want, tc.cond)
		}
		if tc.cond&(Overflow|Underflow) != 0 && tc.n != 0 && (len(cnt.levels) != 0 || cnt.exact) {
			t.Fatalf("(%s)^%d: certain range outcome ran levels %v", tc.x, tc.n, cnt.levels)
		}
	}
	exact := mustGuarded(t, 7, Exact, -95, 96, 0)
	if _, _, err := MustParse("2").PowWithContext(1000, exact); !errors.Is(err, ErrInexact) {
		t.Fatalf("Exact overflow: %v", err)
	}
	trapped := mustGuarded(t, 7, TiesToEven, -95, 96, Underflow)
	if _, _, err := MustParse("0.5").PowWithContext(1000, trapped); !errors.Is(err, ErrUnderflow) {
		t.Fatalf("trapped Underflow: %v", err)
	}
	r := rand.New(rand.NewPCG(53, 42))
	cases := 4000
	if testing.Short() {
		cases = 800
	}
	for i := range cases {
		c := powOperandFor(r, 12)
		if c.Sign() == 0 {
			continue
		}
		e := int64(r.IntN(9) - 4)
		n := int64(r.IntN(61) - 30)
		p := int64(1 + r.IntN(12))
		emin := int64(-r.IntN(40))
		emax := int64(r.IntN(40))
		mode := allModes[r.IntN(len(allModes))]
		x := powDecimal(c, e)
		ctx := mustGuarded(t, uint32(p), mode, int32(emin), int32(emax), 0)
		got, conditions, err := x.PowWithContext(int32(n), ctx)
		want := powOracle(powExactRat(c, e, n), powIdeal(e, n), p, mode, powGuardsOracle{on: true, emin: emin, emax: emax})
		powCheck(t, fmt.Sprintf("case %d: (%v)^%d p=%d [%d,%d] %v", i, x, n, p, emin, emax, mode), got, conditions, err, want, c.Sign() < 0 && n%2 != 0)
	}
}

// TestPowExactModeRefusal covers the Exact mode refusal of Pow: under
// Exact a power that needs more than p digits refuses in O(1) (no level
// and no exact power run) with Decimal{}, zero Conditions and
// *Error{Condition: Inexact}; an exact power that fits succeeds
// with no Conditions; a zero-only discard (1.10³ = 1.331000 at p=4 is
// 1.331) reports Rounded, which Exact permits; and the reciprocal of a
// power of 5, whose value 2^(b·n) may be short although 5^(b·n) is long,
// is decided exactly (5⁻²⁰ = 1.048576E−14 at p=10).
func TestPowExactModeRefusal(t *testing.T) {
	for _, tc := range []struct {
		x string
		n int32
		p uint32
	}{{"1.1", 40, 34}, {"3", 100, 10}, {"-7", 21, 16}, {"3", -2, 5}, {"1.0001", 1000000, 34}} {
		for _, traps := range []Conditions{0, Inexact | Rounded} {
			ctx, _ := NewContext(tc.p, Exact, nil, traps)
			cnt := &powCount{}
			got, conditions, err := MustParse(tc.x).powContext(tc.n, ctx, limits{}, "PowWithContext", cnt)
			var ce *Error
			if !errors.As(err, &ce) || ce.Code != 0 || ce.Condition != Inexact || !isZeroValue(got) || conditions != 0 {
				t.Fatalf("(%s)^%d Exact p=%d: (%v, %v, %v)", tc.x, tc.n, tc.p, got, conditions, err)
			}
			// Beyond the trailing-zero scan (one limb here), no work.
			if tc.n > 0 && (len(cnt.levels) != 0 || cnt.exact || cnt.work != powTestScan(0)) {
				t.Fatalf("(%s)^%d Exact: refusal ran work %d, levels %v", tc.x, tc.n, cnt.work, cnt.levels)
			}
		}
	}
	// The Exact refusal precedes the unguarded range refusal for
	// every operand, as for n > 0 and Div. 74055 and 74053 differ only in
	// whether the O(1) refusal applies (c ends in 5); both are inexact.
	// 5⁻¹⁶ is exact and out of range, so it reports ErrExponentRange.
	exactCtx := mustContext(t, 17, Exact)
	for _, in := range []string{"7.4055E-134217735", "7.4053E-134217735"} {
		if _, _, err := MustParse(in).PowWithContext(-16, exactCtx); !errors.Is(err, ErrInexact) {
			t.Fatalf("(%s)^-16 Exact: %v, want the Exact refusal", in, err)
		}
		if _, _, err := MustParse(in).PowWithContext(-16, mustContext(t, 17, TiesToEven)); !errors.Is(err, ErrExponentRange) {
			t.Fatalf("(%s)^-16 half-even: %v, want ErrExponentRange", in, err)
		}
	}
	if _, _, err := MustParse("5E-134217735").PowWithContext(-16, exactCtx); !errors.Is(err, ErrExponentRange) {
		t.Fatalf("(5E-134217735)^-16 Exact: %v, want ErrExponentRange", err)
	}
	for _, tc := range []struct {
		x    string
		n    int32
		p    uint32
		want string
		cond Conditions
	}{
		{"1.1", 10, 34, "2.5937424601", 0},
		{"1.10", 3, 4, "1.331", Rounded},
		{"1.10", 3, 7, "1.331000", 0},
		{"5", -20, 10, "1.048576E-14", 0},
		{"0.5", -30, 10, "1073741824", 0},
		{"-2", 7, 3, "-128", 0},
		{"2E+3", 3, 1, "8E+9", 0},
	} {
		ctx := mustContext(t, tc.p, Exact)
		got, conditions, err := MustParse(tc.x).PowWithContext(tc.n, ctx)
		if err != nil || got.String() != tc.want || conditions != tc.cond {
			t.Fatalf("(%s)^%d Exact p=%d = %v %v %v, want %s %v", tc.x, tc.n, tc.p, got, conditions, err, tc.want, tc.cond)
		}
	}
}

// TestPowZivMatchesExact is the differential test for the Ziv
// acceptance and the exact-path gate: over random operands, exponents
// and precisions in all eight modes, guarded and not, the kernel's
// outcome equals the one forced through the exact fallback by the test
// seam (every truncated level rejected) in value, exponent, Conditions
// and error. The guard against a vacuous pass requires that at least a
// third of the cases were decided by a truncated level.
func TestPowZivMatchesExact(t *testing.T) {
	r := rand.New(rand.NewPCG(53, 43))
	cases := 5000
	if testing.Short() {
		cases = 1000
	}
	decided := 0
	for i := range cases {
		c := powOperandFor(r, 30)
		if c.Sign() == 0 {
			continue
		}
		e := int64(r.IntN(11) - 5)
		n := int32(r.IntN(121) - 60)
		p := uint32(1 + r.IntN(40))
		mode := allModes[r.IntN(len(allModes))]
		ctx := mustContext(t, p, mode)
		if r.IntN(3) == 0 {
			ctx = mustGuarded(t, p, mode, int32(-r.IntN(200)), int32(r.IntN(200)), 0)
		}
		x := powDecimal(c, e)
		normal := &powCount{}
		got, conditions, err := x.powContext(n, ctx, limits{}, "PowWithContext", normal)
		forced := &powCount{escalate: true}
		want, wantConditions, wantErr := x.powContext(n, ctx, limits{}, "PowWithContext", forced)
		if len(normal.levels) > 0 && !normal.exact {
			decided++
			if !forced.exact {
				t.Fatalf("case %d: the seam did not reach the exact fallback", i)
			}
		}
		if fmt.Sprint(err) != fmt.Sprint(wantErr) || conditions != wantConditions || got.coefficientDigits() != want.coefficientDigits() || got.exponent() != want.exponent() || got.negative() != want.negative() {
			t.Fatalf("case %d (%v)^%d %v: truncated %v %v %v, exact %v %v %v", i, x, n, ctx, got, conditions, err, want, wantConditions, wantErr)
		}
	}
	if decided < cases/3 {
		t.Fatalf("vacuous differential: %d of %d decided by a truncated level", decided, cases)
	}
}

// TestPowDigitBracket covers the fixed-point digit bracket
// Dlo ≤ digits(c^k) ≤ Dhi, Dhi − Dlo ≤ 1, holds against big.Int for
// random c of 1–60 digits (exact and truncated leading digits) and k up
// to 3000; for k up to MaxInt32 against log10 2, log10 3 and log10 7 to
// 60 digits (big.Float); the log10 brackets enclose those constants; and
// the bracket stays within one digit for every k at the 19-digit extremes.
func TestPowDigitBracket(t *testing.T) {
	r := rand.New(rand.NewPCG(53, 44))
	for i := range 3000 {
		c := randomDigits(r, 1+r.IntN(60))
		if new(big.Int).Mod(c, big.NewInt(10)).Sign() == 0 {
			c.Add(c, big.NewInt(1))
		}
		x := powDecimal(c, 0)
		o := newPowOperand(x)
		k := uint64(1 + r.IntN(300))
		if i%10 == 0 {
			k = uint64(1 + r.IntN(3000))
		}
		lo, hi, ok := o.log.digits(o.d, k)
		d := uint64(len(new(big.Int).Exp(c, new(big.Int).SetUint64(k), nil).String()))
		if !ok || lo > d || d > hi || hi-lo > 1 {
			t.Fatalf("digits(%v^%d) = %d outside [%d, %d]", c, k, d, lo, hi)
		}
	}
	for _, tc := range []struct {
		c     int64
		log10 string
	}{
		{2, "0.301029995663981195213738894724493026768189881462108541310"},
		{3, "0.477121254719662437295027903255115309200128864190695864829"},
		{7, "0.845098040014256830712216258592636193483572396323965406503"},
	} {
		l, _, _ := new(big.Float).SetPrec(300).Parse(tc.log10, 10)
		o := newPowOperand(New(tc.c, 0))
		lo := new(big.Float).SetPrec(300).SetMantExp(new(big.Float).SetUint64(o.log.lo), -64)
		hi := new(big.Float).SetPrec(300).SetMantExp(new(big.Float).SetUint64(o.log.hi), -64)
		if lo.Cmp(l) > 0 || hi.Cmp(l) < 0 || o.log.one {
			t.Fatalf("log10 %d bracket [%v, %v] misses %v", tc.c, lo, hi, l)
		}
		for range 2000 {
			k := uint64(2 + r.IntN(math.MaxInt32-1))
			prod := new(big.Float).SetPrec(300).Mul(l, new(big.Float).SetUint64(k))
			floor, _ := prod.Int(nil)
			d := floor.Uint64() + 1
			lo, hi, ok := o.log.digits(1, k)
			if !ok || lo > d || d > hi || hi-lo > 1 {
				t.Fatalf("digits(%d^%d) = %d outside [%d, %d]", tc.c, k, d, lo, hi)
			}
		}
	}
	for _, top := range []string{"1000000000000000000", "9999999999999999999", "1000000000000000001", "3162277660168379332"} {
		for _, d := range []uint64{20, 40} {
			c, _ := new(big.Int).SetString(top+strings.Repeat("7", int(d-19)), 10)
			o := newPowOperand(powDecimal(c, 0))
			for _, k := range []uint64{1, 2, 3, 1000, 1 << 20, math.MaxInt32, 1 << 31} {
				lo, hi, ok := o.log.digits(o.d, k)
				if !ok || hi < lo || hi-lo > 1 || lo < k*(d-1)+1 || hi > k*d {
					t.Fatalf("bracket of %s…^%d = [%d, %d]", top, k, lo, hi)
				}
			}
		}
	}
}

// TestPowTruncatedWidth checks the kernel's truncated-power bounds: L ≤ C^m ≤
// U always (against big.Int), and the relative width (U − L)/L stays below
// 6m·10^(1−w) over random c, m and w, which with w = p+1+⌈log10(2m)⌉+2 is
// below 0.3·10^−(p+1). The worst observed ratio to that bound is reported.
func TestPowTruncatedWidth(t *testing.T) {
	r := rand.New(rand.NewPCG(53, 45))
	worst := 0.0
	cases := 3000
	if testing.Short() {
		cases = 600
	}
	for range cases {
		c := randomDigits(r, 1+r.IntN(60))
		m := uint64(2 + r.IntN(300))
		p := uint64(1 + r.IntN(40))
		w := p + 1 + powGuard(m)
		o := newPowOperand(powDecimal(c, 0))
		buf := make([]uint32, powLevelLimbs(w, p, false))
		arena := powArena{buf: buf}
		lower, sl, upper, su := o.powBounds(m, w, &arena, nil)
		exact := new(big.Int).Exp(c, new(big.Int).SetUint64(m), nil)
		toRat := func(r []uint32, s int64) *big.Rat {
			v := powDecimal(big.NewInt(0), 0)
			v = publishScratch(r, 0, false)
			return new(big.Rat).Mul(divRat(t, v), pow10Rat(s))
		}
		L, U, X := toRat(lower, sl), toRat(upper, su), new(big.Rat).SetInt(exact)
		if L.Cmp(X) > 0 || U.Cmp(X) < 0 {
			t.Fatalf("%v^%d at w=%d: bounds [%v, %v] miss the power", c, m, w, L.FloatString(3), U.FloatString(3))
		}
		width := new(big.Rat).Quo(new(big.Rat).Sub(U, L), L)
		bound := new(big.Rat).Mul(big.NewRat(int64(6*m), 1), pow10Rat(1-int64(w)))
		ratio, _ := new(big.Rat).Quo(width, bound).Float64()
		if ratio >= 1 {
			t.Fatalf("%v^%d at w=%d: width %v exceeds 6m·10^(1−w)", c, m, w, width.FloatString(40))
		}
		worst = max(worst, ratio)
		if limit := new(big.Rat).Mul(big.NewRat(3, 10), pow10Rat(-int64(p+1))); bound.Cmp(limit) > 0 {
			t.Fatalf("m=%d p=%d: 6m·10^(1−w) above 0.3·10^−(p+1)", m, p)
		}
	}
	t.Logf("worst width / (6m·10^(1−w)) = %.4f", worst)
}

// TestPowLongCoefficients covers limb-held operands and results: bare
// powers of 60- to 200-digit coefficients (with trailing zeros, so the
// cohort appends n·z zeros) equal big.Int.Exp, and context powers of
// 100- to 300-digit operands at precisions 1–120 match the oracle in all
// modes.
func TestPowLongCoefficients(t *testing.T) {
	r := rand.New(rand.NewPCG(53, 46))
	for range 60 {
		c := randomDigits(r, 60+r.IntN(140))
		c.Mul(c, new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(r.IntN(20))), nil))
		n := int64(2 + r.IntN(6))
		e := int64(r.IntN(11) - 5)
		got, err := powDecimal(c, e).Pow(int32(n))
		want, _ := powOracleBare(c, e, n)
		powCheck(t, fmt.Sprintf("%d-digit ^%d", len(c.String()), n), got, 0, err, want, false)
	}
	for range 300 {
		c := randomDigits(r, 100+r.IntN(200))
		n := int64(r.IntN(13) - 6)
		if n >= -1 && n <= 1 {
			n = 3
		}
		p := int64(1 + r.IntN(120))
		mode := allModes[r.IntN(len(allModes))]
		e := int64(r.IntN(11) - 5)
		got, conditions, err := powDecimal(c, e).PowWithContext(int32(n), mustContext(t, uint32(p), mode))
		want := powOracle(powExactRat(c, e, n), powIdeal(e, n), p, mode, powGuardsOracle{})
		powCheck(t, fmt.Sprintf("%d-digit ^%d p=%d %v", len(c.String()), n, p, mode), got, conditions, err, want, false)
	}
}

// powTestLimbs is t(x) = 1+(x−1)/9, restated for the closed forms.
func powTestLimbs(x uint64) uint64 { return 1 + (x-1)/9 }

// powTestSteps is the exact-path tariff for c^m, restated independently: over
// the left-to-right binary-exponentiation steps, t(a)² + 2a for squaring c^k
// and t(a)·t(d) + a + d for multiplying c^k by c, with a = size(k).
func powTestSteps(m, d uint64, size func(k uint64) uint64) uint64 {
	var total uint64
	k := uint64(1)
	top := 63
	for m>>uint(top) == 0 {
		top--
	}
	for i := top - 1; i >= 0; i-- {
		a := size(k)
		total += powTestLimbs(a)*powTestLimbs(a) + 2*a
		k *= 2
		if m>>uint(i)&1 == 1 {
			a = size(k)
			total += powTestLimbs(a)*powTestLimbs(d) + a + d
			k++
		}
	}
	return total
}

// powTestScan is the charge of finding z: the ⌊z/9⌋
// zero limbs and the limb holding c's last digit.
func powTestScan(z uint64) uint64 { return z/9 + 1 }

// powTestLevel is one truncated level's tariff, 4·⌈log2 m⌉·(t(w)²+2w),
// plus two division charges for n < 0.
func powTestLevel(w, m, p uint64, reciprocal bool) uint64 {
	ceilLog := uint64(0)
	for uint64(1)<<ceilLog < m {
		ceilLog++
	}
	level := 4 * ceilLog * (powTestLimbs(w)*powTestLimbs(w) + 2*w)
	if reciprocal {
		level += 2 * powTestDiv(w, p)
	}
	return level
}

// powTestDiv is the Div-kernel bound of one reciprocal division by a
// dy-digit integer: reads dy+p+1, divisor dy, one, the loop
// 2(⌈(p+1)/9⌉+1)(t(dy)+1) and the normalization 2(t(dy+p+1)+t(dy)+1).
func powTestDiv(dy, p uint64) uint64 {
	return dy + p + 1 + dy + 1 + 2*((p+9)/9+1)*(powTestLimbs(dy)+1) + 2*(powTestLimbs(dy+p+1)+powTestLimbs(dy)+1)
}

// powStripped is c = C/10^z and z.
func powStripped(c *big.Int) (*big.Int, uint64) {
	c = new(big.Int).Abs(c)
	var z uint64
	ten := big.NewInt(10)
	for c.Sign() != 0 && new(big.Int).Mod(c, ten).Sign() == 0 {
		c.Quo(c, ten)
		z++
	}
	return c, z
}

// powActualDigits returns k ↦ digits(c^k) from big.Int, memoized.
func powActualDigits(c *big.Int) func(uint64) uint64 {
	memo := map[uint64]uint64{}
	return func(k uint64) uint64 {
		if v, ok := memo[k]; ok {
			return v
		}
		v := uint64(len(new(big.Int).Exp(c, new(big.Int).SetUint64(k), nil).String()))
		memo[k] = v
		return v
	}
}

// TestPowBudget covers the Pow budget boundaries: the smallest
// admitting work cap of bare Pow lies between the exact tariff at the
// actual partial-power sizes and at those sizes plus one (the bracket's
// width), plus n·z, and equals it exactly for all-nines coefficients,
// whose bracket is exact; the smallest admitting digit cap is the
// published cohort's D + n·z; the context forms charge B + 2N + 1; zeros
// and n = 0 cost W = 1 bare and 4 in context.
func TestPowBudget(t *testing.T) {
	smallest := func(hi uint64, run func(Budget) error, digits bool) uint64 {
		return smallestAdmitting(hi, func(n uint64) bool {
			if digits {
				return run(Budget{MaxDigits: n}) == nil
			}
			return run(Budget{MaxWork: n}) == nil
		})
	}
	r := rand.New(rand.NewPCG(53, 47))
	for _, digits := range []int{1, 2, 9, 10, 19, 20, 38, 60, 150} {
		for _, n := range []int32{2, 3, 5, 8, 13, 37} {
			for _, nines := range []bool{false, true} {
				c := randomDigits(r, digits)
				if nines {
					c, _ = new(big.Int).SetString(strings.Repeat("9", digits), 10)
				}
				zeros := int64(r.IntN(4))
				full := new(big.Int).Mul(c, new(big.Int).Exp(big.NewInt(10), big.NewInt(zeros), nil))
				x := powDecimal(full, -3)
				stripped, z := powStripped(full)
				d := uint64(len(stripped.String()))
				m := uint64(n)
				size := powActualDigits(stripped)
				lower := powTestSteps(m, d, size) + m*z + powTestScan(z)
				upper := powTestSteps(m, d, func(k uint64) uint64 { return min(size(k)+1, k*d) }) + m*z + powTestScan(z)
				run := func(b Budget) error { _, _, err := x.PowWithContext(n, Context{}.WithBudget(b)); return err }
				w := smallest(upper+1, run, false)
				// All-nines coefficients short enough that every partial
				// power has k·d digits have an exact bracket: attained.
				exactBracket := nines && size(m) == m*d
				if w < lower || w > upper || exactBracket && w != powTestSteps(m, d, func(k uint64) uint64 { return k * d })+m*z+powTestScan(z) {
					t.Fatalf("(%v)^%d: smallest work %d outside [%d, %d]", x, n, w, lower, upper)
				}
				want := size(m) + m*z
				if got := smallest(want+10, run, true); got != want {
					t.Fatalf("(%v)^%d: smallest digits %d, want %d", x, n, got, want)
				}
			}
		}
	}
	for _, p := range []uint32{1, 7, 34, 81} {
		for _, tc := range []struct {
			x string
			n int32
		}{{"1.05", 12}, {"2", 20}, {"3", -7}, {"1.1", 3}, {strings.Repeat("9", 50), 3}} {
			x := MustParse(tc.x)
			ctx := mustContext(t, p, TiesToEven)
			got, _, err := x.PowWithContext(tc.n, ctx)
			if err != nil {
				t.Fatal(err)
			}
			cnt := &powCount{}
			_, _, _ = x.powContext(tc.n, ctx, limits{}, "PowWithContext", cnt)
			run := func(b Budget) error { _, _, err := x.PowWithContext(tc.n, ctx.WithBudget(b)); return err }
			w := smallest(1<<40, run, false)
			base := w - 2*got.CoefficientDigits() - 1
			levels := powTestScan(0) // every operand here has z = 0
			for _, lw := range cnt.levels {
				levels += powTestLevel(lw, powMagnitude(tc.n), uint64(p), tc.n < 0)
			}
			if !cnt.exact && base != levels {
				t.Fatalf("(%s)^%d p=%d: B = %d, want the levels' %d", tc.x, tc.n, p, base, levels)
			}
			if cnt.exact && base < levels {
				t.Fatalf("(%s)^%d p=%d: B = %d below the levels' %d", tc.x, tc.n, p, base, levels)
			}
			if d := smallest(uint64(p), run, true); d != got.CoefficientDigits() {
				t.Fatalf("(%s)^%d p=%d: smallest digits %d, want %d", tc.x, tc.n, p, d, got.CoefficientDigits())
			}
		}
	}
	for _, tc := range []struct {
		name string
		run  func(Budget) error
		work uint64
	}{
		{"bare zero", func(b Budget) error {
			_, _, err := MustParse("0E-7").PowWithContext(3, Context{}.WithBudget(b))
			return err
		}, 1},
		{"bare n=0", func(b Budget) error {
			_, _, err := MustParse("123.4").PowWithContext(0, Context{}.WithBudget(b))
			return err
		}, 1},
		{"context zero", func(b Budget) error {
			_, _, err := MustParse("0E-7").PowWithContext(3, Decimal64Context().WithBudget(b))
			return err
		}, 4},
		{"context n=0", func(b Budget) error {
			_, _, err := MustParse("123.4").PowWithContext(0, Decimal64Context().WithBudget(b))
			return err
		}, 4},
		// n = 1 is RoundToPrecision (an Add of a zero: W = d bare, the
		// one-nonzero Add base d plus 2N+1 in context).
		{"bare n=1", func(b Budget) error {
			_, _, err := MustParse("-123.45").PowWithContext(1, Context{}.WithBudget(b))
			return err
		}, 5},
		{"context n=1", func(b Budget) error {
			_, _, err := MustParse("-123.45").PowWithContext(1, Decimal64Context().WithBudget(b))
			return err
		}, 5 + 2*5 + 1},
	} {
		if w := smallest(100, tc.run, false); w != tc.work {
			t.Fatalf("%s: work %d, want %d", tc.name, w, tc.work)
		}
		if n := smallest(100, tc.run, true); n != 1 && !strings.Contains(tc.name, "n=1") {
			t.Fatalf("%s: digits %d", tc.name, n)
		}
	}
	// n = −1 is Div of one by x, charged as Div.
	for _, in := range []string{"8", "0.3", "-1.25E+7"} {
		x := MustParse(in)
		pow := func(b Budget) error {
			_, _, err := x.PowWithContext(-1, Decimal64Context().WithBudget(b))
			return err
		}
		div := func(b Budget) error {
			_, _, err := One().DivWithContext(x, Decimal64Context().WithBudget(b))
			return err
		}
		if a, b := smallest(1<<20, pow, false), smallest(1<<20, div, false); a != b {
			t.Fatalf("(%s)^-1: work %d, Div's %d", in, a, b)
		}
		if _, _, err := x.PowWithContext(-1, Context{}.WithBudget(Budget{MaxWork: 1 << 20})); err == nil {
			bare := func(b Budget) error { _, _, err := x.PowWithContext(-1, Context{}.WithBudget(b)); return err }
			divBare := func(b Budget) error { _, _, err := One().DivWithContext(x, Context{}.WithBudget(b)); return err }
			if a, b := smallest(1<<20, bare, false), smallest(1<<20, divBare, false); a != b {
				t.Fatalf("bare (%s)^-1: work %d, Div's %d", in, a, b)
			}
		}
	}
}

// TestPowCountedWorkWithinTariff is the counted-loop check of the Pow
// tariff: over random operands, exponents and precisions — bare
// exact powers, terminating reciprocals, context powers decided at a
// level, after escalation, by the exact path, and forced through every
// level to the exact fallback by the test seam — the kernel's counted
// work (Mul-family units plus the Div kernel's) never exceeds the charge
// B, which is the smallest admitting work cap bare and that cap minus
// 2N+1 in context. Each context B is also pinned to the tariff's
// structure: the levels run at 4·⌈log2|n|⌉·(t(w)²+2w) each (plus two
// division bounds for n < 0), plus, when the exact path ran, its tariff
// within the bracket's width.
func TestPowCountedWorkWithinTariff(t *testing.T) {
	r := rand.New(rand.NewPCG(53, 48))
	cases := 600
	if testing.Short() {
		cases = 150
	}
	var levelsSeen, exactSeen, forcedSeen int
	for i := range cases {
		c := powOperandFor(r, 40)
		if c.Sign() == 0 {
			continue
		}
		c.Abs(c)
		n := int32(r.IntN(81) - 40)
		if n >= -1 && n <= 1 {
			n = 2 + int32(r.IntN(30))
		}
		x := powDecimal(c, int64(r.IntN(7)-3))
		stripped, z := powStripped(c)
		d := uint64(len(stripped.String()))
		m := powMagnitude(n)
		if n > 0 {
			cnt := &powCount{}
			if _, _, err := x.powUnlimited(n, limits{}, "Pow", cnt); err != nil {
				t.Fatal(err)
			}
			run := func(b Budget) error { _, _, err := x.PowWithContext(n, Context{}.WithBudget(b)); return err }
			w := smallestAdmitting(1<<50, func(v uint64) bool { return run(Budget{MaxWork: v}) == nil })
			if cnt.work > w {
				t.Fatalf("case %d (%v)^%d: counted %d > B %d", i, x, n, cnt.work, w)
			}
		}
		p := uint32(1 + r.IntN(40))
		ctx := mustContext(t, p, allModes[r.IntN(7)])
		for _, forced := range []bool{false, true} {
			cnt := &powCount{escalate: forced}
			got, _, err := x.powContext(n, ctx, limits{}, "PowWithContext", cnt)
			if err != nil {
				t.Fatal(err)
			}
			run := func(b Budget) error {
				_, _, err := x.powContext(n, ctx, b.arith(), "PowWithContext", &powCount{escalate: forced})
				return err
			}
			w := smallestAdmitting(1<<60, func(v uint64) bool { return run(Budget{MaxWork: v}) == nil })
			base := w - 2*got.CoefficientDigits() - 1
			counted := cnt.work + cnt.div.units
			if counted > base {
				t.Fatalf("case %d (%v)^%d p=%d forced=%v: counted %d > B %d", i, x, n, p, forced, counted, base)
			}
			levels := powTestScan(z)
			for _, lw := range cnt.levels {
				levels += powTestLevel(lw, m, uint64(p), n < 0)
			}
			if !cnt.exact {
				levelsSeen++
				if base != levels {
					t.Fatalf("case %d (%v)^%d p=%d: B %d, levels %d", i, x, n, p, base, levels)
				}
				continue
			}
			exactSeen++
			if forced && len(cnt.levels) > 0 {
				forcedSeen++
			}
			size := powActualDigits(stripped)
			lower := levels + powTestSteps(m, d, size)
			upper := levels + powTestSteps(m, d, func(k uint64) uint64 { return min(size(k)+1, k*d) })
			if n < 0 {
				lower += powTestDiv(size(m), uint64(p))
				upper += powTestDiv(min(size(m)+1, m*d), uint64(p))
			}
			if base < lower || base > upper {
				t.Fatalf("case %d (%v)^%d p=%d forced=%v: B %d outside [%d, %d] (z=%d)", i, x, n, p, forced, base, lower, upper, z)
			}
		}
	}
	if levelsSeen < cases/5 || exactSeen < cases/5 || forcedSeen < cases/5 {
		t.Fatalf("vacuous sweep: %d level, %d exact, %d forced", levelsSeen, exactSeen, forcedSeen)
	}
}

// TestPowRefusesBeforeAllocating covers resource safety for Pow: a work cap
// below the exact charge, or a digit cap below Dlo + n·z, refuses with only
// its error allocated, as do the digit caps of 2^MaxInt32 and 2^MinInt32
// (whose results would have hundreds of millions of digits); a context work
// cap below the first level refuses before that level's scratch; and a cap
// that admits one level refuses the next before allocating it (seam-forced,
// 300-digit precision so every level's scratch is on the heap).
func TestPowRefusesBeforeAllocating(t *testing.T) {
	x := MustParse(strings.Repeat("123456789", 30) + "E-100")
	run := func(b Budget) error { _, _, err := x.PowWithContext(20, Context{}.WithBudget(b)); return err }
	w := smallestAdmitting(1<<40, func(v uint64) bool { return run(Budget{MaxWork: v}) == nil })
	n := smallestAdmitting(1<<20, func(v uint64) bool { return run(Budget{MaxDigits: v}) == nil })
	o := newPowOperand(x)
	dlo, _, _ := o.log.digits(o.d, 20)
	for _, tc := range []struct {
		name string
		run  func() error
	}{
		{"bare work", func() error { return run(Budget{MaxWork: w - 1}) }},
		{"bare digits below Dlo", func() error { return run(Budget{MaxDigits: dlo - 1}) }},
		{"2^MaxInt32", func() error {
			_, _, err := MustParse("2").PowWithContext(math.MaxInt32, Context{}.WithBudget(Budget{MaxDigits: 1_000_000}))
			return err
		}},
		{"2^MinInt32", func() error {
			_, _, err := MustParse("2").PowWithContext(math.MinInt32, Context{}.WithBudget(Budget{MaxDigits: 1_000_000}))
			return err
		}},
		{"1.0001^MaxInt32 context", func() error {
			_, _, err := MustParse("1.0001").PowWithContext(math.MaxInt32, mustContext(t, 300, TiesToEven).WithBudget(Budget{MaxWork: 1000}))
			return err
		}},
	} {
		if allocs := testing.AllocsPerRun(5, func() { _ = tc.run() }); allocs != 1 {
			t.Fatalf("%s: %v allocations, want only the error", tc.name, allocs)
		}
		if err := tc.run(); !errors.Is(err, ErrInsufficientStorage) {
			t.Fatalf("%s: %v", tc.name, err)
		}
	}
	if n <= dlo-1 {
		t.Fatalf("smallest digit cap %d at or below Dlo−1 = %d", n, dlo-1)
	}
	// One level admitted, the second refused before its scratch.
	ctx := mustContext(t, 300, TiesToEven)
	y := MustParse("1.0001")
	first := powTestLevel(300+1+powGuard(1000), 1000, 300, false)
	forced := func() error {
		_, _, err := y.powContext(1000, ctx, limits{MaxWork: first + 700}, "PowWithContext", &powCount{escalate: true})
		return err
	}
	if err := forced(); !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("second level: %v", err)
	}
	if allocs := testing.AllocsPerRun(5, func() { _ = forced() }); allocs != 3 {
		// The first level's scratch, the seam's level record and the error.
		t.Fatalf("second-level refusal: %v allocations, want 3", allocs)
	}
}

// TestPowHugeExponentBudgets covers the level-by-level charging
// with huge exponents: 1.0001^1000000 at p=34 (whose exact power has
// about five million digits) runs under the budget EstimatePow
// returns, decides at its first level, and its smallest admitting work is
// that level plus 2N+1 — far below the worst-case estimate — while the
// bare forms with 2^MaxInt32-sized results are refused by digit caps.
func TestPowHugeExponentBudgets(t *testing.T) {
	x := MustParse("1.0001")
	ctx := Decimal128Context()
	est, err := EstimatePow(x.Shape(), 1000000, ctx)
	if err != nil {
		t.Fatal(err)
	}
	cnt := &powCount{}
	got, _, err := x.powContext(1000000, ctx, est.Budget().arith(), "PowWithContext", cnt)
	if err != nil || len(cnt.levels) != 1 || cnt.exact {
		t.Fatalf("1.0001^1e6: %v %v, levels %v", got, err, cnt.levels)
	}
	first := powTestScan(0) + powTestLevel(cnt.levels[0], 1000000, 34, false)
	w := smallestAdmitting(est.WorkUnits, func(v uint64) bool {
		_, _, err := x.PowWithContext(1000000, ctx.WithBudget(Budget{MaxWork: v}))
		return err == nil
	})
	if w != first+2*got.CoefficientDigits()+1 || est.WorkUnits < 1000*w {
		t.Fatalf("1.0001^1e6: work %d, first level %d, estimate %d", w, first, est.WorkUnits)
	}
	if got.String() != "2.674710993142140172948354481790713E+43" {
		// 1.0001^10⁶ = 26747109931421401729483544817907127664007597.525…
		// (Python decimal at 60 digits), far from a rounding boundary.
		t.Fatalf("1.0001^1e6 = %v", got)
	}
	for _, n := range []int32{math.MaxInt32, math.MinInt32, 1 << 30} {
		if _, _, err := MustParse("7").PowWithContext(n, Context{}.WithBudget(Budget{MaxDigits: 1 << 20})); !errors.Is(err, ErrInsufficientStorage) && !errors.Is(err, ErrInexact) {
			t.Fatalf("7^%d: %v", n, err)
		}
	}
}

// TestPowAllocations covers the allocation class of Pow:
// inline results allocate nothing (bare powers and reciprocals, and
// Decimal128 context powers, whose truncated levels use stack scratch);
// results of at most 81 digits allocate once (the fused holder), with or
// without appended cohort zeros.
func TestPowAllocations(t *testing.T) {
	for _, tc := range []struct {
		name  string
		run   func()
		allow float64
	}{
		{"bare inline", func() { _, _ = MustParse("1.5").Pow(7) }, 0},
		{"bare inline reciprocal", func() { _, _ = MustParse("2").Pow(-9) }, 0},
		{"bare inline with zeros", func() { _, _ = MustParse("120").Pow(3) }, 0},
		{"bare 48 digits", func() { _, _ = MustParse("3").Pow(100) }, 1},
		{"bare 80 digits", func() { _, _ = MustParse("12345678901234567890").Pow(4) }, 1},
		{"bare 81 digits with zeros", func() { _, _ = MustParse("1234567890123456789000").Pow(3) }, 1},
		{"context Decimal128", func() { _, _, _ = MustParse("1.05").PowWithContext(365, Decimal128Context()) }, 0},
		{"context Decimal128 reciprocal", func() { _, _, _ = MustParse("3").PowWithContext(-77, Decimal128Context()) }, 0},
		{"context exact path", func() { _, _, _ = MustParse("1.1").PowWithContext(10, Decimal128Context()) }, 0},
		{"context 81 digits", func() { _, _, _ = MustParse("7").PowWithContext(1000, mustContext(t, 81, TiesToEven)) }, 1},
	} {
		if n := testing.AllocsPerRun(50, tc.run); n != tc.allow {
			t.Fatalf("%s: %v allocations, want %v", tc.name, n, tc.allow)
		}
	}
}

// powTestLnPrec is the oracle logarithm's precision: 192 bits, far below
// the 2⁻⁶⁴ grid the bracket is checked on.
const powTestLnPrec = 192

// powTestAtanh2 is 2·atanh((u−1)/(u+1)) = ln u for u ∈ [1, 2], the series
// summed until its terms vanish at the working precision.
func powTestAtanh2(u *big.Float) *big.Float {
	const prec = powTestLnPrec
	one := new(big.Float).SetPrec(prec).SetInt64(1)
	t := new(big.Float).SetPrec(prec).Quo(new(big.Float).SetPrec(prec).Sub(u, one), new(big.Float).SetPrec(prec).Add(u, one))
	t2 := new(big.Float).SetPrec(prec).Mul(t, t)
	sum, term := new(big.Float).SetPrec(prec), new(big.Float).SetPrec(prec).Set(t)
	for k := int64(1); term.Sign() != 0 && term.MantExp(nil) > -prec-8; k += 2 {
		sum.Add(sum, new(big.Float).SetPrec(prec).Quo(term, new(big.Float).SetPrec(prec).SetInt64(k)))
		term.Mul(term, t2)
	}
	return sum.Mul(sum, new(big.Float).SetPrec(prec).SetInt64(2))
}

// powTestLn is ln(y) for y ≥ 1, independently of the kernel: y = 2^j·u
// with u ∈ [1, 2) and ln y = j·ln 2 + ln u, given ln2 = powTestAtanh2(2).
func powTestLn(y, ln2 *big.Float) *big.Float {
	const prec = powTestLnPrec
	u := new(big.Float).SetPrec(prec).Set(y)
	j := int64(0)
	two := new(big.Float).SetPrec(prec).SetInt64(2)
	for u.Cmp(two) >= 0 {
		u.Quo(u, two)
		j++
	}
	r := new(big.Float).SetPrec(prec).Mul(ln2, new(big.Float).SetPrec(prec).SetInt64(j))
	return r.Add(r, powTestAtanh2(u))
}

// TestPowLogBracket covers the rigor of the digit bracket directly: for
// random coefficients of 1–60 digits (random, a 19-digit top followed by
// nines or zeros, tops just above and below 2^j·10¹⁸, tops just above
// 10¹⁸, 2·10¹⁸, √2·10¹⁸, 2√2·10¹⁸ and 2^(1/4)·10¹⁸, where the final
// roundings leave least slack, and tops next to 10¹⁹), the fixed-point
// bracket encloses log10(c/10^(d−1)) computed at
// 192 bits by an independent atanh series — lo·2⁻⁶⁴ ≤ λ(c) ≤ hi·2⁻⁶⁴,
// with hi ≥ 1 reported as one — and is at most 16 units wide.
func TestPowLogBracket(t *testing.T) {
	r := rand.New(rand.NewPCG(53, 50))
	const prec = powTestLnPrec
	ln2 := powTestAtanh2(new(big.Float).SetPrec(prec).SetInt64(2))
	ln10 := powTestLn(new(big.Float).SetPrec(prec).SetInt64(10), ln2)
	scale := new(big.Float).SetPrec(prec).SetMantExp(new(big.Float).SetPrec(prec).SetInt64(1), 64)
	tops := []string{"1000000000000000000", "9999999999999999999", "2000000000000000000", "1999999999999999999", "4000000000000000001", "7999999999999999999", "8000000000000000000", "3162277660168379332"}
	cases := 16000
	if testing.Short() {
		cases = 4000
	}
	for i := range cases {
		var digits string
		switch {
		case i < len(tops)*4:
			digits = tops[i%len(tops)] + []string{"", "9", strings.Repeat("9", 30), "0000001"}[i/len(tops)]
		case i%5 == 0:
			digits = randomDigits(r, 19).String() + strings.Repeat("9", 1+r.IntN(30))
		case i%5 == 1:
			// Tops just above 10¹⁸ and 2·10¹⁸, where log2 of the reduced
			// value is near 0 and the final rounding leaves least slack.
			anchors := []string{"1000000000000000000", "2000000000000000000", "1414213562373095049", "2828427124746190098", "1189207115002721067"}
			top, _ := new(big.Int).SetString(anchors[r.IntN(len(anchors))], 10)
			top.Add(top, randomDigits(r, 1+r.IntN(17)))
			digits = top.String() + []string{"", "7", "123456789"}[r.IntN(3)]
		default:
			digits = randomDigits(r, 1+r.IntN(60)).String()
		}
		c, _ := new(big.Int).SetString(digits, 10)
		o := newPowOperand(powDecimal(c, 0))
		stripped, _ := powStripped(c)
		y := new(big.Float).SetPrec(prec).Quo(new(big.Float).SetPrec(prec).SetInt(stripped), new(big.Float).SetPrec(prec).SetInt(new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(o.d-1)), nil)))
		lambda := new(big.Float).SetPrec(prec).Quo(powTestLn(y, ln2), ln10)
		lambda.Mul(lambda, scale)
		lo := new(big.Float).SetPrec(prec).SetUint64(o.log.lo)
		if lo.Cmp(lambda) > 0 {
			t.Fatalf("%s: lower bound %d above λ·2⁶⁴ = %s", digits, o.log.lo, lambda.Text('f', 3))
		}
		if o.log.one {
			if lambda.Cmp(new(big.Float).SetPrec(prec).Sub(scale, new(big.Float).SetInt64(16))) < 0 {
				t.Fatalf("%s: one reported for λ·2⁶⁴ = %s", digits, lambda.Text('f', 3))
			}
			continue
		}
		hi := new(big.Float).SetPrec(prec).SetUint64(o.log.hi)
		if hi.Cmp(lambda) < 0 {
			t.Fatalf("%s: upper bound %d below λ·2⁶⁴ = %s", digits, o.log.hi, lambda.Text('f', 3))
		}
		if o.log.hi-o.log.lo > 16 {
			t.Fatalf("%s: bracket [%d, %d] wider than 16 units", digits, o.log.lo, o.log.hi)
		}
	}
}

// TestPowLog2Bits checks the repeated-squaring kernel of the bracket on
// its own: for random y = Y·2⁻⁶³ ∈ [1, 2) (uniform, and just above 1, √2
// and 2^(1/4)), the rounding-down bits B and rounding-up bits B′ satisfy
// B·2⁻⁶² ≤ log2 y < (B′+1)·2⁻⁶² against the 192-bit atanh logarithm, and
// B′ − B ≤ 2.
func TestPowLog2Bits(t *testing.T) {
	r := rand.New(rand.NewPCG(53, 51))
	const prec = powTestLnPrec
	ln2 := powTestAtanh2(new(big.Float).SetPrec(prec).SetInt64(2))
	unit := new(big.Float).SetPrec(prec).SetMantExp(new(big.Float).SetPrec(prec).SetInt64(1), -62)
	anchors := []uint64{1 << 63, 13043817825332782212, 10968499437862720130}
	cases := 8000
	if testing.Short() {
		cases = 2000
	}
	for i := range cases {
		y := uint64(1)<<63 | r.Uint64()
		if i%2 == 0 {
			y = anchors[r.IntN(len(anchors))] + r.Uint64()>>uint(8+r.IntN(56))
		}
		v := new(big.Float).SetPrec(prec).SetMantExp(new(big.Float).SetPrec(prec).SetUint64(y), -63)
		log2 := new(big.Float).SetPrec(prec).Quo(powTestAtanh2(v), ln2)
		down, up := powLog2(y, false), powLog2(y, true)
		lo := new(big.Float).SetPrec(prec).Mul(new(big.Float).SetPrec(prec).SetUint64(down), unit)
		hi := new(big.Float).SetPrec(prec).Mul(new(big.Float).SetPrec(prec).SetUint64(up+1), unit)
		if lo.Cmp(log2) > 0 || hi.Cmp(log2) <= 0 || up-down > 2 {
			t.Fatalf("y = %d·2⁻⁶³: bits [%d, %d+1] miss log2 y = %s", y, down, up, log2.Text('g', 30))
		}
	}
}

// TestPowLevelRejectsExactValues pins the acceptance rule of a truncated
// level where the public path cannot reach it: a
// level whose width holds the whole power computes C^m exactly, and must
// then decline a reciprocal whose value is exactly its (p+1)-digit prefix,
// since a below-half class would be wrong. For 5⁻ᵏ, 25⁻ᵏ and 125⁻ᵏ with
// 2^(b·k) of at most p+1 digits, powLevel at w ≥ digits(c^k) declines; for
// inexact reciprocals (3⁻ᵏ, 7⁻ᵏ, 2⁻ᵏ) at the same widths it accepts
// the true prefix, which big.Int confirms.
func TestPowLevelRejectsExactValues(t *testing.T) {
	declined, accepted := 0, 0
	for _, c := range []int64{5, 25, 125, 3, 7, 2} {
		for m := uint64(2); m <= 30; m++ {
			power := new(big.Int).Exp(big.NewInt(c), new(big.Int).SetUint64(m), nil)
			d := uint64(len(power.String()))
			o := newPowOperand(New(c, 0))
			for p := uint64(1); p+1 < d; p++ {
				w := d + uint64(m%3)
				buf := make([]uint32, powLevelLimbs(w, p, true))
				arena := powArena{buf: buf}
				q, f, ok := o.powLevel(m, w, p, true, &arena, nil)
				// At w ≥ d the bounds are c^m itself, so the prefix exponent is
				// that of 1/c^m's (p+1)th digit: −d − p. Test 1/c^m·10^(d+p).
				want := -int64(d) - int64(p)
				if ok && f != want {
					t.Fatalf("1/%d^%d p=%d w=%d: prefix exponent %d, want %d", c, m, p, w, f, want)
				}
				scaled := new(big.Rat).Mul(new(big.Rat).SetFrac(big.NewInt(1), power), pow10Rat(-want))
				floor := new(big.Int).Quo(scaled.Num(), scaled.Denom())
				exact := scaled.IsInt()
				switch {
				case exact && ok:
					t.Fatalf("1/%d^%d p=%d w=%d: accepted the exact value %v", c, m, p, w, floor)
				case exact:
					declined++
				case ok:
					if publishScratch(q, 0, false).coefficientDigits() != floor.String() {
						t.Fatalf("1/%d^%d p=%d w=%d: prefix %v, want %v", c, m, p, w, q, floor)
					}
					accepted++
				}
			}
		}
	}
	if declined < 50 || accepted < 500 {
		t.Fatalf("vacuous: %d exact declined, %d inexact accepted", declined, accepted)
	}
}

// TestPowDirectedEnclosure covers the directed-rounding enclosure and
// tightness property for PowWithContext: TowardNegativeInfinity
// and TowardPositiveInfinity return the floor and ceiling of x^n on the
// grid the rounding used (the p-digit grid of the power's decade, never
// below Etiny under guards), so they bracket the exact power with no
// representable value strictly between, including a carry into a new
// decade (3.16² = 9.9856 at p=2 is 9.9 and 10) and negative odd powers.
func TestPowDirectedEnclosure(t *testing.T) {
	r := rand.New(rand.NewPCG(53, 52))
	type sample struct {
		c      *big.Int
		e, n   int64
		p      int64
		guards *ExponentGuards
	}
	samples := []sample{
		{big.NewInt(316), -2, 2, 2, nil},
		{big.NewInt(-316), -2, 3, 2, nil},
		{big.NewInt(3), 0, -5, 4, nil},
		{big.NewInt(5), -1, 7, 3, &ExponentGuards{Emin: -4, Emax: 4}},
	}
	cases := 6000
	if testing.Short() {
		cases = 1200
	}
	for range cases {
		s := sample{c: powOperandFor(r, 20), e: int64(r.IntN(9) - 4), n: int64(r.IntN(61) - 30), p: int64(1 + r.IntN(30))}
		if s.c.Sign() == 0 {
			continue
		}
		if r.IntN(3) == 0 {
			emin := int32(r.IntN(41) - 30)
			s.guards = &ExponentGuards{Emin: emin, Emax: emin + int32(r.IntN(60))}
		}
		samples = append(samples, s)
	}
	checked, inexact := 0, 0
	for i, s := range samples {
		x := powDecimal(s.c, s.e)
		exact := powExactRat(s.c, s.e, s.n)
		loCtx, err := NewContext(uint32(s.p), TowardNegativeInfinity, s.guards, 0)
		if err != nil {
			t.Fatal(err)
		}
		hiCtx, _ := NewContext(uint32(s.p), TowardPositiveInfinity, s.guards, 0)
		lo, loConditions, loErr := x.PowWithContext(int32(s.n), loCtx)
		hi, hiConditions, hiErr := x.PowWithContext(int32(s.n), hiCtx)
		label := fmt.Sprintf("sample %d (%v)^%d p=%d %v", i, x, s.n, s.p, s.guards)
		if loErr != nil || hiErr != nil {
			t.Fatalf("%s: errors %v / %v", label, loErr, hiErr)
		}
		emin := int64(0)
		if s.guards != nil {
			emin = int64(s.guards.Emin)
		}
		if checkDirectedEnclosure(t, label, exact, directionPrecisionQuantum(exact, s.p, s.guards != nil, emin), lo, loConditions, hi, hiConditions) {
			checked++
			if loConditions&Inexact != 0 {
				inexact++
			}
		}
		if i == 0 && (lo.String() != "9.9" || hi.String() != "10") {
			t.Fatalf("%s: carry row %v %v", label, lo, hi)
		}
	}
	if checked < cases/2 || inexact < cases/4 {
		t.Fatalf("enclosure checked %d pairs, %d inexact", checked, inexact)
	}
}

// TestPowStraddlingBracket covers straddling brackets: 3162277660168379331²
// has 37 digits and …332² has 38, and both brackets straddle, Dlo = 37 <
// Dhi = 38. (a) A bare digit cap in [Dlo, Dhi) + n·z, the one case the
// publication cap decides, admits exactly when the actual digits fit,
// with and without cohort zeros. (b) At p = 36 (Dlo = p+1) the context
// matches the oracle in all eight modes. (c) Under guards with Emax = 10
// the value certainly overflows, but a straddle takes the exact path, so
// W = 2p+1 is refused and the smallest admitting work is the scan, the
// exact tariff and 2p+1.
func TestPowStraddlingBracket(t *testing.T) {
	for _, in := range []string{"3162277660168379331", "3162277660168379332", "31622776601683793310", "3162277660168379332000"} {
		x := MustParse(in)
		c, _ := new(big.Int).SetString(in, 10)
		stripped, z := powStripped(c)
		o := newPowOperand(x)
		lo, hi, _ := o.log.digits(o.d, 2)
		if hi != lo+1 || lo != 37 {
			t.Fatalf("%s: bracket [%d, %d] does not straddle 37", in, lo, hi)
		}
		actual := uint64(len(new(big.Int).Mul(c, c).String()))
		for cap := lo + 2*z - 1; cap <= hi+2*z; cap++ {
			got, _, err := x.PowWithContext(2, Context{}.WithBudget(Budget{MaxDigits: cap}))
			if (err == nil) != (cap >= actual) || err == nil && got.CoefficientDigits() != actual {
				t.Fatalf("%s² under digit cap %d (actual %d): %v %v", in, cap, actual, got, err)
			}
			if err != nil && !errors.Is(err, ErrInsufficientStorage) {
				t.Fatalf("%s² under digit cap %d: %v", in, cap, err)
			}
		}
		if z == 0 {
			for _, mode := range allModes {
				got, conditions, err := x.PowWithContext(2, mustContext(t, 36, mode))
				want := powOracle(powExactRat(c, 0, 2), 0, 36, mode, powGuardsOracle{})
				powCheck(t, fmt.Sprintf("%s² p=36 %v", in, mode), got, conditions, err, want, false)
			}
		}
		ctx := mustGuarded(t, 36, TiesToEven, -100, 10, 0)
		if _, _, err := x.PowWithContext(2, ctx.WithBudget(Budget{MaxWork: 73})); !errors.Is(err, ErrInsufficientStorage) {
			t.Fatalf("%s² guarded at W = 2p+1: %v", in, err)
		}
		size := powActualDigits(stripped)
		d := uint64(len(stripped.String()))
		w := smallestAdmitting(1<<30, func(v uint64) bool {
			_, _, err := x.PowWithContext(2, ctx.WithBudget(Budget{MaxWork: v}))
			return err == nil
		})
		lower := powTestScan(z) + powTestSteps(2, d, size) + 73
		upper := powTestScan(z) + powTestSteps(2, d, func(k uint64) uint64 { return min(size(k)+1, k*d) }) + 73
		if w < lower || w > upper {
			t.Fatalf("%s² guarded: smallest work %d outside [%d, %d]", in, w, lower, upper)
		}
		got, conditions, _ := x.PowWithContext(2, ctx)
		if got.coefficientDigits() != strings.Repeat("9", 36) || got.Exponent() != 10-36+1 || conditions&Overflow == 0 {
			t.Fatalf("%s² guarded: %v %v", in, got, conditions)
		}
	}
}

// TestPowReciprocalBareCharges covers the bare reciprocal tariff: n ≤ −2
// charges the scan, the terminating test t(d)·(1 + ⌊a_max/q⌋) and the exact
// plan of the power of 5 or 2 the reciprocal is, restated here from actual
// digit counts. 8⁻³ = 0.001953125 is 1 + 1 + 23 = 25 (24 plus the
// one-limb scan). powPredicateMax bounds the
// largest a with 2^a (or 5^a) below 10^d, within one, for every d ≤ 2000.
func TestPowReciprocalBareCharges(t *testing.T) {
	for _, tc := range []struct {
		x    string
		want uint64 // 0: the restated closed form only
	}{{"8", 25}, {"64", 0}, {"0.125", 0}, {"3.90625", 0}, {"2E+5", 0}, {"1024", 0}, {"0.0000000009765625", 0}} {
		x := MustParse(tc.x)
		w := smallestAdmitting(1<<40, func(v uint64) bool {
			_, _, err := x.PowWithContext(-3, Context{}.WithBudget(Budget{MaxWork: v}))
			return err == nil
		})
		c, _ := divOracleParts(t, x)
		stripped, z := powStripped(c)
		d := uint64(len(stripped.String()))
		five := new(big.Int).Mod(stripped, big.NewInt(5)).Sign() == 0
		base, amax, step := int64(5), d*3322/1000, uint64(29)
		a := uint64(0)
		for v := new(big.Int).Set(stripped); v.Cmp(big.NewInt(1)) > 0; a++ {
			if five {
				v.Quo(v, big.NewInt(5))
			} else {
				v.Quo(v, big.NewInt(2))
			}
		}
		if five {
			base, amax, step = 2, d*1431/1000, 12
		}
		size := powActualDigits(big.NewInt(base))
		want := powTestScan(z) + powTestLimbs(d)*(1+amax/step) + powTestSteps(3*a, 1, size)
		if w != want || tc.want != 0 && w != tc.want {
			t.Fatalf("(%s)^-3: smallest work %d, closed form %d (pinned %d)", tc.x, w, want, tc.want)
		}
	}
	two, five := big.NewInt(1), big.NewInt(1)
	var a2, a5 uint64
	for d := uint64(1); d <= 2000; d++ {
		limit := new(big.Int).Exp(big.NewInt(10), new(big.Int).SetUint64(d), nil)
		for new(big.Int).Lsh(two, 1).Cmp(limit) < 0 {
			two.Lsh(two, 1)
			a2++
		}
		for new(big.Int).Mul(five, big.NewInt(5)).Cmp(limit) < 0 {
			five.Mul(five, big.NewInt(5))
			a5++
		}
		if m2, m5 := powPredicateMax(d, false), powPredicateMax(d, true); m2 < a2 || m2 > a2+1 || m5 < a5 || m5 > a5+1 {
			t.Fatalf("d=%d: powPredicateMax %d and %d, largest powers 2^%d and 5^%d", d, m2, m5, a2, a5)
		}
	}
}

// TestPowContextExactScratchIsResultSized checks that the context exact
// path sizes its cohort pad by the result, not by the context precision,
// so a huge precision costs nothing the result does not need, and a digit
// or work budget refuses before any large allocation. Sizing by precision
// would make 123456789² at p = 2³²−1 allocate 1.8 GB, also under
// {MaxDigits: 10, MaxWork: 100} before refusing.
func TestPowContextExactScratchIsResultSized(t *testing.T) {
	huge := mustContext(t, math.MaxUint32, TiesToEven)
	const limit = 64 << 10
	for _, tc := range []struct {
		name   string
		x      string
		n      int32
		budget Budget
		want   string
		err    error
	}{
		{"exact square", "123456789", 2, Budget{}, "15241578750190521", nil},
		{"cohort padding", "1000", 3, Budget{}, "1000000000", nil},
		{"zero-heavy cohort", "1.000E+5", 2, Budget{}, "1.000000E+10", nil},
		{"digit cap", "123456789", 2, Budget{MaxDigits: 10, MaxWork: 100}, "", ErrInsufficientStorage},
		{"digit cap at the result", "123456789", 2, Budget{MaxDigits: 17}, "15241578750190521", nil},
		{"digit cap below the cohort", "1000", 3, Budget{MaxDigits: 9}, "", ErrInsufficientStorage},
		{"digit cap at the cohort", "1000", 3, Budget{MaxDigits: 10}, "1000000000", nil},
		{"digit cap below a long cohort", "10", 1 << 30, Budget{MaxDigits: 1000}, "", ErrInsufficientStorage},
		{"exponent range", "1.23456789E+2147483600", 2, Budget{}, "", ErrExponentRange},
	} {
		x := MustParse(tc.x)
		var got Decimal
		var err error
		bytes := coldAllocatedWithin(func() { got, _, err = x.PowWithContext(tc.n, huge.WithBudget(tc.budget)) }, limit)
		if tc.err != nil {
			if !errors.Is(err, tc.err) {
				t.Errorf("%s: %v, want %v", tc.name, err, tc.err)
			}
		} else if err != nil || got.String() != tc.want {
			t.Errorf("%s: %v %v, want %s", tc.name, got, err, tc.want)
		}
		if bytes > limit {
			t.Errorf("%s: %d bytes allocated at p = 2^32-1, want at most %d", tc.name, bytes, limit)
		}
	}
}

// TestPowGuardedContextRefusesBeforeAllocation is the guarded variant of
// TestPowContextExactScratchIsResultSized: the huge cohort is not
// allocated on refusal.
func TestPowGuardedContextRefusesBeforeAllocation(t *testing.T) {
	for _, mode := range []RoundingMode{TiesToEven, Exact} {
		for _, tc := range []struct {
			name   string
			x      Decimal
			guards ExponentGuards
			want   error
			zero   bool
		}{
			{"normal", New(10, 0), ExponentGuards{Emin: -100, Emax: math.MaxInt32}, ErrInsufficientStorage, false},
			{"overflow", New(10, 0), ExponentGuards{Emin: -100, Emax: 100}, ErrInsufficientStorage, false},
			{"underflow", New(10, -2), ExponentGuards{Emin: (1 << 25) - 1, Emax: math.MaxInt32}, nil, true},
		} {
			ctx, err := NewContext(1<<25, mode, &tc.guards, 0)
			if err != nil {
				t.Fatal(err)
			}
			var got Decimal
			var cond Conditions
			bytes := coldAllocatedWithin(func() {
				got, cond, err = tc.x.PowWithContext(1<<24, ctx.WithBudget(Budget{MaxDigits: 1000, MaxWork: 10000}))
			}, 65536)
			if mode == Exact && tc.name != "normal" {
				var ce *Error
				if !errors.As(err, &ce) || ce.Code != 0 || ce.Condition != Inexact || cond != 0 {
					t.Errorf("%s Exact: %v %v", tc.name, cond, err)
				}
			} else if tc.zero {
				if err != nil || !got.IsZero() || got.Exponent() != 0 || cond != Subnormal|Underflow|Inexact|Rounded|Decreased {
					t.Errorf("%s: %v %v %v", tc.name, got, cond, err)
				}
			} else if !errors.Is(err, tc.want) || cond != 0 {
				t.Errorf("%s mode%v: %v %v", tc.name, mode, cond, err)
			}
			if bytes > 65536 {
				t.Errorf("%s mode%v heap%d", tc.name, mode, bytes)
			}
		}
	}
}

// TestPowContextBudgetPreservesRefusalPrecedence checks that Exact and
// exponent range failures precede the publication digit cap.
// An uncapped public call is the general-path differential; errors and
// successful coefficients independently determine the capped outcome.
func TestPowContextBudgetPreservesRefusalPrecedence(t *testing.T) {
	var compared, exactRefusals, rangeRefusals, capRefusals int
	for _, input := range []string{"11", "-11", "1000", "9.99", "1.25", "1E+2147483647", "1E-2147483648"} {
		x := MustParse(input)
		for _, p := range []uint32{1, 2, 3, 8} {
			for mode := TiesToEven; mode <= Exact; mode++ {
				for _, guards := range []*ExponentGuards{nil, {Emin: -2, Emax: 4}} {
					ctx, err := NewContext(p, mode, guards, 0)
					if err != nil {
						t.Fatal(err)
					}
					baseline, bc, be := x.PowWithContext(2, ctx)
					for _, cap := range []uint64{1, 2, 3, 9} {
						got, gc, ge := x.PowWithContext(2, ctx.WithBudget(Budget{MaxDigits: cap}))
						compared++
						if be != nil {
							var ce *Error
							switch {
							case errors.As(be, &ce) && ce.Code == 0:
								exactRefusals++
								var actual *Error
								if !errors.As(ge, &actual) || actual.Condition != ce.Condition || gc != bc {
									t.Errorf("%s p%d mode%v guards%v cap%d: got %v %v want %v %v", input, p, mode, guards, cap, gc, ge, bc, be)
								}
							case errors.Is(be, ErrExponentRange):
								rangeRefusals++
								if !errors.Is(ge, ErrExponentRange) || gc != 0 {
									t.Errorf("range %s p%d cap%d: %v %v", input, p, cap, gc, ge)
								}
							default:
								t.Fatal(be)
							}
						} else if baseline.CoefficientDigits() > cap {
							capRefusals++
							if !errors.Is(ge, ErrInsufficientStorage) || gc != 0 {
								t.Errorf("cap %s p%d mode%v: %v %v", input, p, mode, gc, ge)
							}
						} else if ge != nil || gc != bc || got.String() != baseline.String() {
							t.Errorf("success %s p%d mode%v: %v %v %v; want %v %v", input, p, mode, got, gc, ge, baseline, bc)
						}
					}
				}
			}
		}
	}
	if compared < 1000 || exactRefusals == 0 || rangeRefusals == 0 || capRefusals == 0 {
		t.Fatalf("vacuous comparisons %d exact %d range %d cap %d", compared, exactRefusals, rangeRefusals, capRefusals)
	}
}

// TestPowNegativeHugePrecisionBound checks that a short terminating
// reciprocal must not allocate scratch proportional to unused precision.
// The baseline witness uses 2^18 rather than MaxUint32, bounding a failed
// run below one MiB. math/big derives the exact value independently.
func TestPowNegativeHugePrecisionBound(t *testing.T) {
	for _, n := range []int32{-1, -2, -3} {
		for _, precision := range []uint32{256, 1 << 18} {
			t.Run(fmt.Sprintf("n%d/p%d", n, precision), func(t *testing.T) {
				ctx, err := NewContext(precision, TiesToEven, nil, 0)
				if err != nil {
					t.Fatal(err)
				}
				var got Decimal
				var conditions Conditions
				const limit = 32 << 10
				used := coldAllocatedWithin(func() {
					got, conditions, err = New(2, 0).PowWithContext(n, ctx)
				}, limit)
				if err != nil || conditions != 0 {
					t.Fatalf("terminating reciprocal: got %v, %v, %v", got, conditions, err)
				}
				want := powExactRat(big.NewInt(2), 0, int64(n))
				actual, ok := new(big.Rat).SetString(got.String())
				if !ok || actual.Cmp(want) != 0 || got.exponent() != n {
					t.Fatalf("reciprocal: got %v exponent%d; want %s exponent%d", got, got.exponent(), want, n)
				}
				if used > limit {
					t.Fatalf("unused precision allocated %d bytes; want <=%d", used, limit)
				}
			})
		}
	}
}

// TestPowNegativeMaxPrecision covers the largest precision scale
// without an enormous allocation: exact reciprocals at MaxUint32 precision
// fit a fixed heap envelope on every target, including executable 386.
func TestPowNegativeMaxPrecision(t *testing.T) {
	for _, guards := range []*ExponentGuards{nil, {Emin: math.MaxInt32, Emax: math.MaxInt32}} {
		for mode := TiesToEven; mode <= Exact; mode++ {
			ctx := contextTestContext(t, math.MaxUint32, mode, guards, 0)
			for _, n := range []int32{-1, -2, -3} {
				var got Decimal
				var c Conditions
				var err error
				used := coldAllocatedWithin(func() { got, c, err = New(2, 0).PowWithContext(n, ctx) }, 32<<10)
				want := powExactRat(big.NewInt(2), 0, int64(n))
				actual, ok := new(big.Rat).SetString(got.String())
				wantC := Conditions(0)
				if guards != nil {
					wantC = Subnormal
				}
				if err != nil || !ok || actual.Cmp(want) != 0 || got.Exponent() != n || c != wantC || used > 32<<10 {
					t.Fatalf("n%d mode%d guards%v: %v %v %v, heap%d; want %s e%d %v", n, mode, guards, got, c, err, used, want, n, wantC)
				}
				est, e := EstimatePow(New(2, 0).Shape(), n, ctx)
				if e != nil {
					t.Fatalf("terminating value succeeds but estimator refuses: n%d %v", n, e)
				}
				_, _, e = New(2, 0).PowWithContext(n, ctx.WithBudget(est.Budget()))
				if e != nil || used > est.HeapBytes {
					t.Fatalf("n%d under estimate %+v: %v, heap%d", n, est, e, used)
				}
			}
		}
	}
}

// TestPowNegativeProbeGuardPublication covers a large necessary
// output: a short exact reciprocal may overflow and require p nines. The
// digit and work quotas still apply; Exact refuses before publication.
func TestPowNegativeProbeGuardPublication(t *testing.T) {
	for _, n := range []int32{-1, -2, -3} {
		for mode := TiesToEven; mode <= Exact; mode++ {
			ctx := contextTestContext(t, 256, mode, &ExponentGuards{Emin: -2, Emax: -1}, 0)
			x := New(2, -1)
			got, c, err := x.PowWithContext(n, ctx)
			if mode == Exact {
				if !errors.Is(err, ErrInexact) || c != 0 || !isZeroValue(got) {
					t.Fatalf("Exact overflow n%d: %v %v %v", n, got, c, err)
				}
				continue
			}
			if err != nil || got.coefficientDigits() != strings.Repeat("9", 256) || got.Exponent() != -256 || c != Overflow|Inexact|Rounded|Decreased {
				t.Fatalf("overflow n%d mode%d: %v %v %v", n, mode, got, c, err)
			}
			used := coldAllocatedWithin(func() {
				_, _, err = x.PowWithContext(n, ctx.WithBudget(Budget{MaxDigits: 255}))
			}, 128)
			if !errors.Is(err, ErrInsufficientStorage) || used > 128 {
				t.Fatalf("overflow digit admission n%d: %v, heap%d", n, err, used)
			}
		}
	}
}

// TestPowNegativeProbeWorkTariff covers the reciprocal precharge:
// independently restated power/division bounds bracket the least admitted B,
// and measured kernel work, including a failed probe, fits that B.
func TestPowNegativeProbeWorkTariff(t *testing.T) {
	var terminating, repeating int
	for _, base := range []int64{2, 3, 5, 11, -2, -3} {
		for _, n := range []int32{-2, -3, -17} {
			const p = 4096
			x := New(base, 0)
			ctx := mustContext(t, p, TiesToEven)
			cnt := &powCount{}
			got, cond, err := x.powContext(n, ctx, limits{}, "PowWithContext", cnt)
			want := powOracle(powExactRat(big.NewInt(base), 0, int64(n)), 0, p, TiesToEven, powGuardsOracle{})
			powCheck(t, fmt.Sprintf("%d^%d", base, n), got, cond, err, want, base < 0 && n%2 != 0)
			if !cnt.exact || len(cnt.levels) != 0 {
				t.Fatalf("%d^%d did not exercise direct exact-power route", base, n)
			}
			if cond&Inexact == 0 {
				terminating++
			} else {
				repeating++
			}
			w := smallestAdmitting(1<<40, func(cap uint64) bool {
				_, _, e := x.PowWithContext(n, ctx.WithBudget(Budget{MaxWork: cap}))
				return e == nil
			})
			b := w - 2*got.CoefficientDigits() - 1
			c := new(big.Int).Abs(big.NewInt(base))
			d, m := uint64(len(c.String())), uint64(-n)
			size := powActualDigits(c)
			lo := powTestScan(0) + powTestSteps(m, d, size) + powTestDiv(size(m), p)
			hiSize := func(k uint64) uint64 { return min(size(k)+1, k*d) }
			hi := powTestScan(0) + powTestSteps(m, d, hiSize) + powTestDiv(hiSize(m), p)
			if b < lo || b > hi || cnt.work+cnt.div.units > b {
				t.Fatalf("%d^%d B%d outside [%d,%d] or counted%d exceeds it", base, n, b, lo, hi, cnt.work+cnt.div.units)
			}
			var refused error
			used := coldAllocatedWithin(func() { _, _, refused = x.PowWithContext(n, ctx.WithBudget(Budget{MaxWork: b - 1})) }, 128)
			if !errors.Is(refused, ErrInsufficientStorage) || used > 128 {
				t.Fatalf("precharge %d^%d: %v heap%d", base, n, refused, used)
			}
		}
	}
	if terminating != 9 || repeating != 9 {
		t.Fatalf("vacuous routes exact%d repeating%d", terminating, repeating)
	}
}
