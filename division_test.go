// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"errors"
	"fmt"
	"math"
	"math/big"
	"math/bits"
	"math/rand/v2"
	"reflect"
	"runtime"
	"slices"
	"strings"
	"testing"
)

// divRat is the independent oracle value of a Decimal.
func divRat(t *testing.T, d Decimal) *big.Rat {
	t.Helper()
	text, err := d.Text(0)
	if err != nil {
		t.Fatal(err)
	}
	r, ok := new(big.Rat).SetString(text)
	if !ok {
		t.Fatalf("oracle cannot read %q", text)
	}
	return r
}

func pow10Rat(e int64) *big.Rat {
	p := new(big.Int).Exp(big.NewInt(10), big.NewInt(max(e, -e)), nil)
	if e >= 0 {
		return new(big.Rat).SetInt(p)
	}
	return new(big.Rat).SetFrac(big.NewInt(1), p)
}

// oracleRound rounds |v| (nonnegative) to an integer under mode with sign
// negative, returning the magnitude and whether it changed.
func oracleRound(v *big.Rat, mode RoundingMode, negative bool) (*big.Int, bool) {
	floor := new(big.Int).Quo(v.Num(), v.Denom())
	frac := new(big.Rat).Sub(v, new(big.Rat).SetInt(floor))
	if frac.Sign() == 0 {
		return floor, false
	}
	half := frac.Cmp(big.NewRat(1, 2))
	up := false
	switch mode {
	case AwayFromZero:
		up = true
	case TowardPositiveInfinity:
		up = !negative
	case TowardNegativeInfinity:
		up = negative
	case TiesToEven:
		up = half > 0 || half == 0 && floor.Bit(0) == 1
	case TiesAwayFromZero:
		up = half >= 0
	case TiesTowardZero:
		up = half > 0
	}
	if up {
		floor.Add(floor, big.NewInt(1))
	}
	return floor, true
}

func divDigitsOf(n *big.Int) int64 {
	if n.Sign() == 0 {
		return 1
	}
	return int64(len(n.String()))
}

// divExpect is an oracle outcome: value as coefficient and exponent.
type divExpect struct {
	coefficient *big.Int
	exponent    int64
	conditions  Conditions
	refused     bool
}

func checkDivOutcome(t *testing.T, label string, got Decimal, conditions Conditions, err error, want divExpect, negative bool) {
	t.Helper()
	if want.refused {
		var ce *Error
		if !errors.As(err, &ce) || ce.Code != 0 || ce.Condition != Inexact || !isZeroValue(got) || conditions != 0 {
			t.Fatalf("%s: got (%v, %v, %v), want Exact refusal", label, got, conditions, err)
		}
		return
	}
	if err != nil {
		t.Fatalf("%s: unexpected error %v", label, err)
	}
	wantCoefficient := new(big.Int).Set(want.coefficient)
	if negative && wantCoefficient.Sign() != 0 {
		wantCoefficient.Neg(wantCoefficient)
	}
	gotBig, gotExp := divOracleParts(t, got)
	if gotBig.Cmp(wantCoefficient) != 0 || gotExp != want.exponent || conditions != want.conditions {
		t.Fatalf("%s: got %s·10^%d %v, want %s·10^%d %v", label, gotBig, gotExp, conditions, wantCoefficient, want.exponent, want.conditions)
	}
	if got.negative() && got.isZero() {
		t.Fatalf("%s: negative zero", label)
	}
}

// divOracleParts returns the signed coefficient and exponent from canonical
// text, independently of internal storage.
func divOracleParts(t *testing.T, d Decimal) (*big.Int, int64) {
	t.Helper()
	r := divRat(t, d)
	e := int64(d.Exponent())
	scaled := new(big.Rat).Mul(r, pow10Rat(-e))
	if !scaled.IsInt() {
		t.Fatalf("%v is not an integer at its exponent", d)
	}
	return new(big.Int).Set(scaled.Num()), e
}

// divOracleDirection is the rounding direction of the oracle's rounded
// magnitude r·10^t, carrying the sign of the exact quotient q, relative to q.
func divOracleDirection(q *big.Rat, r *big.Int, t int64) Conditions {
	rounded := new(big.Rat).Mul(new(big.Rat).SetInt(r), pow10Rat(t))
	if q.Sign() < 0 {
		rounded.Neg(rounded)
	}
	return oracleDirection(rounded, q)
}

// oracleToExponent is the DivToExponent contract: one rounding at t.
func oracleToExponent(q *big.Rat, ideal, t int64, mode RoundingMode) divExpect {
	v := new(big.Rat).Abs(q)
	v.Mul(v, pow10Rat(-t))
	r, inexact := oracleRound(v, mode, q.Sign() < 0)
	if mode == Exact && inexact {
		return divExpect{refused: true}
	}
	var c Conditions
	if inexact {
		c = Inexact | Rounded | divOracleDirection(q, r, t)
	} else if t > ideal {
		c = Rounded
	}
	return divExpect{coefficient: r, exponent: t, conditions: c}
}

// oracleContext is DivWithContext for an unguarded finite precision p.
func oracleContext(q *big.Rat, ideal int64, p int64, mode RoundingMode) divExpect {
	v := new(big.Rat).Abs(q)
	// adjusted = floor(log10 v)
	a := int64(len(new(big.Int).Quo(v.Num(), v.Denom()).String())) - 1
	if v.Cmp(big.NewRat(1, 1)) < 0 {
		a = -1
		for new(big.Rat).Mul(v, pow10Rat(-a)).Cmp(big.NewRat(1, 1)) < 0 {
			a--
		}
	}
	t := a - p + 1
	scaled := new(big.Rat).Mul(v, pow10Rat(-t))
	r, inexact := oracleRound(scaled, mode, q.Sign() < 0)
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
	if !inexact && t < ideal {
		for t < ideal && r.Sign() != 0 && new(big.Int).Mod(r, big.NewInt(10)).Sign() == 0 {
			r.Quo(r, big.NewInt(10))
			t++
		}
	}
	if divDigitsOf(r) > p {
		r.Quo(r, big.NewInt(10))
		t++
	}
	if inexact {
		c |= divOracleDirection(q, r, t)
	}
	return divExpect{coefficient: r, exponent: t, conditions: c}
}

// oracleExact is bare Div: the terminating quotient at the largest exponent
// not above the ideal exponent, or refusal.
func oracleExact(q *big.Rat, ideal int64) (divExpect, bool) {
	den := new(big.Int).Set(q.Denom())
	for _, f := range []int64{2, 5} {
		for new(big.Int).Mod(den, big.NewInt(f)).Sign() == 0 {
			den.Quo(den, big.NewInt(f))
		}
	}
	if den.Cmp(big.NewInt(1)) != 0 {
		return divExpect{}, false
	}
	v := new(big.Rat).Abs(q)
	for e := ideal; ; e-- {
		scaled := new(big.Rat).Mul(v, pow10Rat(-e))
		if scaled.IsInt() {
			return divExpect{coefficient: new(big.Int).Set(scaled.Num()), exponent: e}, true
		}
	}
}

func randomDivOperand(rng *rand.Rand, maxDigits int) Decimal {
	var b strings.Builder
	if rng.IntN(2) == 0 {
		b.WriteByte('-')
	}
	digits := 1 + rng.IntN(maxDigits)
	for i := range digits {
		if i == 0 {
			b.WriteByte(byte('1' + rng.IntN(9)))
		} else {
			b.WriteByte(byte('0' + rng.IntN(10)))
		}
	}
	// Terminating divisors appear often: powers of 2 and 5 times small odds.
	fmt.Fprintf(&b, "E%d", rng.IntN(41)-20)
	return MustParse(b.String())
}

func randomDivisor(rng *rand.Rand, maxDigits int) Decimal {
	if rng.IntN(3) == 0 {
		v := int64(1)
		for range rng.IntN(12) {
			v *= []int64{2, 5}[rng.IntN(2)]
		}
		v *= []int64{1, 3, 7, 9, 11}[rng.IntN(5)]
		if rng.IntN(2) == 0 {
			v = -v
		}
		return New(v, int32(rng.IntN(21)-10))
	}
	return randomDivOperand(rng, maxDigits)
}

var allDivModes = []RoundingMode{TiesToEven, TiesAwayFromZero, TiesTowardZero, TowardZero, AwayFromZero, TowardPositiveInfinity, TowardNegativeInfinity, Exact}

// TestDivToExponentAgainstRationalOracle checks that instructed
// non-terminating division rounds once for explicit exponent targets: every
// mode against an independent math/big.Rat single rounding, with operands
// across the inline and slow bands, targets from -80 to +20 and the
// Rounded-iff-inexact-or-above-ideal rule.
func TestDivToExponentAgainstRationalOracle(t *testing.T) {
	rng := rand.New(rand.NewPCG(20260925, 43))
	for i := range 6000 {
		x, y := randomDivOperand(rng, 70), randomDivisor(rng, 45)
		if i%17 == 0 {
			x = zeroDecimal(int32(rng.IntN(11) - 5))
		}
		target := int64(rng.IntN(101) - 80)
		mode := allDivModes[rng.IntN(len(allDivModes))]
		q := new(big.Rat).Quo(divRat(t, x), divRat(t, y))
		ideal := int64(x.exponent()) - int64(y.exponent())
		want := oracleToExponent(q, ideal, target, mode)
		if x.isZero() {
			want = divExpect{coefficient: new(big.Int), exponent: target}
		}
		got, conditions, err := x.DivToExponent(y, int32(target), mode)
		checkDivOutcome(t, fmt.Sprintf("%v/%v t=%d %v", x, y, target, mode), got, conditions, err, want, q.Sign() < 0)
	}
}

// TestDivWithContextAgainstRationalOracle covers instructed division under a finite unguarded precision: one rounding at p digits,
// exact quotients stripped toward the ideal exponent.
func TestDivWithContextAgainstRationalOracle(t *testing.T) {
	rng := rand.New(rand.NewPCG(20260925, 44))
	for range 6000 {
		x, y := randomDivOperand(rng, 70), randomDivisor(rng, 45)
		p := uint32(1 + rng.IntN(60))
		mode := allDivModes[rng.IntN(len(allDivModes))]
		ctx, err := NewContext(p, mode, nil, 0)
		if err != nil {
			t.Fatal(err)
		}
		q := new(big.Rat).Quo(divRat(t, x), divRat(t, y))
		want := oracleContext(q, int64(x.exponent())-int64(y.exponent()), int64(p), mode)
		got, conditions, err := x.DivWithContext(y, ctx)
		checkDivOutcome(t, fmt.Sprintf("%v/%v p=%d %v", x, y, p, mode), got, conditions, err, want, q.Sign() < 0)
	}
}

// TestDivExactAgainstRationalOracle checks that a terminating quotient is
// exact and an uninstructed non-terminating division is refused: terminating
// quotients return the exact value at the exponent closest to the ideal;
// every other quotient returns the Inexact refusal with a remedy.
func TestDivExactAgainstRationalOracle(t *testing.T) {
	rng := rand.New(rand.NewPCG(20260925, 45))
	for range 6000 {
		x, y := randomDivOperand(rng, 60), randomDivisor(rng, 30)
		q := new(big.Rat).Quo(divRat(t, x), divRat(t, y))
		ideal := int64(x.exponent()) - int64(y.exponent())
		got, err := x.Div(y)
		want, terminates := oracleExact(q, ideal)
		label := fmt.Sprintf("%v/%v", x, y)
		if !terminates {
			var ce *Error
			if !errors.As(err, &ce) || ce.Code != 0 || !errors.Is(err, ErrInexact) || ce.Remedy == "" || !isZeroValue(got) {
				t.Fatalf("%s: got (%v, %v), want remedy refusal", label, got, err)
			}
			continue
		}
		checkDivOutcome(t, label, got, 0, err, want, q.Sign() < 0)
	}
}

// TestDivNamedVectors pins named vectors: 38-digit ties and the AVG shape, the Rounded table, signs, zero cohorts, zero divisors
// and the int32 exponent rows.
func TestDivNamedVectors(t *testing.T) {
	d := MustParse[string]
	for _, tc := range []struct {
		x, y   string
		target int32
		mode   RoundingMode
		want   string
		cond   Conditions
	}{
		{"1", "8", -2, TiesToEven, "0.12", Inexact | Rounded | Decreased},
		{"1", "8", -2, TiesAwayFromZero, "0.13", Inexact | Rounded | Increased},
		{"-1", "8", -2, TowardPositiveInfinity, "-0.12", Inexact | Rounded | Increased},
		{"-1", "8", -2, TowardNegativeInfinity, "-0.13", Inexact | Rounded | Decreased},
		{"3", "8", -2, TiesToEven, "0.38", Inexact | Rounded | Increased},
		{"100", "1", 1, TiesToEven, "1.0E+2", Rounded},
		{"1", "4", -5, TiesToEven, "0.25000", 0},
		{"-1", "3", 0, TowardZero, "0", Inexact | Rounded | Increased}, // unsigned zero, rounded up
		{"-1", "3", 0, TowardNegativeInfinity, "-1", Inexact | Rounded | Decreased},
		{"0E-3", "1E+2", 4, TiesToEven, "0E+4", 0},
		{"5", "1", 1, TiesToEven, "0E+1", Inexact | Rounded | Decreased},
		{"5", "1", 1, TiesAwayFromZero, "1E+1", Inexact | Rounded | Increased},
		{"15", "1", 1, TiesToEven, "2E+1", Inexact | Rounded | Increased},
		// k < 0 with D = Cy - 2·Hrem = 1: the low part decides (Cy=3, Hrem=1).
		{"1351", "3", 2, TiesToEven, "5E+2", Inexact | Rounded | Increased},
		{"1350", "3", 2, TiesToEven, "4E+2", Inexact | Rounded | Decreased},
		{"1349", "3", 2, TiesToEven, "4E+2", Inexact | Rounded | Decreased},
		{"1351", "3", 2, TiesTowardZero, "5E+2", Inexact | Rounded | Increased},
	} {
		got, cond, err := d(tc.x).DivToExponent(d(tc.y), tc.target, tc.mode)
		if err != nil || got.String() != tc.want || cond != tc.cond {
			t.Errorf("%s/%s t=%d %v: got (%s, %v, %v), want (%s, %v)", tc.x, tc.y, tc.target, tc.mode, got, cond, err, tc.want, tc.cond)
		}
	}
	for _, tc := range []struct {
		x, y string
		p    uint32
		want string
		cond Conditions
	}{
		{"100", "1", 1, "1E+2", Rounded},
		{"2.400", "2.0", 2, "1.2", Rounded},
		{"1", "4", 5, "0.25", 0},
		{"1.20", "1", 3, "1.20", 0},
		{"1", "3", 5, "0.33333", Inexact | Rounded | Decreased},
	} {
		ctx, _ := NewContext(tc.p, TiesToEven, nil, 0)
		got, cond, err := d(tc.x).DivWithContext(d(tc.y), ctx)
		if err != nil || got.String() != tc.want || cond != tc.cond {
			t.Errorf("%s/%s p=%d: got (%s, %v, %v), want (%s, %v)", tc.x, tc.y, tc.p, got, cond, err, tc.want, tc.cond)
		}
	}
	for _, tc := range []struct{ x, y, want string }{
		{"2.400", "2.0", "1.20"}, {"1", "4", "0.25"}, {"0E-3", "1E+2", "0.00000"},
		{"1E+2147483647", "5E-1", "2E+2147483647"}, {"-12", "-4", "3"}, {"12", "-4", "-3"},
	} {
		got, err := d(tc.x).Div(d(tc.y))
		if err != nil || got.String() != tc.want {
			t.Errorf("Div %s/%s: got (%s, %v), want %s", tc.x, tc.y, got, err, tc.want)
		}
	}
	// A zero dividend keeps its ideal exponent under guards: no clamp.
	guarded, _ := NewContext(2, TiesToEven, &ExponentGuards{Emin: 0, Emax: 0}, 0)
	if got, cond, err := d("0E-3").DivWithContext(d("1E+2"), guarded); err != nil || got.Exponent() != -5 || !got.IsZero() || cond != 0 {
		t.Errorf("guarded zero cohort: (%s, %v, %v)", got, cond, err)
	}
	// Zero divisors, including under a tiny work cap (domain wins).
	tiny := Budget{MaxWork: 1}
	if _, _, err := d("1").DivWithContext(Zero(), Context{}.WithBudget(tiny)); !errors.Is(err, ErrDivisionByZero) {
		t.Errorf("1/0: %v", err)
	}
	if _, err := Zero().Div(Zero()); !errors.Is(err, ErrDivisionUndefined) {
		t.Errorf("0/0: %v", err)
	}
	var oe *Error
	if _, _, err := d("1").DivToExponent(Zero(), 0, TiesToEven); !errors.As(err, &oe) || oe.Condition != DivisionByZero || oe.Op != "DivToExponent" {
		t.Errorf("DivToExponent 1/0: %v", err)
	}
	// Unknown mode wins over the zero divisor.
	var ctxErr *Error
	if _, _, err := d("1").DivToExponent(Zero(), 0, RoundingMode(99)); !errors.As(err, &ctxErr) {
		t.Errorf("invalid mode: %v", err)
	}
	// 1/3 under a work cap of 1 is a resource refusal (precharge first).
	if _, _, err := d("1").DivWithContext(d("3"), Context{}.WithBudget(tiny)); !errors.Is(err, ErrInsufficientStorage) {
		t.Errorf("1/3 cap 1: %v", err)
	}
	// Carry past the int32 exponent limit is a range error.
	p1, _ := NewContext(1, TiesToEven, nil, 0)
	if _, _, err := d("95E+2147483646").DivWithContext(d("1"), p1); !errors.Is(err, ErrExponentRange) {
		t.Errorf("post-carry range: %v", err)
	}
	// Guard overflow substitutes Bmax before any range check.
	big5, _ := NewContext(5, TiesToEven, &ExponentGuards{Emin: -10, Emax: math.MaxInt32}, 0)
	if got, cond, err := d("1E+2147483647").DivWithContext(d("1E-1"), big5); err != nil || got.String() != "9.9999E+2147483647" || cond != Overflow|Inexact|Rounded|Decreased {
		t.Errorf("Bmax substitution: (%s, %v, %v)", got, cond, err)
	}
}

// TestDivideLimbsAgainstBigInt pins the Algorithm D kernel (quotient and
// remainder) against math/big over random multi-limb operands.
func TestDivideLimbsAgainstBigInt(t *testing.T) {
	rng := rand.New(rand.NewPCG(7, 8))
	toBig := func(limbs []uint32) *big.Int {
		v := new(big.Int)
		for _, limb := range slices.Backward(limbs) {
			v.Mul(v, big.NewInt(int64(decimalLimbBase)))
			v.Add(v, big.NewInt(int64(limb)))
		}
		return v
	}
	// Witnesses for Algorithm D's add-back step (a qhat one too large after
	// the two-limb correction), found by counting its extra limb steps.
	for _, w := range [][2][]uint32{
		{{205147989, 0, 999999999, 500000001}, {44626981, 999999999, 500000001}},
		{{893001023, 999999999, 499999999, 499999999}, {556650913, 500000001, 500000000}},
		{{0, 221779563, 500000001, 1, 499999999}, {431336675, 500000001, 499999999}},
	} {
		un, vn := len(w[0]), len(w[1])
		u := append(append([]uint32(nil), w[0]...), make([]uint32, max(un, vn)+1-un)...)
		v := append([]uint32(nil), w[1]...)
		wantQ, wantR := new(big.Int).QuoRem(toBig(w[0]), toBig(w[1]), new(big.Int))
		var c divCount
		q, _ := divideLimbs(u, un, v, make([]uint32, un-vn+2), &c)
		if toBig(q).Cmp(wantQ) != 0 || toBig(u[:vn]).Cmp(wantR) != 0 {
			t.Fatalf("add-back witness %v / %v: q=%v r=%v, want %v %v", w[0], w[1], toBig(q), toBig(u[:vn]), wantQ, wantR)
		}
	}
	for range 20000 {
		un, vn := 1+rng.IntN(12), 1+rng.IntN(6)
		u := make([]uint32, max(un, vn)+1)
		v := make([]uint32, vn)
		for i := range un {
			u[i] = uint32(rng.Uint64N(decimalLimbBase))
		}
		for i := range vn {
			v[i] = uint32(rng.Uint64N(decimalLimbBase))
			if rng.IntN(4) == 0 {
				v[i] = uint32(decimalLimbBase - 1)
			}
		}
		if v[vn-1] == 0 {
			v[vn-1] = 1 + uint32(rng.IntN(5))
		}
		wantQ, wantR := new(big.Int).QuoRem(toBig(u[:un]), toBig(v), new(big.Int))
		original := append([]uint32(nil), v...)
		q, zero := divideLimbs(u, un, v, make([]uint32, max(un-vn+2, 2)), nil)
		if toBig(q).Cmp(wantQ) != 0 || toBig(u[:vn]).Cmp(wantR) != 0 || zero != (wantR.Sign() == 0) {
			t.Fatalf("u=%v v=%v: q=%v r=%v, want %v %v", u[:un], original, toBig(q), toBig(u[:vn]), wantQ, wantR)
		}
		for i := range v {
			if v[i] != original[i] {
				t.Fatalf("divisor not restored: %v vs %v", v, original)
			}
		}
	}
}

// oracleGuarded is DivWithContext under a guarded context, following the
// guarded outcomes of the context arithmetic (contextRun).
func oracleGuarded(q *big.Rat, ideal, p int64, emin, emax int64, mode RoundingMode) divExpect {
	v := new(big.Rat).Abs(q)
	a := int64(0)
	for new(big.Rat).Mul(v, pow10Rat(-a)).Cmp(big.NewRat(1, 1)) < 0 {
		a--
	}
	for new(big.Rat).Mul(v, pow10Rat(-(a+1))).Cmp(big.NewRat(1, 1)) >= 0 {
		a++
	}
	bmax := func() divExpect {
		nines := new(big.Int).Sub(new(big.Int).Exp(big.NewInt(10), big.NewInt(p), nil), big.NewInt(1))
		direction := divOracleDirection(q, nines, emax-p+1)
		return divExpect{coefficient: nines, exponent: emax - p + 1, conditions: Overflow | Inexact | Rounded | direction}
	}
	if a > emax {
		if mode == Exact {
			return divExpect{refused: true}
		}
		return bmax()
	}
	tiny := a < emin
	t := max(a-p+1, emin-(p-1))
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
	if !inexact && t < ideal {
		for t < ideal && r.Sign() != 0 && new(big.Int).Mod(r, big.NewInt(10)).Sign() == 0 {
			r.Quo(r, big.NewInt(10))
			t++
		}
	}
	if divDigitsOf(r) > p {
		r.Quo(r, big.NewInt(10))
		t++
	}
	if r.Sign() != 0 && t+divDigitsOf(r)-1 > emax {
		return bmax()
	}
	if inexact {
		c |= divOracleDirection(q, r, t)
	}
	if tiny {
		c |= Subnormal
		if inexact {
			c |= Underflow
		}
	}
	return divExpect{coefficient: r, exponent: t, conditions: c}
}

// TestDivGuardedContextAgainstRationalOracle covers guarded Div: overflow
// substitution, the Etiny quantum with Subnormal and
// Underflow, and exact quotients outside the lattice rounding ordinarily.
func TestDivGuardedContextAgainstRationalOracle(t *testing.T) {
	rng := rand.New(rand.NewPCG(20260925, 46))
	for range 6000 {
		x, y := randomDivOperand(rng, 40), randomDivisor(rng, 30)
		p := int64(1 + rng.IntN(20))
		emin := int64(rng.IntN(41) - 30)
		emax := emin + int64(rng.IntN(40))
		mode := allDivModes[rng.IntN(len(allDivModes))]
		ctx, err := NewContext(uint32(p), mode, &ExponentGuards{Emin: int32(emin), Emax: int32(emax)}, 0)
		if err != nil {
			t.Fatal(err)
		}
		q := new(big.Rat).Quo(divRat(t, x), divRat(t, y))
		want := oracleGuarded(q, int64(x.exponent())-int64(y.exponent()), p, emin, emax, mode)
		got, conditions, err := x.DivWithContext(y, ctx)
		checkDivOutcome(t, fmt.Sprintf("%v/%v p=%d [%d,%d] %v", x, y, p, emin, emax, mode), got, conditions, err, want, q.Sign() < 0)
	}
}

// TestDivTrapsRetainFiniteResult covers the Div trap flow: a trapped
// condition returns the finite result with the untrapped conditions, and
// an Exact refusal is Inexact regardless of the trap selection.
func TestDivTrapsRetainFiniteResult(t *testing.T) {
	ctx, _ := NewContext(5, TiesToEven, nil, Inexact)
	got, cond, err := One().DivWithContext(MustParse("3"), ctx)
	var ce *Error
	if !errors.As(err, &ce) || ce.Code != 0 || ce.Condition != Inexact || got.String() != "0.33333" || cond != Rounded|Decreased {
		t.Fatalf("Inexact trap: (%s, %v, %v)", got, cond, err)
	}
	exact, _ := NewContext(5, Exact, nil, 0)
	got, cond, err = One().DivWithContext(MustParse("3"), exact)
	if !errors.As(err, &ce) || ce.Code != 0 || ce.Condition != Inexact || !isZeroValue(got) || cond != 0 {
		t.Fatalf("Exact refusal: (%v, %v, %v)", got, cond, err)
	}
	got, cond, err = MustParse("100").DivWithContext(One(), mustContext(t, 1, Exact))
	if err != nil || got.String() != "1E+2" || cond != Rounded {
		t.Fatalf("Exact zero-only discard: (%s, %v, %v)", got, cond, err)
	}
}

func mustContext(t *testing.T, p uint32, mode RoundingMode) Context {
	t.Helper()
	ctx, err := NewContext(p, mode, nil, 0)
	if err != nil {
		t.Fatal(err)
	}
	return ctx
}

// TestDivTariffBoundsCountedWork checks the tariff against counted loops:
// over a size sweep and hand-picked witnesses, the kernel's counted limb operations and digit
// reads never exceed the precharge B.
func TestDivTariffBoundsCountedWork(t *testing.T) {
	type witness struct {
		x, y Decimal
		t    int64
	}
	var cases []witness
	rng := rand.New(rand.NewPCG(20260925, 47))
	for range 3000 {
		x, y := randomDivOperand(rng, 200), randomDivisor(rng, 120)
		cases = append(cases, witness{x, y, int64(rng.IntN(301) - 200)})
	}
	one := strings.Repeat("0", 999)
	cases = append(cases,
		witness{MustParse("1" + one[:999]), MustParse("7"), -34},       // 1000-digit / 1-digit
		witness{MustParse("1" + one[:998] + "1"), MustParse("1"), 965}, // low-part scan (10^999+1)/1
		witness{MustParse("5"), MustParse("1"), 1},                     // H = 0 path
		witness{MustParse(strings.Repeat("9", 9000)), MustParse(strings.Repeat("9", 72)), 0},
	)
	for _, w := range cases {
		s := newDivSource(w.x, w.y)
		p := s.plan(w.t)
		if !p.ok {
			continue
		}
		var stack [divStackLimbs]uint32
		num, den, quot, ok := divScratchBuffers(&stack, &s, p, 1)
		if !ok {
			continue
		}
		var c divCount
		r, _ := s.divDigits(p, num, den, quot, &c)
		if c.units > p.charge {
			t.Fatalf("%v/%v t=%d path=%d: counted %d > B %d", w.x, w.y, w.t, p.path, c.units, p.charge)
		}
		_ = r
	}
}

// TestDivBudgetBoundaries covers the Div budget twins: the precharge B and
// the final digit count N admit at equality and refuse one below.
func TestDivBudgetBoundaries(t *testing.T) {
	x, y := MustParse("123456789012345678901234567890"), MustParse("7")
	s := newDivSource(x, y)
	p := s.plan(-10)
	full, _, err := x.DivToExponent(y, -10, TiesToEven)
	if err != nil {
		t.Fatal(err)
	}
	n := full.CoefficientDigits()
	w := p.charge + 2*n + 1
	for _, tc := range []struct {
		budget Budget
		ok     bool
	}{
		{Budget{MaxWork: p.charge - 1}, false},
		{Budget{MaxWork: w - 1}, false},
		{Budget{MaxWork: w}, true},
		{Budget{MaxDigits: n - 1}, false},
		{Budget{MaxDigits: n}, true},
	} {
		got, _, err := x.DivToExponentWithBudget(y, -10, TiesToEven, tc.budget)
		if tc.ok != (err == nil) || tc.ok && !got.Equal(full) {
			t.Errorf("%+v: (%v, %v)", tc.budget, got, err)
		}
		if !tc.ok && !errors.Is(err, ErrInsufficientStorage) {
			t.Errorf("%+v: want InsufficientStorage, got %v", tc.budget, err)
		}
	}
}

var divSink Decimal

// TestDivStackCasesDoNotAllocate covers the zero-allocation cases: a
// 38-digit dividend shifted by 10^76 over a 38-digit
// divisor, the AVG shape over an int64 count, and bare Div of two 38-digit
// operands, each with a quotient of at most 38 digits.
func TestDivStackCasesDoNotAllocate(t *testing.T) {
	x38 := MustParse("-12345678901234567890123456789012345678E-38")
	y38 := MustParse("98765432109876543210987654321098765432E-38")
	sum := MustParse("99999999999999999999999999999999999999E-6")
	count := FromInt64(1234567)
	exact := MustParse("99999999999999999999999999999999999998")
	half := MustParse("49999999999999999999999999999999999999")
	for name, f := range map[string]func(){
		"sql-divide": func() { divSink, _, _ = x38.DivToExponent(y38, -38, TiesToEven) },
		"avg":        func() { divSink, _, _ = sum.DivToExponent(count, -6, TiesToEven) },
		"bare-exact": func() { divSink, _ = exact.Div(half) },
	} {
		if allocs := testing.AllocsPerRun(50, f); allocs != 0 {
			t.Errorf("%s: %g allocations", name, allocs)
		}
	}
}

// TestDivExactAtIdealExponent checks that a terminating quotient is exact,
// that dividing by one is exact, and that exact division collapses to the
// ideal exponent: 1/4 is 0.25, 2.75/1 is 2.75 and
// 2.400/2.0 is 1.20, through Div, an unlimited context and a finite
// precision wide enough to hold them, never padded or stripped past the
// ideal exponent.
func TestDivExactAtIdealExponent(t *testing.T) {
	wide := mustContext(t, 10, TiesToEven)
	for _, tc := range []struct {
		x, y, want string
		exponent   int32
	}{
		{"1", "4", "0.25", -2},
		{"2.75", "1", "2.75", -2},
		{"2.400", "2.0", "1.20", -2},
	} {
		x, y := MustParse(tc.x), MustParse(tc.y)
		bare, err := x.Div(y)
		if err != nil || bare.String() != tc.want || bare.Exponent() != tc.exponent {
			t.Fatalf("Div %s/%s: (%s, %v)", tc.x, tc.y, bare, err)
		}
		for _, ctx := range []Context{{}, wide} {
			got, cond, err := x.DivWithContext(y, ctx)
			if err != nil || got.String() != tc.want || got.Exponent() != tc.exponent || cond != 0 {
				t.Fatalf("DivWithContext %s/%s p=%d: (%s, %v, %v)", tc.x, tc.y, ctx.Precision(), got, cond, err)
			}
		}
	}
}

// TestDivZeroDivisorIdentities covers division by zero and zero over zero,
// which error distinctly: every Div form returns
// no value, zero conditions and a distinct typed identity.
func TestDivZeroDivisorIdentities(t *testing.T) {
	ctx := mustContext(t, 5, TiesToEven)
	for _, dividend := range []Decimal{MustParse("-7.5"), Zero(), MustParse("0E-9")} {
		code, condition := ErrDivisionByZero, DivisionByZero
		if dividend.IsZero() {
			code, condition = ErrDivisionUndefined, DivisionUndefined
		}
		for _, divisor := range []Decimal{Zero(), MustParse("0E+5"), MustParse("0.000")} {
			type call struct {
				op string
				fn func() (Decimal, Conditions, error)
			}
			for _, c := range []call{
				{"Div", func() (Decimal, Conditions, error) { d, err := dividend.Div(divisor); return d, 0, err }},
				{"DivWithContext", func() (Decimal, Conditions, error) {
					d, _, err := dividend.DivWithContext(divisor, Context{}.WithBudget(Budget{MaxWork: 1}))
					return d, 0, err
				}},
				{"DivWithContext", func() (Decimal, Conditions, error) { return dividend.DivWithContext(divisor, ctx) }},
				{"DivToExponent", func() (Decimal, Conditions, error) { return dividend.DivToExponent(divisor, -2, TiesToEven) }},
			} {
				got, cond, err := c.fn()
				var oe *Error
				if !errors.Is(err, code) || !errors.As(err, &oe) || oe.Op != c.op || oe.Condition != condition || !isZeroValue(got) || cond != 0 {
					t.Fatalf("%s(%v, %v): (%v, %v, %v), want %v", c.op, dividend, divisor, got, cond, err, code)
				}
				if errors.Is(err, ErrDivisionByZero) == errors.Is(err, ErrDivisionUndefined) {
					t.Fatalf("%s: identities not distinct: %v", c.op, err)
				}
			}
		}
	}
}

// TestDivNonTerminatingRequiresInstruction checks that uninstructed
// non-terminating division errors: 1/3 without a rounding target returns no value and the
// rounding-refused (Inexact) class whose remedy names DivWithContext and
// DivToExponent.
func TestDivNonTerminatingRequiresInstruction(t *testing.T) {
	check := func(op string, got Decimal, cond Conditions, err error) {
		t.Helper()
		var ce *Error
		if !errors.As(err, &ce) || ce.Code != 0 || ce.Op != op || ce.Condition != Inexact || !errors.Is(err, ErrInexact) || !isZeroValue(got) || cond != 0 {
			t.Fatalf("%s: (%v, %v, %v)", op, got, cond, err)
		}
		if !strings.Contains(err.Error(), "DivWithContext") || !strings.Contains(err.Error(), "DivToExponent") {
			t.Fatalf("%s: remedy missing from %q", op, err)
		}
	}
	got, err := One().Div(MustParse("3"))
	check("Div", got, 0, err)
	got, cond, err := One().DivWithContext(MustParse("3"), Context{})
	check("DivWithContext", got, cond, err)
}

// TestDivInstructedRoundsOnce checks that instructed non-terminating
// division rounds once: 1/3 under a working precision and mode is
// correctly rounded once with Inexact and Rounded, and a direct exponent
// target rounds the exact rational once (1251/1000 to one place is 1.3,
// where rounding to three digits first would give 1.2).
func TestDivInstructedRoundsOnce(t *testing.T) {
	for _, tc := range []struct {
		mode      RoundingMode
		want      string
		direction Conditions // sign of result − 1/3.
	}{{TiesToEven, "0.33333", Decreased}, {TowardPositiveInfinity, "0.33334", Increased}, {TowardZero, "0.33333", Decreased}} {
		got, cond, err := One().DivWithContext(MustParse("3"), mustContext(t, 5, tc.mode))
		if err != nil || got.String() != tc.want || cond != Inexact|Rounded|tc.direction {
			t.Fatalf("1/3 p=5 %v: (%s, %v, %v)", tc.mode, got, cond, err)
		}
	}
	got, cond, err := MustParse("1251").DivToExponent(MustParse("1000"), -1, TiesToEven)
	if err != nil || got.String() != "1.3" || cond != Inexact|Rounded|Increased {
		t.Fatalf("single rounding: (%s, %v, %v)", got, cond, err)
	}
	twice, _, _ := MustParse("1251").DivWithContext(MustParse("1000"), mustContext(t, 3, TiesToEven))
	if rounded, _, _ := twice.Quantize(-1, TiesToEven); rounded.String() != "1.2" {
		t.Fatalf("double-rounding witness changed: %s", rounded)
	}
}

// divChargedExponent is the exponent at which the tariff plans
// each Div method: ideal−K for bare Div and unlimited contexts, the target
// for DivToExponent, and max((dx−dy)+ideal−p, Etiny) for finite contexts.
func divChargedExponent(s *divSource, ctx *Context, target *int64) int64 {
	if target != nil {
		return *target
	}
	if ctx == nil || ctx.precision == 0 {
		k := (s.dy*3322 + 999) / 1000
		return s.ideal - int64(k)
	}
	p := int64(ctx.precision)
	t := int64(s.dx) - int64(s.dy) + s.ideal - p
	if ctx.guarded {
		t = max(t, int64(ctx.guards.Emin)-(p-1))
	}
	return t
}

// TestDivBudgetBoundariesEveryPath covers the Div tariff through all
// three budget twins and every kernel path (tiny shortcut, no high part,
// long division with k >= 0 and k < 0, quotient zero): the precharge B and
// the complete charge W = B + 2N + 1 admit at equality and refuse one
// below, as does the final digit quota N.
func TestDivBudgetBoundariesEveryPath(t *testing.T) {
	rng := rand.New(rand.NewPCG(20260925, 48))
	paths := map[string]int{}
	type call func(Budget) (Decimal, error)
	for range 3000 {
		x, y := randomDivOperand(rng, 50), randomDivisor(rng, 40)
		if rng.IntN(5) == 0 {
			x = MustParse("7")
			y = randomDivisor(rng, 40)
		}
		s := newDivSource(x, y)
		var (
			f       call
			name    string
			charged int64
		)
		switch rng.IntN(3) {
		case 0:
			name = "DivWithContext exact"
			f = func(b Budget) (Decimal, error) {
				res, _, resErr := x.DivWithContext(y, Context{}.WithBudget(b))
				return res, resErr
			}
			charged = divChargedExponent(&s, nil, nil)
		case 1:
			target := s.ideal + int64(rng.IntN(121)-60)
			if target < math.MinInt32 || target > math.MaxInt32 {
				continue
			}
			name = "DivToExponentWithBudget"
			f = func(b Budget) (Decimal, error) {
				d, _, err := x.DivToExponentWithBudget(y, int32(target), TiesToEven, b)
				return d, err
			}
			charged = divChargedExponent(&s, nil, &target)
		default:
			p := uint32(1 + rng.IntN(40))
			var guards *ExponentGuards
			if rng.IntN(2) == 0 {
				emin := int32(rng.IntN(41) - 30)
				guards = &ExponentGuards{Emin: emin, Emax: emin + int32(rng.IntN(40))}
			}
			ctx, err := NewContext(p, TiesToEven, guards, 0)
			if err != nil {
				t.Fatal(err)
			}
			name = "DivWithContext"
			f = func(b Budget) (Decimal, error) {
				d, _, err := x.DivWithContext(y, ctx.WithBudget(b))
				return d, err
			}
			charged = divChargedExponent(&s, &ctx, nil)
		}
		full, err := f(Budget{})
		if err != nil {
			continue // non-terminating bare quotient or range refusal
		}
		plan := s.plan(charged)
		if !plan.ok {
			t.Fatalf("%s %v/%v: plan overflow", name, x, y)
		}
		paths[fmt.Sprintf("%s/%d/k>=0=%t", name, plan.path, plan.k >= 0)]++
		n := full.CoefficientDigits()
		if full.IsZero() {
			n = 1
		}
		w := plan.charge + 2*n + 1
		for _, tc := range []struct {
			budget Budget
			ok     bool
		}{
			{Budget{MaxWork: plan.charge - 1}, false},
			{Budget{MaxWork: w - 1}, false},
			{Budget{MaxWork: w}, true},
			{Budget{MaxDigits: n - 1}, n == 1},
			{Budget{MaxDigits: n}, true},
		} {
			if tc.budget.MaxWork == 0 && tc.budget.MaxDigits == 0 {
				continue // a zero field is no quota
			}
			got, err := f(tc.budget)
			if tc.ok != (err == nil) || tc.ok && (!got.Equal(full) || got.Exponent() != full.Exponent()) {
				t.Fatalf("%s %v/%v %+v (B=%d N=%d path=%d): (%v, %v)", name, x, y, tc.budget, plan.charge, n, plan.path, got, err)
			}
			if !tc.ok && !errors.Is(err, ErrInsufficientStorage) {
				t.Fatalf("%s %v/%v %+v: %v", name, x, y, tc.budget, err)
			}
		}
	}
	for _, want := range []string{
		"DivWithContext exact/2/k>=0=true",
		"DivToExponentWithBudget/0/k>=0=false", "DivToExponentWithBudget/0/k>=0=true",
		"DivToExponentWithBudget/2/k>=0=false", "DivToExponentWithBudget/2/k>=0=true",
		"DivWithContext/2/k>=0=false", "DivWithContext/2/k>=0=true",
	} {
		if paths[want] == 0 {
			t.Errorf("path %s never exercised: %v", want, paths)
		}
	}
	// The no-high-part path (dy=1, dx+k=0) through the direct twin.
	five, one := MustParse("5"), One()
	s := newDivSource(five, one)
	if plan := s.plan(1); plan.path != divHZero {
		t.Fatalf("H=0 witness took path %d", plan.path)
	}
	if _, _, err := five.DivToExponentWithBudget(one, 1, TiesToEven, Budget{MaxWork: 5}); !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("H=0 below W: %v", err)
	}
	if got, _, err := five.DivToExponentWithBudget(one, 1, TiesToEven, Budget{MaxWork: 6}); err != nil || !got.IsZero() {
		t.Fatalf("H=0 at W: (%v, %v)", got, err)
	}
}

// TestDivToExponentRefusesHugeGapBeforeAllocating covers the digit
// quota for an explicit target: a quotient that must exceed the cap is
// refused before its gap-sized scratch is allocated.
func TestDivToExponentRefusesHugeGapBeforeAllocating(t *testing.T) {
	x, y := MustParse("1"), MustParse("3")
	allocs := testing.AllocsPerRun(5, func() {
		_, _, err := x.DivToExponentWithBudget(y, -200000000, TiesToEven, Budget{MaxDigits: 38})
		if !errors.Is(err, ErrInsufficientStorage) {
			t.Fatalf("huge gap under a digit cap: %v", err)
		}
	})
	if allocs > 1 {
		t.Fatalf("refusal allocated %g objects (want only the error)", allocs)
	}
}

// TestDivTariffMatchesWitnesses pins the tariff's charges on fixed
// witnesses with independently computed numbers: the
// tiny shortcut applies to k < 0 with 0 < dx+k <= dy−2 (B = min(t(dx),t(dy))+1
// = 3, N = 1, W = 6), and a guarded context plans at Etiny (1E−100/3 at p=5,
// Emin=−10: tiny, B = 2, N = 1, W = 5).
func TestDivTariffMatchesWitnesses(t *testing.T) {
	x, y := MustParse("1234567890"), MustParse("10000000000000000000")
	if _, _, err := x.DivToExponentWithBudget(y, 5, TiesToEven, Budget{MaxWork: 5}); !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("tiny k<0 below W: %v", err)
	}
	if got, _, err := x.DivToExponentWithBudget(y, 5, TiesToEven, Budget{MaxWork: 6}); err != nil || !got.IsZero() {
		t.Fatalf("tiny k<0 at W=6: (%v, %v)", got, err)
	}
	ctx, _ := NewContext(5, TiesToEven, &ExponentGuards{Emin: -10, Emax: 10}, 0)
	tiny := MustParse("1E-100")
	if _, _, err := tiny.DivWithContext(MustParse("3"), ctx.WithBudget(Budget{MaxWork: 4})); !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("guarded tiny below W: %v", err)
	}
	got, cond, err := tiny.DivWithContext(MustParse("3"), ctx.WithBudget(Budget{MaxWork: 5}))
	if err != nil || !got.IsZero() || got.Exponent() != -14 || cond != Inexact|Rounded|Subnormal|Underflow|Decreased {
		t.Fatalf("guarded tiny at W=5: (%v, %v, %v)", got, cond, err)
	}
}

// TestDivDigitQuotaPrecedesExactRefusal pins refusal precedence: for an
// explicit target, a positive digit quota below the quotient's known
// minimum length refuses before the Exact refusal.
func TestDivDigitQuotaPrecedesExactRefusal(t *testing.T) {
	_, _, err := One().DivToExponentWithBudget(MustParse("3"), -50, Exact, Budget{MaxDigits: 49})
	if !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("quota 49: %v, want ErrInsufficientStorage", err)
	}
	_, _, err = One().DivToExponentWithBudget(MustParse("3"), -50, Exact, Budget{MaxDigits: 50})
	var ce *Error
	if !errors.As(err, &ce) || ce.Code != 0 || ce.Condition != Inexact {
		t.Fatalf("quota 50: %v, want the Exact refusal", err)
	}
}

// TestDivDirectionAgainstRationalOracle covers the rounding direction for
// DivToExponent and DivWithContext, guarded and unguarded:
// in every mode the direction bit equals sign(result − x/y) by
// math/big.Rat comparison, accompanies Inexact exactly, and respects the
// directed-mode side unless Overflow is reported. Named rows pin −1/3 at
// t=0 under TowardZero (the unsigned zero, Increased), the Etiny quantum,
// zero-only discards (Rounded, no direction), Exact refusals and resource
// refusals (no value, no direction).
func TestDivDirectionAgainstRationalOracle(t *testing.T) {
	rng := rand.New(rand.NewPCG(0xdec045, 5))
	counts := map[Conditions]int{}
	for i := range 12_000 {
		x, y := randomDivOperand(rng, 30), randomDivisor(rng, 20)
		mode := allDivModes[rng.IntN(len(allDivModes))]
		exact := new(big.Rat).Quo(divRat(t, x), divRat(t, y))
		var got Decimal
		var conditions Conditions
		var err error
		var label string
		switch i % 3 {
		case 0:
			target := int32(rng.IntN(81) - 60)
			label = fmt.Sprintf("%v/%v t=%d %v", x, y, target, mode)
			got, conditions, err = x.DivToExponent(y, target, mode)
		case 1:
			p := uint32(1 + rng.IntN(30))
			label = fmt.Sprintf("%v/%v p=%d %v", x, y, p, mode)
			got, conditions, err = x.DivWithContext(y, mustContext(t, p, mode))
		default:
			p := int32(1 + rng.IntN(20))
			emin := int32(rng.IntN(41) - 30)
			guards := &ExponentGuards{Emin: emin, Emax: emin + int32(rng.IntN(40))}
			ctx, ctxErr := NewContext(uint32(p), mode, guards, 0)
			if ctxErr != nil {
				t.Fatal(ctxErr)
			}
			label = fmt.Sprintf("%v/%v p=%d %+v %v", x, y, p, *guards, mode)
			got, conditions, err = x.DivWithContext(y, ctx)
		}
		if checkRoundingDirection(t, label, exact, mode, got, conditions, err) {
			counts[conditions&(Increased|Decreased|Overflow|Subnormal)]++
		} else if mode != Exact {
			t.Fatalf("%s: unexpected refusal %v", label, err)
		}
	}
	for _, want := range []Conditions{Increased, Decreased, Increased | Subnormal, Decreased | Subnormal, Increased | Overflow, Decreased | Overflow} {
		if counts[want] < 20 {
			t.Fatalf("Div direction corpus reached %v only %d times: %v", want, counts[want], counts)
		}
	}

	guarded, _ := NewContext(5, TiesToEven, &ExponentGuards{Emin: -10, Emax: 10}, 0) // Etiny -14
	towardZero, _ := NewContext(5, TowardZero, &ExponentGuards{Emin: -10, Emax: 10}, 0)
	for _, tc := range []struct {
		name, x, y string
		call       func(x, y Decimal) (Decimal, Conditions, error)
		want       string
		conditions Conditions
	}{
		{"-1/3 t=0 TowardZero", "-1", "3", func(x, y Decimal) (Decimal, Conditions, error) { return x.DivToExponent(y, 0, TowardZero) }, "0", Inexact | Rounded | Increased},
		{"-2/3 t=0 TowardPositiveInfinity", "-2", "3", func(x, y Decimal) (Decimal, Conditions, error) { return x.DivToExponent(y, 0, TowardPositiveInfinity) }, "0", Inexact | Rounded | Increased},
		{"1/3 t=0 TowardNegativeInfinity", "1", "3", func(x, y Decimal) (Decimal, Conditions, error) { return x.DivToExponent(y, 0, TowardNegativeInfinity) }, "0", Inexact | Rounded | Decreased},
		{"-1/3 t=0 AwayFromZero", "-1", "3", func(x, y Decimal) (Decimal, Conditions, error) { return x.DivToExponent(y, 0, AwayFromZero) }, "-1", Inexact | Rounded | Decreased},
		{"Etiny negative to zero", "-1E-100", "3", func(x, y Decimal) (Decimal, Conditions, error) { return x.DivWithContext(y, towardZero) }, "0E-14", Subnormal | Underflow | Inexact | Rounded | Increased},
		{"Etiny subnormal", "1E-12", "3", func(x, y Decimal) (Decimal, Conditions, error) { return x.DivWithContext(y, guarded) }, "3.3E-13", Subnormal | Underflow | Inexact | Rounded | Decreased},
		{"Etiny negative subnormal", "-2E-12", "3", func(x, y Decimal) (Decimal, Conditions, error) { return x.DivWithContext(y, guarded) }, "-6.7E-13", Subnormal | Underflow | Inexact | Rounded | Decreased},
		{"zero-only discard context", "100", "1", func(x, y Decimal) (Decimal, Conditions, error) {
			return x.DivWithContext(y, mustContext(t, 1, TowardPositiveInfinity))
		}, "1E+2", Rounded},
		{"zero-only discard target", "-100", "1", func(x, y Decimal) (Decimal, Conditions, error) { return x.DivToExponent(y, 1, TowardNegativeInfinity) }, "-1.0E+2", Rounded},
	} {
		t.Run(tc.name, func(t *testing.T) {
			x, y := MustParse(tc.x), MustParse(tc.y)
			got, conditions, err := tc.call(x, y)
			if err != nil || got.String() != tc.want || conditions != tc.conditions {
				t.Fatalf("%s: (%s, %v, %v), want (%s, %v)", tc.name, got, conditions, err, tc.want, tc.conditions)
			}
			checkRoundingDirection(t, tc.name, new(big.Rat).Quo(divRat(t, x), divRat(t, y)), TiesToEven, got, conditions, err)
		})
	}
	for _, tc := range []struct {
		name string
		code ErrorCode
		call func() (Decimal, Conditions, error)
	}{
		{"Exact DivToExponent", ErrInexact, func() (Decimal, Conditions, error) { return MustParse("-1").DivToExponent(MustParse("3"), 0, Exact) }},
		{"Exact DivWithContext", ErrInexact, func() (Decimal, Conditions, error) {
			return One().DivWithContext(MustParse("3"), mustContext(t, 5, Exact))
		}},
		{"resource DivToExponent", ErrInsufficientStorage, func() (Decimal, Conditions, error) {
			return One().DivToExponentWithBudget(MustParse("3"), -5, TowardPositiveInfinity, Budget{MaxWork: 1})
		}},
		{"resource DivWithContext", ErrInsufficientStorage, func() (Decimal, Conditions, error) {
			return MustParse("-1").DivWithContext(MustParse("3"), mustContext(t, 5, TowardZero).WithBudget(Budget{MaxDigits: 4}))
		}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got, conditions, err := tc.call()
			if !isZeroValue(got) || conditions != 0 || !errors.Is(err, tc.code) {
				t.Fatalf("%s: (%v, %v, %v); want no value, no conditions, %v", tc.name, got, conditions, err, tc.code)
			}
		})
	}
}

// TestDivDirectedEnclosure covers the directed enclosure and tightness
// property for DivToExponent and DivWithContext: TowardNegativeInfinity and
// TowardPositiveInfinity return the floor and ceiling of x/y on the grid the
// rounding used (the target exponent, or the p-digit grid of the quotient's
// decade, never below Etiny under guards), so they bracket the exact
// quotient and no representable value lies strictly between, including a
// carry into a new decade (19.99/2 = 9.995 to 10.0 at p=3).
func TestDivDirectedEnclosure(t *testing.T) {
	rng := rand.New(rand.NewPCG(0xdec045, 6))
	checked, inexact := 0, 0
	type sample struct {
		x, y   Decimal
		target int32 // DivToExponent when p == 0
		p      int64
		guards *ExponentGuards
	}
	samples := []sample{
		{MustParse("19.99"), MustParse("2"), 0, 3, nil},
		{MustParse("-19.99"), MustParse("2"), 0, 3, nil},
		{MustParse("19.99"), MustParse("2"), -2, 0, nil},
		{MustParse("0.0999"), MustParse("10"), 0, 3, &ExponentGuards{Emin: -2, Emax: 5}},
		{MustParse("-1E-100"), MustParse("3"), 0, 5, &ExponentGuards{Emin: -10, Emax: 10}},
		{MustParse("-1"), MustParse("3"), 0, 0, nil},
	}
	for range 8_000 {
		s := sample{x: randomDivOperand(rng, 30), y: randomDivisor(rng, 20)}
		switch rng.IntN(3) {
		case 0:
			s.target = int32(rng.IntN(81) - 60)
		case 1:
			s.p = int64(1 + rng.IntN(30))
		default:
			s.p = int64(1 + rng.IntN(20))
			emin := int32(rng.IntN(41) - 30)
			s.guards = &ExponentGuards{Emin: emin, Emax: emin + int32(rng.IntN(40))}
		}
		samples = append(samples, s)
	}
	for i, s := range samples {
		exact := new(big.Rat).Quo(divRat(t, s.x), divRat(t, s.y))
		var lo, hi Decimal
		var loConditions, hiConditions Conditions
		var loErr, hiErr error
		quantum := int64(s.target)
		if s.p == 0 {
			lo, loConditions, loErr = s.x.DivToExponent(s.y, s.target, TowardNegativeInfinity)
			hi, hiConditions, hiErr = s.x.DivToExponent(s.y, s.target, TowardPositiveInfinity)
		} else {
			loCtx, err := NewContext(uint32(s.p), TowardNegativeInfinity, s.guards, 0)
			if err != nil {
				t.Fatal(err)
			}
			hiCtx, _ := NewContext(uint32(s.p), TowardPositiveInfinity, s.guards, 0)
			lo, loConditions, loErr = s.x.DivWithContext(s.y, loCtx)
			hi, hiConditions, hiErr = s.x.DivWithContext(s.y, hiCtx)
			emin := int64(0)
			if s.guards != nil {
				emin = int64(s.guards.Emin)
			}
			quantum = directionPrecisionQuantum(exact, s.p, s.guards != nil, emin)
		}
		label := fmt.Sprintf("sample %d %v/%v t=%d p=%d", i, s.x, s.y, s.target, s.p)
		if loErr != nil || hiErr != nil {
			t.Fatalf("%s: errors %v / %v", label, loErr, hiErr)
		}
		if checkDirectedEnclosure(t, label, exact, quantum, lo, loConditions, hi, hiConditions) {
			checked++
			if loConditions&Inexact != 0 {
				inexact++
			}
		}
		if i < 2 && lo.String() != "-10.0" && hi.String() != "10.0" {
			t.Fatalf("%s: carry row did not reach the new decade: %v %v", label, lo, hi)
		}
	}
	if checked < 6_000 || inexact < 3_000 {
		t.Fatalf("enclosure checked %d pairs, %d inexact", checked, inexact)
	}
}

// TestDivWithContextOverflowDirectionVectors covers overflow directions for
// DivWithContext in every mode and sign at p=3,
// Emax=2 (Bmax 999): exact quotients past Bmax, an exact 1000, and 999.5,
// 999.9 and the non-terminating 2999.8/3 = 999.9333…, whose rounding
// carries past Bmax only when the magnitude rounds up. Every ±999 result
// reports Decreased for a positive and Increased for a negative quotient,
// with Overflow exactly on substitution; Exact refuses with no direction.
func TestDivWithContextOverflowDirectionVectors(t *testing.T) {
	guards := &ExponentGuards{Emin: -2, Emax: 2}
	for _, tc := range []struct {
		dividend, divisor string
		tie               bool // the discarded part is exactly one half
		past              bool // the exact quotient already exceeds Bmax's decade
	}{
		{"3000.3", "3", false, true},
		{"1", "0.001", false, true},
		{"2999.7", "3", false, false},
		{"2998.5", "3", true, false},
		{"2999.8", "3", false, false},
	} {
		for _, negative := range []bool{false, true} {
			x, y := MustParse(tc.dividend), MustParse(tc.divisor)
			if negative {
				x = x.Neg()
			}
			exact := new(big.Rat).Quo(divRat(t, x), divRat(t, y))
			for _, mode := range allDivModes {
				up := false
				switch mode {
				case TiesToEven, TiesAwayFromZero, AwayFromZero:
					up = true // 999 is odd, so TiesToEven rounds the tie up
				case TiesTowardZero:
					up = !tc.tie
				case TowardPositiveInfinity:
					up = !negative
				case TowardNegativeInfinity:
					up = negative
				}
				ctx, err := NewContext(3, mode, guards, 0)
				if err != nil {
					t.Fatal(err)
				}
				got, conditions, err := x.DivWithContext(y, ctx)
				label := fmt.Sprintf("%v/%v %v", x, y, mode)
				if mode == Exact {
					if !isZeroValue(got) || conditions != 0 || !errors.Is(err, ErrInexact) {
						t.Fatalf("%s: Exact overflow (%v, %v, %v)", label, got, conditions, err)
					}
					continue
				}
				want := Inexact | Rounded | Decreased
				if negative {
					want = Inexact | Rounded | Increased
				}
				if tc.past || up {
					want |= Overflow
				}
				if err != nil || got.CoefficientDigits() != 3 || got.String() != map[bool]string{false: "999", true: "-999"}[negative] || conditions != want {
					t.Fatalf("%s: (%v, %v, %v); want ±999 %v", label, got, conditions, err, want)
				}
				checkRoundingDirection(t, label, exact, mode, got, conditions, err)
			}
		}
	}
}

// TestFinishContextRefusesNegativeDrop pins the checked-drop
// invariant: an inexact R′ with fewer than p digits at t′ (t′ above the
// rounding exponent t) is refused, never rounded through a wrapped digit
// count, including next to the int64 limit. An exact short R′ (the
// exact-first rule) publishes at t′ unchanged.
func TestFinishContextRefusesNegativeDrop(t *testing.T) {
	ctx, err := NewContext(5, TiesToEven, nil, 0)
	if err != nil {
		t.Fatal(err)
	}
	for _, tPrime := range []int64{0, 100, math.MaxInt64 - 10} {
		r := make([]uint32, 1, 2)
		r[0] = 5
		got, conditions, err := finishContext(r, divBelow, tPrime, 0, 0, false, &ctx, 1, limits{}, "probe")
		if !errors.Is(err, ErrInsufficientStorage) {
			t.Fatalf("t′=%d: (%v, %v, %v), want the checked refusal", tPrime, got, conditions, err)
		}
	}
	r := make([]uint32, 1, 2)
	r[0] = 5
	got, conditions, err := finishContext(r, divExactClass, -3, 0, 0, false, &ctx, 1, limits{}, "probe")
	if err != nil || conditions != 0 || got.String() != "0.005" {
		t.Fatalf("exact short R′: (%v, %v, %v), want 0.005", got, conditions, err)
	}
}

// TestDivByZeroErrorsUnderEveryContextAndTrap checks that domain violations
// are never demoted: a zero divisor surfaces as an
// error under every context — the zero context, p=5 in all eight modes and
// a guarded p=3 context — with no traps, with only the division traps and
// with every trappable condition, through both context forms. Each call
// returns Decimal{}, zero conditions and an *Error
// with ErrDivisionByZero (nonzero dividend) or ErrDivisionUndefined (0/0),
// never a trap-dependent outcome.
func TestDivByZeroErrorsUnderEveryContextAndTrap(t *testing.T) {
	bases := []Context{{}}
	for mode := TiesToEven; mode <= Exact; mode++ {
		bases = append(bases, mustContext(t, 5, mode))
	}
	guarded, err := NewContext(3, TiesToEven, &ExponentGuards{Emin: -2, Emax: 2}, 0)
	if err != nil {
		t.Fatal(err)
	}
	bases = append(bases, guarded)
	calls := 0
	for _, base := range bases {
		for _, traps := range []Conditions{0, DivisionByZero | DivisionUndefined, trappableConditions} {
			ctx, err := base.WithTraps(traps)
			if err != nil {
				t.Fatalf("WithTraps(%v): %v", traps, err)
			}
			for _, dividend := range []Decimal{MustParse("-7.5"), Zero()} {
				code, condition := ErrDivisionByZero, DivisionByZero
				if dividend.IsZero() {
					code, condition = ErrDivisionUndefined, DivisionUndefined
				}
				for _, divisor := range []Decimal{Zero(), MustParse("0E+5")} {
					for op, fn := range map[string]func() (Decimal, Conditions, error){
						"DivWithContext": func() (Decimal, Conditions, error) { return dividend.DivWithContext(divisor, ctx) },
						"DivWithContext budgeted": func() (Decimal, Conditions, error) {
							return dividend.DivWithContext(divisor, ctx.WithBudget(Budget{MaxWork: 1}))
						},
					} {
						calls++
						got, cond, err := fn()
						var oe *Error
						if !errors.Is(err, code) || !errors.As(err, &oe) || oe.Op != strings.TrimSuffix(op, " budgeted") || oe.Condition != condition ||
							oe.Code == 0 || !isZeroValue(got) || cond != 0 {
							t.Fatalf("%s(%v, %v) prec %d traps %v: (%v, %v, %#v), want Decimal{}, 0, %v", op, dividend, divisor,
								ctx.Precision(), traps, got, cond, err, code)
						}
					}
				}
			}
		}
	}
	if calls != 10*3*2*2*2 {
		t.Fatalf("ran %d calls", calls)
	}
}

// TestDivisionHasNoAmbientEngineScale checks that no database engine rule
// applies implicitly: division and multiplication follow the core
// ideal-exponent semantics, not an engine's division scale or
// assignment rounding. Hand-derived: 10/4 = 2.5 at exponent -1 (PostgreSQL
// would give 2.5000000000000000, MySQL 2.5000); 6.0/2 = 3.0 at the ideal
// exponent -1; 1/8 = 0.125 at -3; 1.10*2.00 = 2.2000 at -4 (no SQL Server
// scale reduction); and 1/3, which no finite scale represents, is refused
// with Inexact instead of being rounded to an ambient scale.
func TestDivisionHasNoAmbientEngineScale(t *testing.T) {
	for _, tc := range []struct {
		a, b, op, want string
		exponent       int32
	}{
		{"10", "4", "div", "2.5", -1},
		{"6.0", "2", "div", "3.0", -1},
		{"1", "8", "div", "0.125", -3},
		{"1.10", "2.00", "mul", "2.2000", -4},
	} {
		a, b := MustParse(tc.a), MustParse(tc.b)
		var got Decimal
		var err error
		if tc.op == "div" {
			got, err = a.Div(b)
		} else {
			got, err = a.Mul(b)
		}
		if err != nil || got.String() != tc.want || got.Exponent() != tc.exponent {
			t.Errorf("%s %s %s = %v (exponent %d), %v; want %s at %d", tc.a, tc.op, tc.b, got, got.Exponent(), err, tc.want, tc.exponent)
		}
	}
	got, err := MustParse("1").Div(MustParse("3"))
	var ce *Error
	if !errors.Is(err, ErrInexact) || !errors.As(err, &ce) || ce.Code != 0 || ce.Op != "Div" || ce.Condition != Inexact || !isZeroValue(got) {
		t.Errorf("1/3 = %v, %#v; want Decimal{} and a Div Inexact refusal", got, err)
	}
}

// TestDivContextCarryBoundary pins the all-nines guard carry:
// rounding 9.9 to one significant digit yields 1E+1, not coefficient 1
// at the old exponent. Negative direction is reversed independently.
func TestDivContextCarryBoundary(t *testing.T) {
	for _, sign := range []int64{-1, 1} {
		ctx := mustContext(t, 1, TiesToEven)
		got, c, err := New(99*sign, 0).DivWithContext(New(10, 0), ctx)
		want := New(sign, 1)
		direction := Increased
		if sign < 0 {
			direction = Decreased
		}
		if err != nil || !got.Equal(want) || got.Exponent() != 1 || c != Rounded|Inexact|direction {
			t.Fatalf("carry sign%d: got %v %v %v, want %v %v", sign, got, c, err, want, Rounded|Inexact|direction)
		}
	}
}

// TestDivExactProbeMatchesGeneral covers the exact-first probe: with and
// without the probe the call agrees with independent rational rounding on
// cohorts, conditions and errors, and a failed probe plus the fallback
// stays within the precharge B.
func TestDivExactProbeMatchesGeneral(t *testing.T) {
	var exact, fallback, guarded int
	for _, text := range []string{"2", "3", "5", "7", "11", "13", "17", "1.25", "1024", "0.0002", "9999999999999999997"} {
		for _, neg := range []bool{false, true} {
			x, y := New(7, -2), MustParse(text)
			if neg {
				x = x.Neg()
			}
			for _, precision := range []uint32{256, 4096} {
				for _, guards := range []*ExponentGuards{nil, {Emin: -2, Emax: 2}} {
					for mode := TiesToEven; mode <= Exact; mode++ {
						ctx := contextTestContext(t, precision, mode, guards, 0)
						s := newDivSource(x, y)
						target, etiny := divContextTarget(s.dx, s.dy, s.ideal, ctx)
						plan := s.plan(target)
						trial, tt, eligible := s.exactProbe(plan, target)
						if !eligible {
							continue
						}
						count := &divCount{}
						got, c, err := s.contextQuotient(plan, target, etiny, &ctx, plan.charge, limits{}, "Div", count, 0, true)
						want, wc, we := s.contextQuotient(plan, target, etiny, &ctx, plan.charge, limits{}, "Div", nil, 0, false)
						label := fmt.Sprintf("%s/%s p%d mode%d guards%v", x, y, precision, mode, guards)
						if got.Exponent() != want.Exponent() || !got.Equal(want) || c != wc || fmt.Sprint(err) != fmt.Sprint(we) {
							t.Fatalf("%s fast/general: %v %v %v / %v %v %v", label, got, c, err, want, wc, we)
						}
						if count.units > plan.charge {
							t.Fatalf("%s counted work %d > original B %d", label, count.units, plan.charge)
						}
						q := new(big.Rat).Quo(divRat(t, x), divRat(t, y))
						oracle := oracleContext(q, s.ideal, int64(precision), mode)
						if guards != nil {
							oracle = oracleGuarded(q, s.ideal, int64(precision), int64(guards.Emin), int64(guards.Emax), mode)
							guarded++
						}
						checkDivOutcome(t, label, got, c, err, oracle, neg)
						_, _, _, done := s.tryExactContext(trial, tt, etiny, &ctx, plan.charge, limits{}, "Div", nil, 0)
						if done && err == nil {
							exact++
						} else if !done {
							fallback++
						}
						// The work precharge B is checked first, even on Exact's
						// nontermination refusal; a successful result still pays 2N+1.
						_, _, lowErr := x.DivWithContext(y, ctx.WithBudget(Budget{MaxWork: plan.charge - 1}))
						if !errors.Is(lowErr, ErrInsufficientStorage) {
							t.Fatalf("%s lost precharge: %v", label, lowErr)
						}
						if err == nil {
							w := plan.charge + 2*got.CoefficientDigits() + 1
							for _, cap := range []uint64{w - 1, w} {
								_, _, e := x.DivWithContext(y, ctx.WithBudget(Budget{MaxWork: cap}))
								if cap == w && e != nil || cap < w && !errors.Is(e, ErrInsufficientStorage) {
									t.Fatalf("%s cap%d/W%d: %v", label, cap, w, e)
								}
							}
						}
					}
				}
			}
		}
	}
	if exact < 100 || fallback < 100 || guarded < 100 {
		t.Fatalf("vacuous probe coverage: exact%d fallback%d guarded%d", exact, fallback, guarded)
	}
}

// TestDivProbePhysicalEnvelope covers the probe's combined live admission and
// checked target arithmetic. These synthetic live-byte limits refuse without
// trying to allocate near the runtime limit.
func TestDivProbePhysicalEnvelope(t *testing.T) {
	x, y := One(), New(2, 0)
	s := newDivSource(x, y)
	ctx := contextTestContext(t, 1<<18, TiesToEven, nil, 0)
	target, etiny := divContextTarget(s.dx, s.dy, s.ideal, ctx)
	plan := s.plan(target)
	trial, tt, ok := s.exactProbe(plan, target)
	if !ok {
		t.Fatal("probe witness ineligible")
	}
	_, maxAddress, ok := bigIntRuntimeLimits(runtime.GOOS, runtime.GOARCH, uint64(bits.UintSize))
	if !ok || divAdmittedLive(49, 1, maxAddress-1) {
		t.Fatal("separately valid arenas bypassed combined limit")
	}
	// 1/(2E-2) overflows under Emax=0; although its exact coefficient is
	// short, the result is p nines and cannot fit beside maxAddress-128.
	s.ideal = 2
	ctx = contextTestContext(t, 1<<18, TiesToEven, &ExponentGuards{Emin: -2, Emax: 0}, 0)
	target, etiny = divContextTarget(s.dx, s.dy, s.ideal, ctx)
	plan = s.plan(target)
	trial, tt, ok = s.exactProbe(plan, target)
	if !ok || s.probeResultDigits(trial, &ctx) != uint64(ctx.Precision()) {
		t.Fatal("overflow probe lost p-digit publication")
	}
	_, _, _, done := s.tryExactContext(trial, tt, etiny, &ctx, plan.charge, limits{}, "Div", nil, maxAddress-128)
	if done {
		t.Fatal("probe ignored combined overflow publication limit")
	}
	// A finite-context planner must not inherit bare Div's ideal<MinInt32
	// rejection; this method only selects a trial, whose finisher owns range.
	s.ideal = math.MinInt32 - 1
	target = s.ideal - 1000
	if _, _, ok := s.exactProbe(s.plan(target), target); !ok {
		t.Fatal("probe imported exact-only exponent restriction")
	}
	s.dy = math.MaxUint64
	if _, _, ok := s.exactProbe(divPlan{ok: true, path: divDivide, dn: math.MaxUint64}, math.MinInt64); ok {
		t.Fatal("overflowed probe arithmetic was admitted")
	}
}

// TestDivExactProbeRandomAndTraps covers the exact-first probe randomly and its
// trap identity. Seeded operands span signs, scale, terminating denominators,
// general denominators and guarded results; the path without the probe owns
// the semantics.
func TestDivExactProbeRandomAndTraps(t *testing.T) {
	rng := rand.New(rand.NewPCG(72, 1))
	var compared, trapped int
	for i := range 240 {
		x := New(int64(rng.IntN(999999)+1), int32(rng.IntN(15)-7))
		if i%2 == 0 {
			x = x.Neg()
		}
		y := New(int64(rng.IntN(99999)+2), int32(rng.IntN(15)-7))
		if i%3 == 0 {
			y = powDecimal(new(big.Int).Lsh(big.NewInt(1), uint(1+rng.IntN(90))), 0)
		}
		var guards *ExponentGuards
		if i%2 == 0 {
			guards = &ExponentGuards{Emin: -2, Emax: 2}
		}
		ctx := contextTestContext(t, 2048, allModes[i%len(allModes)], guards, Inexact|Rounded|Overflow|Underflow|Subnormal)
		s := newDivSource(x, y)
		target, etiny := divContextTarget(s.dx, s.dy, s.ideal, ctx)
		plan := s.plan(target)
		if _, _, eligible := s.exactProbe(plan, target); !eligible {
			continue
		}
		got, c, err := s.contextQuotient(plan, target, etiny, &ctx, plan.charge, limits{}, "Div", nil, 0, true)
		want, wc, we := s.contextQuotient(plan, target, etiny, &ctx, plan.charge, limits{}, "Div", nil, 0, false)
		if !got.Equal(want) || got.Exponent() != want.Exponent() || c != wc || fmt.Sprintf("%#v", err) != fmt.Sprintf("%#v", we) {
			t.Fatalf("case%d %v/%v: fast %v %v %#v / general %v %v %#v", i, x, y, got, c, err, want, wc, we)
		}
		compared++
		if _, ok := errors.AsType[*Error](err); ok {
			trapped++
		}
	}
	if compared < 200 || trapped < 100 {
		t.Fatalf("vacuous comparisons%d traps%d", compared, trapped)
	}
}

// divSameResult compares two division outcomes field by field: storage,
// packed sign and exponent, slow limbs, conditions and the error value.
func divSameResult(a Decimal, ac Conditions, ae error, b Decimal, bc Conditions, be error) bool {
	if a.words != b.words || a.meta != b.meta || (a.slow == nil) != (b.slow == nil) || ac != bc || !reflect.DeepEqual(ae, be) {
		return false
	}
	return a.slow == nil || slices.Equal(a.slow.limbs, b.slow.limbs)
}

// divInlineCorpus returns inline fast-path operands: inline dividends and
// one-word divisors at boundaries (one and two words, 2^64 and 2^128
// edges, powers of ten, ties and carries) plus random magnitudes.
func divInlineCorpus(rng *rand.Rand) (dividends []uint128, divisors []uint64) {
	const maxWord = math.MaxUint64
	dividends = []uint128{
		{lo: 1}, {lo: 2}, {lo: 5}, {lo: 9}, {lo: 10}, {lo: 15}, {lo: 25}, {lo: 99}, {lo: 125},
		{lo: 1 << 32}, {lo: maxWord - 1}, {lo: maxWord}, {hi: 1}, {lo: 1, hi: 1},
		{lo: pow10Words[19]}, {lo: pow10Words[19] - 1}, pow10Wide[20], pow10Wide[38],
		{lo: pow10Wide[38].lo - 1, hi: pow10Wide[38].hi}, {lo: maxWord, hi: maxWord},
		{hi: 1 << 63}, {lo: maxWord - 2, hi: 2}, // 3·(2^64−1)+1: carry into the high word
	}
	divisors = []uint64{
		1, 2, 3, 4, 5, 7, 8, 10, 16, 20, 25, 40, 64, 125, 1024, 3 << 10, 1953125,
		7450580596923828125, 1 << 63, maxWord, maxWord - 1, pow10Words[19], pow10Words[19] - 1,
		pow10Words[18], 999999999, 1000000007, 6, 12, 48, 80,
	}
	for range 60 {
		bitsLen := 1 + rng.IntN(128)
		w := uint128{lo: rng.Uint64(), hi: rng.Uint64()}
		if bitsLen <= 64 {
			w = uint128{lo: w.lo >> (64 - bitsLen)}
		} else {
			w.hi >>= 128 - bitsLen
		}
		if w == (uint128{}) {
			w.lo = 1
		}
		dividends = append(dividends, w)
		y := rng.Uint64() >> rng.IntN(64)
		if y == 0 {
			y = 7
		}
		divisors = append(divisors, y)
	}
	// Terminating divisors 2^a·5^b, so bare Div is served often.
	for a := 0; a < 64; a += 3 {
		for b, five := 0, uint64(1); b < 28; b, five = b+2, five*25 {
			if hi, lo := bits.Mul64(five, 1<<a); hi == 0 {
				divisors = append(divisors, lo)
			}
			if five > math.MaxUint64/25 {
				break
			}
		}
	}
	// Exact ties and round-up carries at k = 0: x = q·y + y/2 (+1).
	for range 30 {
		y := (rng.Uint64() >> rng.IntN(64)) | 2
		y &^= 1
		q := rng.Uint64() >> rng.IntN(64)
		hi, lo := bits.Mul64(q, y)
		lo, c := bits.Add64(lo, y/2, 0)
		dividends = append(dividends, uint128{lo: lo, hi: hi + c})
		lo, c = bits.Add64(lo, 1, 0)
		dividends = append(dividends, uint128{lo: lo, hi: hi + c})
		divisors = append(divisors, y)
	}
	return dividends, divisors
}

var sinkDivDecimal Decimal

func divInlineExactServes(x, y Decimal) bool {
	_, ok := inlineDivExact(x, y)
	return ok
}

// TestDivInlineMatchesGeneral pins the inline division fast paths
// of Div, DivToExponent(WithBudget) and DivWithContext to the general limb
// path: identical storage, cohort, sign, Conditions, error identity and
// allocation count over boundary and random operands, signs, every rounding
// mode (with exact ties and carries), exponents at the int32 limits,
// guarded and trapping contexts, deferred shapes (zero, slow, two-word
// divisor) and refusing or admitting budgets. Served cases with moderate
// exponents are also checked against the independent math/big oracles, and
// a vacuity guard requires the fast paths to serve a substantial share.
func TestDivInlineMatchesGeneral(t *testing.T) {
	rng := rand.New(rand.NewPCG(20261030, 88))
	dividends, divisors := divInlineCorpus(rng)
	exponents := []int32{0, -2, 3, -19, 19, math.MinInt32, math.MinInt32 + 1, math.MinInt32 + 40, math.MaxInt32, math.MaxInt32 - 1, math.MaxInt32 - 40}
	exponent := func() int32 {
		if rng.IntN(3) == 0 {
			return exponents[rng.IntN(len(exponents))]
		}
		return int32(rng.IntN(61) - 30)
	}
	deferred := []Decimal{{}, MustParse("-0.00"), MustParse("340282366920938463463374607431768211456"), MustParse("-123456789012345678901234567890.5"), inlineDecimal(uint128{lo: 3, hi: 1}, -4, false)}
	mode := func() RoundingMode { return allDivModes[rng.IntN(len(allDivModes))] }
	contexts := []func() Context{
		func() Context { return contextTestContext(t, uint32(1+rng.IntN(40)), mode(), nil, 0) },
		func() Context {
			emin := int32(rng.IntN(81) - 40)
			return contextTestContext(t, uint32(1+rng.IntN(25)), mode(), &ExponentGuards{Emin: emin, Emax: emin + int32(rng.IntN(60))}, 0)
		},
		func() Context {
			return contextTestContext(t, uint32(1+rng.IntN(38)), mode(), &ExponentGuards{Emin: math.MinInt32 + 40, Emax: math.MaxInt32}, 0)
		},
		func() Context {
			traps := []Conditions{Inexact, Rounded, Subnormal | Underflow, Overflow | Inexact}[rng.IntN(4)]
			return contextTestContext(t, uint32(1+rng.IntN(19)), mode(), &ExponentGuards{Emin: -5, Emax: 5}, traps)
		},
	}
	budgets := []Budget{{}, {MaxInputBytes: 3}, {MaxWork: 1}, {MaxDigits: 1}, {MaxWork: 40}, {MaxWork: math.MaxUint64, MaxDigits: math.MaxUint64}}
	moderate := func(es ...int64) bool {
		for _, e := range es {
			if e < -80 || e > 80 {
				return false
			}
		}
		return true
	}
	var cases, servedExact, servedTo, servedContext, oracled int
	for i := range 40000 {
		var x, y Decimal
		switch {
		case i%50 == 0:
			x = deferred[rng.IntN(len(deferred))]
			y = inlineDecimal(uint128{lo: divisors[rng.IntN(len(divisors))]}, exponent(), rng.IntN(2) == 0)
		case i%50 == 25:
			x = inlineDecimal(dividends[rng.IntN(len(dividends))], exponent(), rng.IntN(2) == 0)
			y = deferred[rng.IntN(len(deferred))]
		default:
			x = inlineDecimal(dividends[rng.IntN(len(dividends))], exponent(), rng.IntN(2) == 0)
			y = inlineDecimal(uint128{lo: divisors[rng.IntN(len(divisors))]}, exponent(), rng.IntN(2) == 0)
		}
		ideal := int64(x.exponent()) - int64(y.exponent())
		negative := x.negative() != y.negative()
		label := fmt.Sprintf("%d: %s·10^%d / %s·10^%d", i, x.coefficientDigits(), x.exponent(), y.coefficientDigits(), y.exponent())
		served := inlineDivOperands(x, y)
		cases++

		// Div.
		got, err := x.Div(y)
		want, _, wantErr := x.divUnlimitedLimbs(y, limits{}, "Div")
		if !divSameResult(got, 0, err, want, 0, wantErr) {
			t.Fatalf("%s Div: fast %v %v, general %v %v", label, got, err, want, wantErr)
		}
		if served && divInlineExactServes(x, y) {
			servedExact++
			if moderate(ideal, int64(x.exponent()), int64(y.exponent())) {
				oracled++
				expect, ok := oracleExact(new(big.Rat).Quo(divRat(t, x), divRat(t, y)), ideal)
				if !ok {
					t.Fatalf("%s Div served a nonterminating quotient", label)
				}
				checkDivOutcome(t, label+" Div", got, 0, err, expect, negative)
			}
		}

		// DivToExponent and DivToExponentWithBudget.
		// The general path does work proportional to a positive gap
		// ideal − target, so huge positive gaps are not compared.
		target64 := ideal + int64(rng.IntN(91)-45)
		if rng.IntN(8) == 0 {
			target64 = int64(exponent())
		}
		target := int32(min(max(target64, math.MinInt32), math.MaxInt32))
		m := RoundingMode(rng.IntN(int(Exact) + 2)) // includes one invalid mode
		toExponent := ideal-int64(target) <= 120
		if toExponent {
			gotT, gotC, gotE := x.DivToExponent(y, target, m)
			wantT, wantC, wantE := x.divToExponentLimbs(y, target, m, limits{}, "DivToExponent")
			if !divSameResult(gotT, gotC, gotE, wantT, wantC, wantE) {
				t.Fatalf("%s DivToExponent(%d, %v): fast %v %v %v, general %v %v %v", label, target, m, gotT, gotC, gotE, wantT, wantC, wantE)
			}
			if served && m <= Exact {
				if _, _, _, ok := inlineDivToExponent(x, y, target, m); ok {
					servedTo++
					if moderate(ideal, int64(target), int64(x.exponent()), int64(y.exponent())) {
						oracled++
						q := new(big.Rat).Quo(divRat(t, x), divRat(t, y))
						checkDivOutcome(t, fmt.Sprintf("%s DivToExponent(%d, %v)", label, target, m), gotT, gotC, gotE, oracleToExponent(q, ideal, int64(target), m), negative)
					}
				}
			}
			budget := budgets[rng.IntN(len(budgets))]
			gotB, gotBC, gotBE := x.DivToExponentWithBudget(y, target, m, budget)
			wantB, wantBC, wantBE := x.divToExponentLimbs(y, target, m, budget.arith(), "DivToExponentWithBudget")
			if !divSameResult(gotB, gotBC, gotBE, wantB, wantBC, wantBE) {
				t.Fatalf("%s DivToExponentWithBudget(%d, %v, %+v): fast %v %v %v, general %v %v %v", label, target, m, budget, gotB, gotBC, gotBE, wantB, wantBC, wantBE)
			}
		}

		// DivWithContext, unbudgeted and budgeted.
		ctx := contexts[rng.IntN(len(contexts))]()
		if rng.IntN(4) == 0 {
			ctx = ctx.WithBudget(budgets[rng.IntN(len(budgets))])
		}
		gotX, gotXC, gotXE := x.DivWithContext(y, ctx)
		wantX, wantXC, wantXE := x.divContextLimbs(y, ctx, ctx.arith, "DivWithContext")
		if !divSameResult(gotX, gotXC, gotXE, wantX, wantXC, wantXE) {
			t.Fatalf("%s DivWithContext(p%d %v guards%v %+v traps%v budget%+v): fast %v %v %v, general %v %v %v", label, ctx.precision, ctx.rounding, ctx.guarded, ctx.guards, ctx.traps, ctx.arith, gotX, gotXC, gotXE, wantX, wantXC, wantXE)
		}
		if served && ctx.arith == (limits{}) && ctx.precision <= inlineDivMaxPrecision {
			if _, _, _, ok := inlineDivContext(x, y, &ctx, "DivWithContext"); ok {
				servedContext++
				if ctx.traps == 0 && moderate(ideal, int64(x.exponent()), int64(y.exponent())) && (!ctx.guarded || moderate(int64(ctx.guards.Emin), int64(ctx.guards.Emax))) {
					oracled++
					q := new(big.Rat).Quo(divRat(t, x), divRat(t, y))
					expect := oracleContext(q, ideal, int64(ctx.precision), ctx.rounding)
					if ctx.guarded {
						expect = oracleGuarded(q, ideal, int64(ctx.precision), int64(ctx.guards.Emin), int64(ctx.guards.Emax), ctx.rounding)
					}
					checkDivOutcome(t, fmt.Sprintf("%s DivWithContext(p%d %v guards%v %+v)", label, ctx.precision, ctx.rounding, ctx.guarded, ctx.guards), gotX, gotXC, gotXE, expect, negative)
				}
			}
		}

		if i%400 == 0 && toExponent {
			pairs := [][2]func(){
				{func() { sinkDivDecimal, _ = x.Div(y) }, func() { sinkDivDecimal, _, _ = x.divUnlimitedLimbs(y, limits{}, "Div") }},
				{func() { sinkDivDecimal, _, _ = x.DivToExponent(y, target, m) }, func() { sinkDivDecimal, _, _ = x.divToExponentLimbs(y, target, m, limits{}, "DivToExponent") }},
				{func() { sinkDivDecimal, _, _ = x.DivWithContext(y, ctx) }, func() { sinkDivDecimal, _, _ = x.divContextLimbs(y, ctx, ctx.arith, "DivWithContext") }},
			}
			for j, pair := range pairs {
				if fast, general := testing.AllocsPerRun(20, pair[0]), testing.AllocsPerRun(20, pair[1]); fast != general {
					t.Fatalf("%s entry %d allocations: fast %v, general %v", label, j, fast, general)
				}
			}
		}
	}
	if servedExact < cases/4 || servedTo < cases/3 || servedContext < cases/4 || oracled < cases/2 {
		t.Fatalf("vacuous inline coverage: cases %d, served Div %d, DivToExponent %d, DivWithContext %d, oracle checks %d", cases, servedExact, servedTo, servedContext, oracled)
	}
	t.Logf("cases %d, served Div %d, DivToExponent %d, DivWithContext %d, oracle checks %d", cases, servedExact, servedTo, servedContext, oracled)
}
