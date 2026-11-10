// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"errors"
	"fmt"
	"math"
	"math/big"
	"math/rand/v2"
	"slices"
	"strings"
	"testing"
)

// sqrtGuards is the oracle's view of optional exponent guards.
type sqrtGuards struct {
	on         bool
	emin, emax int64
}

// sqrtWant is an oracle outcome: the coefficient and exponent of the
// result with its Conditions, or the Exact refusal.
type sqrtWant struct {
	coefficient *big.Int
	exponent    int64
	conditions  Conditions
	refused     bool
}

// sqrtScaled is c·10^k as a rational.
func sqrtScaled(c *big.Int, k int64) *big.Rat {
	return new(big.Rat).Mul(new(big.Rat).SetInt(c), pow10Rat(k))
}

// sqrtOracle rounds √(c·10^e), c > 0, to p digits in mode, independently
// of the library: the result exponent comes from the adjusted exponent
// ⌊(e + digits(c) − 1)/2⌋, q = big.Int.Sqrt of ⌊X⌋ with X = c·10^(e−2t)
// (⌊√X⌋ = ⌊√⌊X⌋⌋), exactness from q² = X as rationals, and the half class
// from comparing 4X with (2q+1)². Guards follow GDA: overflow above Emax
// substitutes the largest finite value, and a root whose adjusted exponent
// lies below Emin is Subnormal (and Underflow when inexact).
func sqrtOracle(c *big.Int, e, p int64, mode RoundingMode, g sqrtGuards) sqrtWant {
	adjusted := e + int64(len(c.String())) - 1
	a := adjusted >> 1
	ideal := e >> 1
	overflow := func() sqrtWant {
		if mode == Exact {
			return sqrtWant{refused: true}
		}
		nines := new(big.Int).Sub(new(big.Int).Exp(big.NewInt(10), big.NewInt(p), nil), big.NewInt(1))
		return sqrtWant{coefficient: nines, exponent: g.emax - p + 1, conditions: Overflow | Inexact | Rounded | Decreased}
	}
	if g.on && a > g.emax {
		return overflow()
	}
	t := a - p + 1
	if g.on {
		t = max(t, g.emin-p+1)
	}
	x := sqrtScaled(c, e-2*t)
	floor := new(big.Int).Quo(x.Num(), x.Denom())
	q := new(big.Int).Sqrt(floor)
	qq := new(big.Rat).SetInt(new(big.Int).Mul(q, q))
	exact := qq.Cmp(x) == 0
	twice := new(big.Int).Add(new(big.Int).Lsh(q, 1), big.NewInt(1))
	half := new(big.Rat).Mul(x, big.NewRat(4, 1)).Cmp(new(big.Rat).SetInt(new(big.Int).Mul(twice, twice)))
	if mode == Exact && !exact {
		return sqrtWant{refused: true}
	}
	up := false
	if !exact {
		odd := q.Bit(0) == 1
		switch mode {
		case AwayFromZero, TowardPositiveInfinity:
			up = true
		case TiesToEven:
			up = half > 0 || half == 0 && odd
		case TiesAwayFromZero:
			up = half >= 0
		case TiesTowardZero:
			up = half > 0
		}
	}
	if up {
		q.Add(q, big.NewInt(1))
		if int64(len(q.String())) > p {
			q.Quo(q, big.NewInt(10))
			t++
		}
	}
	if g.on && q.Sign() != 0 && t+int64(len(q.String()))-1 > g.emax {
		return overflow()
	}
	var conditions Conditions
	switch {
	case !exact:
		conditions = Inexact | Rounded | Decreased
		if up {
			conditions = Inexact | Rounded | Increased
		}
	case t > ideal:
		conditions = Rounded
	default:
		for t < ideal && q.Sign() != 0 && new(big.Int).Mod(q, big.NewInt(10)).Sign() == 0 {
			q.Quo(q, big.NewInt(10))
			t++
		}
	}
	if g.on && a < g.emin {
		conditions |= Subnormal
		if !exact {
			conditions |= Underflow
		}
	}
	return sqrtWant{coefficient: q, exponent: t, conditions: conditions}
}

// sqrtCheck compares one SqrtWithContext outcome with the oracle, and
// checks the direction bit independently: sign(result² − v).
func sqrtCheck(t *testing.T, label string, v Decimal, got Decimal, conditions Conditions, err error, want sqrtWant) {
	t.Helper()
	if want.refused {
		var ce *Error
		if !errors.As(err, &ce) || ce.Code != 0 || ce.Condition != Inexact || !got.Equal(Decimal{}) || conditions != 0 {
			t.Fatalf("%s: (%v, %v, %v), want the Exact refusal", label, got, conditions, err)
		}
		return
	}
	if err != nil {
		t.Fatalf("%s: %v", label, err)
	}
	if got.negative() || got.coefficientDigits() != want.coefficient.String() || int64(got.exponent()) != want.exponent || conditions != want.conditions {
		t.Fatalf("%s: %s·10^%d %v, want %s·10^%d %v", label, got.coefficientDigits(), got.exponent(), conditions, want.coefficient, want.exponent, want.conditions)
	}
	if conditions&Overflow != 0 {
		return
	}
	r := divRat(t, got)
	square := new(big.Rat).Mul(r, r)
	switch square.Cmp(divRat(t, v)) {
	case 1:
		if conditions&Increased == 0 {
			t.Fatalf("%s: result above the root without Increased (%v)", label, conditions)
		}
	case -1:
		if conditions&Decreased == 0 {
			t.Fatalf("%s: result below the root without Decreased (%v)", label, conditions)
		}
	default:
		if conditions&(Inexact|Increased|Decreased) != 0 {
			t.Fatalf("%s: exact root reported %v", label, conditions)
		}
	}
}

// sqrtOperand draws a positive operand: random digits, a perfect square
// (possibly with trailing zeros), or a square of a (p+1)-digit value
// ending in 5 (a tie at p digits).
func sqrtOperand(r *rand.Rand, maxDigits int, p int64) *big.Int {
	switch r.IntN(4) {
	case 0:
		root := randomDigits(r, 1+r.IntN(max(1, maxDigits/2)))
		return root.Mul(root, root)
	case 1:
		root := randomDigits(r, int(p))
		root.Mul(root, big.NewInt(10)).Add(root, big.NewInt(5))
		return root.Mul(root, root)
	}
	c := randomDigits(r, 1+r.IntN(maxDigits))
	if r.IntN(5) == 0 {
		c.Mul(c, new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(r.IntN(12))), nil))
	}
	return c
}

// randomDigits is a random integer of exactly n digits.
func randomDigits(r *rand.Rand, n int) *big.Int {
	b := make([]byte, n)
	for i := range b {
		b[i] = byte('0' + r.IntN(10))
	}
	b[0] = byte('1' + r.IntN(9))
	v, _ := new(big.Int).SetString(string(b), 10)
	return v
}

func sqrtDecimal(c *big.Int, e int64) Decimal {
	return MustParse(fmt.Sprintf("%sE%d", c, e))
}

// TestSqrtAgainstBigOracle checks that an inexact root rounds once in each
// mode: over random operands, exact squares, trailing
// zeros and ties, in all eight modes at random precisions, SqrtWithContext
// equals the big.Int.Sqrt oracle in value, exponent and Conditions, the
// direction bit agrees with sign(result² − v), and the directed pair
// encloses the root on its p-digit grid.
func TestSqrtAgainstBigOracle(t *testing.T) {
	r := rand.New(rand.NewPCG(53, 3))
	cases := 6000
	if testing.Short() {
		cases = 1500
	}
	inexact, ties := 0, 0
	for i := range cases {
		p := int64(1 + r.IntN(40))
		if r.IntN(10) == 0 {
			p = int64(41 + r.IntN(120))
		}
		c := sqrtOperand(r, 70, p)
		e := int64(r.IntN(81) - 40)
		v := sqrtDecimal(c, e)
		for mode := TiesToEven; mode <= Exact; mode++ {
			ctx := mustContext(t, uint32(p), mode)
			got, conditions, err := v.SqrtWithContext(ctx)
			want := sqrtOracle(c, e, p, mode, sqrtGuards{})
			sqrtCheck(t, fmt.Sprintf("case %d √%s p=%d %v", i, v, p, mode), v, got, conditions, err, want)
			if mode == TiesToEven && want.conditions&Inexact != 0 {
				inexact++
			}
		}
		lo, loConditions, _ := v.SqrtWithContext(mustContext(t, uint32(p), TowardNegativeInfinity))
		hi, hiConditions, _ := v.SqrtWithContext(mustContext(t, uint32(p), TowardPositiveInfinity))
		loRat, hiRat, value := divRat(t, lo), divRat(t, hi), divRat(t, v)
		if new(big.Rat).Mul(loRat, loRat).Cmp(value) > 0 || new(big.Rat).Mul(hiRat, hiRat).Cmp(value) < 0 {
			t.Fatalf("case %d: [%v, %v] does not enclose √%v", i, lo, hi, v)
		}
		if loConditions&Inexact != 0 {
			if gap := new(big.Rat).Sub(hiRat, loRat); gap.Cmp(pow10Rat(int64(lo.exponent()))) != 0 {
				t.Fatalf("case %d: enclosure [%v, %v] is not one quantum wide", i, lo, hi)
			}
			if hiConditions&Increased == 0 || loConditions&Decreased == 0 {
				t.Fatalf("case %d: enclosure directions %v %v", i, loConditions, hiConditions)
			}
			ties += boolInt(sqrtOracle(c, e, p, TiesAwayFromZero, sqrtGuards{}).coefficient.Cmp(sqrtOracle(c, e, p, TiesTowardZero, sqrtGuards{}).coefficient) != 0)
		}
	}
	if inexact < cases/3 || ties < 50 {
		t.Fatalf("vacuous corpus: %d inexact, %d ties of %d", inexact, ties, cases)
	}
}

func boolInt(b bool) int {
	if b {
		return 1
	}
	return 0
}

// TestSqrtTieCorpus covers a tie corpus: squares of (p+1)-digit
// integers ending in 5 sit exactly halfway at p digits, so the three tie
// modes separate, and a one-unit perturbation of the square breaks the
// tie in the direction of the perturbation. √1.5625 at p = 2 is 1.2 under
// TiesToEven and TiesTowardZero and 1.3 under TiesAwayFromZero.
func TestSqrtTieCorpus(t *testing.T) {
	v := MustParse("1.5625")
	for _, tc := range []struct {
		mode RoundingMode
		want string
	}{
		{TiesToEven, "1.2"}, {TiesAwayFromZero, "1.3"}, {TiesTowardZero, "1.2"},
		{TowardZero, "1.2"}, {AwayFromZero, "1.3"},
	} {
		got, conditions, err := v.SqrtWithContext(mustContext(t, 2, tc.mode))
		if err != nil || got.String() != tc.want || conditions&(Inexact|Rounded) != Inexact|Rounded {
			t.Fatalf("√1.5625 p=2 %v: %v %v %v, want %s", tc.mode, got, conditions, err, tc.want)
		}
	}
	r := rand.New(rand.NewPCG(53, 4))
	odd := 0
	for i := range 3000 {
		p := int64(1 + r.IntN(45))
		root := randomDigits(r, int(p))
		root.Mul(root, big.NewInt(10)).Add(root, big.NewInt(5))
		square := new(big.Int).Mul(root, root)
		e := int64(r.IntN(41) - 20)
		for _, delta := range []int64{0, -1, 1} {
			c := new(big.Int).Add(square, big.NewInt(delta))
			v := sqrtDecimal(c, e)
			for mode := TiesToEven; mode <= Exact; mode++ {
				got, conditions, err := v.SqrtWithContext(mustContext(t, uint32(p), mode))
				sqrtCheck(t, fmt.Sprintf("tie %d √%s p=%d %v", i, v, p, mode), v, got, conditions, err, sqrtOracle(c, e, p, mode, sqrtGuards{}))
			}
		}
		// The tie itself: TiesAwayFromZero rounds up, TiesTowardZero down.
		v := sqrtDecimal(square, 2*e)
		away, _, _ := v.SqrtWithContext(mustContext(t, uint32(p), TiesAwayFromZero))
		toward, _, _ := v.SqrtWithContext(mustContext(t, uint32(p), TiesTowardZero))
		if away.Equal(toward) {
			t.Fatalf("tie %d: √%s p=%d tie modes agree on %v", i, v, p, away)
		}
		odd += boolInt(new(big.Int).Quo(root, big.NewInt(10)).Bit(0) == 1)
	}
	if odd < 1000 {
		t.Fatalf("vacuous tie corpus: %d odd retained digits", odd)
	}
}

// TestSqrtExactRoots covers exact roots and the exponent rule: an exact root is
// published at the exponent nearest ⌊e/2⌋ that fits p digits, and one that
// needs a higher exponent keeps it with Rounded but not Inexact, which Exact
// permits: √(10000000000) at p = 3 is 1.00E+5 with Rounded. Bare Sqrt publishes
// every exact root at ⌊e/2⌋, over random squares against big.Int.Sqrt.
func TestSqrtExactRoots(t *testing.T) {
	for _, tc := range []struct {
		in, want   string
		p          uint32
		conditions Conditions
	}{
		{"4", "2", 0, 0},
		{"4", "2", 5, 0},
		{"0.25", "0.5", 0, 0},
		{"0.25", "0.5", 7, 0},
		{"4.0", "2.0", 0, 0},
		{"4.0", "2.0", 34, 0},
		{"100", "10", 0, 0},
		{"100", "10", 9, 0},
		{"1E+10", "1E+5", 0, 0},
		{"1E+10", "1E+5", 3, 0},
		{"1E+11", "", 0, 0}, // √10E+10 is irrational
		{"10000000000", "100000", 0, 0},
		{"10000000000", "1.00E+5", 3, Rounded},
		{"10000000000", "100000", 6, 0},
		{"0.0004", "0.02", 0, 0},
		{"4E-2", "0.2", 0, 0},
		{"1.5625", "1.25", 0, 0},
		{"1.5625", "1.25", 3, 0},
		{"152415787532388367501905199875019052100", "12345678901234567890", 0, 0},
		{"152415787532388367501905199875019052100", "1.2346E+19", 5, Inexact | Rounded | Increased},
		{"9.8596E+2", "31.4", 0, 0},
		{"9.8596E+2", "31.4", 3, 0},
		{"9.8596E+2", "31", 2, Inexact | Rounded | Decreased},
	} {
		for _, mode := range []RoundingMode{TiesToEven, Exact} {
			v := MustParse(tc.in)
			var got Decimal
			var conditions Conditions
			var err error
			if tc.p == 0 && mode == TiesToEven {
				got, err = v.Sqrt()
			} else {
				got, conditions, err = v.SqrtWithContext(mustContext(t, tc.p, mode))
			}
			if tc.want == "" || mode == Exact && tc.conditions&Inexact != 0 {
				var ce *Error
				if !errors.As(err, &ce) || ce.Code != 0 || ce.Condition != Inexact {
					t.Fatalf("√%s p=%d %v: %v %v, want refusal", tc.in, tc.p, mode, got, err)
				}
				continue
			}
			if err != nil || got.String() != tc.want || conditions != tc.conditions {
				t.Fatalf("√%s p=%d %v: %v %v %v, want %s %v", tc.in, tc.p, mode, got, conditions, err, tc.want, tc.conditions)
			}
		}
	}
	r := rand.New(rand.NewPCG(53, 5))
	for i := range 3000 {
		root := randomDigits(r, 1+r.IntN(45))
		if r.IntN(4) == 0 {
			root.Mul(root, new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(r.IntN(6))), nil))
		}
		c := new(big.Int).Mul(root, root)
		e := int64(r.IntN(61) - 30)
		if e%2 != 0 && r.IntN(4) != 0 {
			// An odd exponent roots 10·C, a square when C = 10·root².
			c.Mul(c, big.NewInt(10))
		}
		v := sqrtDecimal(c, e)
		got, err := v.Sqrt()
		ideal := e >> 1
		n := new(big.Int).Set(c)
		if e-2*ideal == 1 {
			n.Mul(n, big.NewInt(10))
		}
		want := new(big.Int).Sqrt(n)
		exact := new(big.Int).Mul(want, want).Cmp(n) == 0
		if !exact {
			if _, ok := errors.AsType[*Error](err); !ok {
				t.Fatalf("case %d: √%v = %v %v, want refusal", i, v, got, err)
			}
			continue
		}
		if err != nil || got.coefficientDigits() != want.String() || int64(got.exponent()) != ideal || got.negative() {
			t.Fatalf("case %d: √%v = %v %v, want %s·10^%d", i, v, got, err, want, ideal)
		}
		ctxGot, conditions, err := v.SqrtWithContext(Context{})
		if err != nil || conditions != 0 || !ctxGot.Equal(got) || ctxGot.exponent() != got.exponent() {
			t.Fatalf("case %d: Context{} %v %v %v, bare %v", i, ctxGot, conditions, err, got)
		}
		p := int64(1 + r.IntN(50))
		for _, mode := range []RoundingMode{TiesToEven, Exact} {
			got, conditions, err := v.SqrtWithContext(mustContext(t, uint32(p), mode))
			sqrtCheck(t, fmt.Sprintf("case %d √%v p=%d %v", i, v, p, mode), v, got, conditions, err, sqrtOracle(c, e, p, mode, sqrtGuards{}))
		}
	}
}

// TestSqrtNegativeAndZero covers negative operands and the zero rule: a
// negative nonzero operand is ErrInvalidOperation in
// every form and mode, even Exact and Context{}, while any zero, negative
// included, is an unsigned zero at ⌊e/2⌋ with no Conditions.
func TestSqrtNegativeAndZero(t *testing.T) {
	for _, in := range []string{"-1", "-4", "-0.25", "-1E-999999", "-" + strings.Repeat("9", 200)} {
		v := MustParse(in)
		check := func(op string, got Decimal, conditions Conditions, err error) {
			t.Helper()
			var oe *Error
			if !errors.As(err, &oe) || oe.Op != op || !errors.Is(err, ErrInvalidOperation) || oe.Condition != InvalidOperation || !got.Equal(Decimal{}) || conditions != 0 {
				t.Fatalf("%s(%s): %v %v %v", op, in, got, conditions, err)
			}
		}
		got, err := v.Sqrt()
		check("Sqrt", got, 0, err)
		got, _, err = v.SqrtWithContext(Context{}.WithBudget(Budget{MaxWork: 1}))
		check("SqrtWithContext", got, 0, err)
		for mode := TiesToEven; mode <= Exact; mode++ {
			got, conditions, err := v.SqrtWithContext(mustContext(t, 7, mode))
			check("SqrtWithContext", got, conditions, err)
		}
		got, conditions, err := v.SqrtWithContext(Context{})
		check("SqrtWithContext", got, conditions, err)
		got, conditions, err = v.SqrtWithContext(Decimal128Context().WithBudget(Budget{MaxDigits: 1}))
		check("SqrtWithContext", got, conditions, err)
	}
	for _, tc := range []struct {
		in       string
		exponent int32
	}{{"0", 0}, {"0E-3", -2}, {"0E3", 1}, {"-0E-5", -3}, {"0.00", -1}, {"-0E+7", 3}} {
		v := MustParse(tc.in)
		got, err := v.Sqrt()
		if err != nil || !got.IsZero() || got.negative() || got.exponent() != tc.exponent {
			t.Fatalf("Sqrt(%s) = %v (exp %d) %v, want 0E%d", tc.in, got, got.exponent(), err, tc.exponent)
		}
		for mode := TiesToEven; mode <= Exact; mode++ {
			got, conditions, err := v.SqrtWithContext(mustContext(t, 3, mode))
			if err != nil || conditions != 0 || !got.IsZero() || got.negative() || got.exponent() != tc.exponent {
				t.Fatalf("SqrtWithContext(%s) %v = %v %v %v", tc.in, mode, got, conditions, err)
			}
		}
	}
}

// TestSqrtDefaultModeCoincidesWithGDA checks that the default mode
// coincides with GDA: a context built without choosing a mode (the zero
// RoundingMode, as in Decimal128Context) rounds half-even, so the results
// are those of GDA's fixed half-even squareroot (the digits of √2 and
// √10 are hand-checked, and ties are pinned against the oracle).
func TestSqrtDefaultModeCoincidesWithGDA(t *testing.T) {
	var zero RoundingMode
	if zero != TiesToEven || Decimal128Context().Rounding() != TiesToEven {
		t.Fatal("the zero rounding mode is not TiesToEven")
	}
	for _, tc := range []struct {
		in   string
		ctx  Context
		want string
	}{
		{"2", Decimal128Context(), "1.414213562373095048801688724209698"},
		{"10", Decimal64Context(), "3.162277660168379"},
		{"0.1", Decimal32Context(), "0.3162278"},
		{"1.5625", mustContext(t, 2, zero), "1.2"},
		{"1.8225", mustContext(t, 2, zero), "1.4"},
		{"2.1025", mustContext(t, 2, zero), "1.4"},
	} {
		got, conditions, err := MustParse(tc.in).SqrtWithContext(tc.ctx)
		if err != nil || got.String() != tc.want || conditions&(Inexact|Rounded) != Inexact|Rounded {
			t.Fatalf("√%s: %v %v %v, want %s", tc.in, got, conditions, err, tc.want)
		}
	}
}

// TestSqrtBareRefusesNonExactRoot checks that bare Sqrt refuses a
// non-exact root: bare Sqrt and SqrtWithContext at Context{}, budgeted or
// not, return Decimal{} with the rounding-refused *Error (Condition
// Inexact, errors.Is ErrInexact) naming SqrtWithContext, under each
// form's own Op, including for a long operand and an odd exponent.
func TestSqrtBareRefusesNonExactRoot(t *testing.T) {
	for _, in := range []string{"2", "0.5", "1E+1", "4E-1", "1.5625E-1", "99", strings.Repeat("7", 301)} {
		v := MustParse(in)
		check := func(op string, got Decimal, conditions Conditions, err error) {
			t.Helper()
			var ce *Error
			if !errors.As(err, &ce) || ce.Code != 0 || ce.Op != op || ce.Condition != Inexact || !errors.Is(err, ErrInexact) ||
				!strings.Contains(ce.Error(), "SqrtWithContext") || !got.Equal(Decimal{}) || got.exponent() != 0 || conditions != 0 {
				t.Fatalf("%s(%s): %v %v %v", op, in, got, conditions, err)
			}
		}
		got, err := v.Sqrt()
		check("Sqrt", got, 0, err)
		got, _, err = v.SqrtWithContext(Context{})
		check("SqrtWithContext", got, 0, err)
		got, conditions, err := v.SqrtWithContext(Context{})
		check("SqrtWithContext", got, conditions, err)
		got, conditions, err = v.SqrtWithContext(Context{})
		check("SqrtWithContext", got, conditions, err)
	}
}

// TestSqrtExactModeRefusal covers the Exact mode for Sqrt: under
// Exact a root that must change value is refused with Decimal{}, zero
// Conditions and the Inexact refusal whatever the traps, while an exact root
// succeeds, including the zero-only discard that reports Rounded.
func TestSqrtExactModeRefusal(t *testing.T) {
	traps, err := NewContext(5, Exact, nil, Rounded|Inexact|Subnormal)
	if err != nil {
		t.Fatal(err)
	}
	for _, ctx := range []Context{mustContext(t, 5, Exact), traps} {
		for _, in := range []string{"2", "1.5625E+101", "3E-7", strings.Repeat("3", 90)} {
			got, conditions, err := MustParse(in).SqrtWithContext(ctx)
			var ce *Error
			if !errors.As(err, &ce) || ce.Code != 0 || ce.Condition != Inexact || ce.Op != "SqrtWithContext" || !got.Equal(Decimal{}) || conditions != 0 {
				t.Fatalf("Exact √%s: %v %v %v", in, got, conditions, err)
			}
		}
	}
	got, conditions, err := MustParse("10000000000").SqrtWithContext(mustContext(t, 3, Exact))
	if err != nil || got.String() != "1.00E+5" || conditions != Rounded {
		t.Fatalf("Exact √1E+10: %v %v %v", got, conditions, err)
	}
	// The zero-only Rounded stays trappable.
	got, conditions, err = MustParse("10000000000").SqrtWithContext(traps.withPrecision(3))
	var ce *Error
	if !errors.As(err, &ce) || ce.Code != 0 || ce.Condition != Rounded || got.String() != "1.00E+5" || conditions != 0 {
		t.Fatalf("trapped zero-only Rounded: %v %v %v", got, conditions, err)
	}
}

// withPrecision is a test helper deriving a context at another precision.
func (c Context) withPrecision(p uint32) Context {
	c.precision = p
	return c
}

// TestSqrtGuards covers the range guards for Sqrt: a root below Emin is
// Subnormal (and Underflow when inexact) and rounds at Etiny, including an
// exact tie decided from truncated input digits (N − r² = r with δ = 1/4);
// a root above Emax overflows to the largest finite value; Exact refuses
// the overflow; traps select from the emitted set. Random guarded cases
// match the oracle in every mode.
func TestSqrtGuards(t *testing.T) {
	guards := &ExponentGuards{Emin: -3, Emax: 3}
	mk := func(mode RoundingMode, traps Conditions) Context {
		ctx, err := NewContext(3, mode, guards, traps)
		if err != nil {
			t.Fatal(err)
		}
		return ctx
	}
	for _, tc := range []struct {
		in         string
		mode       RoundingMode
		want       string
		conditions Conditions
	}{
		{"6.25E-10", TiesToEven, "0.00002", Subnormal | Underflow | Inexact | Rounded | Decreased},
		{"6.25E-10", TiesAwayFromZero, "0.00003", Subnormal | Underflow | Inexact | Rounded | Increased},
		{"6.25E-10", TiesTowardZero, "0.00002", Subnormal | Underflow | Inexact | Rounded | Decreased},
		{"6.26E-10", TiesToEven, "0.00003", Subnormal | Underflow | Inexact | Rounded | Increased},
		{"6.24E-10", TiesAwayFromZero, "0.00002", Subnormal | Underflow | Inexact | Rounded | Decreased},
		{"2.25E-8", TiesToEven, "0.00015", Subnormal},
		{"1E-100", TiesToEven, "0.00000", Subnormal | Underflow | Inexact | Rounded | Decreased},
		{"1E-100", AwayFromZero, "0.00001", Subnormal | Underflow | Inexact | Rounded | Increased},
		{"1E+8", TiesToEven, "9.99E+3", Overflow | Inexact | Rounded | Decreased},
		{"9.99E+7", TiesToEven, "9.99E+3", Inexact | Rounded | Decreased},
		{"9.9E+7", TiesToEven, "9.95E+3", Inexact | Rounded | Increased},
		{"99800100", TiesToEven, "9.99E+3", Rounded},
		{"99899999", TowardZero, "9.99E+3", Inexact | Rounded | Decreased},
		{"99899999", AwayFromZero, "9.99E+3", Overflow | Inexact | Rounded | Decreased},
		{"99980001", TiesToEven, "9.99E+3", Overflow | Inexact | Rounded | Decreased},
	} {
		got, conditions, err := MustParse(tc.in).SqrtWithContext(mk(tc.mode, 0))
		if err != nil || got.String() != tc.want || conditions != tc.conditions {
			t.Fatalf("√%s %v: %v %v %v, want %s %v", tc.in, tc.mode, got, conditions, err, tc.want, tc.conditions)
		}
	}
	if got, conditions, err := MustParse("1E+8").SqrtWithContext(mk(Exact, 0)); err == nil || conditions != 0 || !got.Equal(Decimal{}) {
		t.Fatalf("Exact overflow: %v %v %v", got, conditions, err)
	}
	got, conditions, err := MustParse("6.25E-10").SqrtWithContext(mk(TiesToEven, Underflow))
	var ce *Error
	if !errors.As(err, &ce) || ce.Code != 0 || ce.Condition != Underflow || got.String() != "0.00002" || conditions != Subnormal|Inexact|Rounded|Decreased {
		t.Fatalf("trapped Underflow: %v %v %v", got, conditions, err)
	}
	r := rand.New(rand.NewPCG(53, 6))
	subnormal, overflow := 0, 0
	for i := range 4000 {
		p := int64(1 + r.IntN(12))
		emin := int64(-r.IntN(20))
		emax := int64(r.IntN(20))
		g := sqrtGuards{on: true, emin: emin, emax: emax}
		ctxGuards := &ExponentGuards{Emin: int32(emin), Emax: int32(emax)}
		c := sqrtOperand(r, 30, p)
		e := int64(r.IntN(141) - 90)
		v := sqrtDecimal(c, e)
		for mode := TiesToEven; mode <= Exact; mode++ {
			ctx, err := NewContext(uint32(p), mode, ctxGuards, 0)
			if err != nil {
				t.Fatal(err)
			}
			got, conditions, err := v.SqrtWithContext(ctx)
			want := sqrtOracle(c, e, p, mode, g)
			sqrtCheck(t, fmt.Sprintf("guarded %d √%v p=%d [%d,%d] %v", i, v, p, emin, emax, mode), v, got, conditions, err, want)
			if mode == TiesToEven {
				subnormal += boolInt(want.conditions&Subnormal != 0)
				overflow += boolInt(want.conditions&Overflow != 0)
			}
		}
	}
	if subnormal < 200 || overflow < 200 {
		t.Fatalf("vacuous guard corpus: %d subnormal, %d overflow", subnormal, overflow)
	}
}

// TestSqrtKernelClass pins the exact class decision of sqrtDigits against
// big.Int.Sqrt, exhaustively for small N and on constructed truncations:
// with X = N + δ, N = r² + r and δ below, at and above 1/4, the class is
// below, half and above, and δ = 0 with N = r² is exact.
func TestSqrtKernelClass(t *testing.T) {
	var stack [sqrtStackLimbs]uint32
	run := func(c *big.Int, k int64) ([]uint32, divHalf) {
		d := sqrtDecimal(c, 0)
		v := coefficientViewOf(d)
		dx, _ := arithmeticDigits(&v)
		p := newSqrtPlan(dx, k)
		scratch := stack[:2]
		if p.s != 0 {
			var ok bool
			scratch, ok = sqrtScratch(&stack, newSqrtLayout(p.s, p.r), p.r)
			if !ok {
				t.Fatal("scratch refused")
			}
		}
		return sqrtDigits(&v, dx, p, scratch, nil)
	}
	oracle := func(x *big.Rat) (*big.Int, divHalf) {
		q := new(big.Int).Sqrt(new(big.Int).Quo(x.Num(), x.Denom()))
		if new(big.Rat).SetInt(new(big.Int).Mul(q, q)).Cmp(x) == 0 {
			return q, divExactClass
		}
		twice := new(big.Int).Add(new(big.Int).Lsh(q, 1), big.NewInt(1))
		switch new(big.Rat).Mul(x, big.NewRat(4, 1)).Cmp(new(big.Rat).SetInt(new(big.Int).Mul(twice, twice))) {
		case -1:
			return q, divBelow
		case 0:
			return q, divHalfClass
		}
		return q, divAbove
	}
	limit := int64(200000)
	if testing.Short() {
		limit = 20000
	}
	for n := int64(1); n <= limit; n++ {
		c := big.NewInt(n)
		for _, k := range []int64{0, 1, -1, -2} {
			r, class := run(c, k)
			q, want := oracle(sqrtScaled(c, k))
			if limbsString(r) != q.String() || class != want {
				t.Fatalf("√(%d·10^%d): %s %v, want %s %v", n, k, limbsString(r), class, q, want)
			}
		}
	}
	rng := rand.New(rand.NewPCG(53, 7))
	half := 0
	for range 3000 {
		root := randomDigits(rng, 1+rng.IntN(30))
		j := int64(1 + rng.IntN(12))
		n := new(big.Int).Add(new(big.Int).Mul(root, root), root)
		scale := new(big.Int).Exp(big.NewInt(10), big.NewInt(j), nil)
		quarter := new(big.Int).Quo(scale, big.NewInt(4))
		for _, tail := range []*big.Int{big.NewInt(0), new(big.Int).Sub(quarter, big.NewInt(1)), quarter, new(big.Int).Add(quarter, big.NewInt(1)), new(big.Int).Sub(scale, big.NewInt(1))} {
			if tail.Sign() < 0 {
				continue
			}
			c := new(big.Int).Add(new(big.Int).Mul(n, scale), tail)
			r, class := run(c, -j)
			q, want := oracle(sqrtScaled(c, -j))
			if limbsString(r) != q.String() || class != want {
				t.Fatalf("√(%s·10^-%d): %s %v, want %s %v", c, j, limbsString(r), class, q, want)
			}
			half += boolInt(want == divHalfClass)
		}
	}
	if half < 1000 {
		t.Fatalf("vacuous truncated-tie corpus: %d halves", half)
	}
}

// limbsString renders little-endian limbs in decimal ("0" when empty).
func limbsString(r []uint32) string {
	r = trimLimbs(r)
	if len(r) == 0 {
		return "0"
	}
	var b strings.Builder
	fmt.Fprintf(&b, "%d", r[len(r)-1])
	for i := len(r) - 2; i >= 0; i-- {
		fmt.Fprintf(&b, "%09d", r[i])
	}
	return b.String()
}

// TestSqrtLongCoefficients covers operands of hundreds of digits: bare
// roots of long squares, context roots at small precision whose input is
// truncated to 2(p+1) digits (the dropped digits decide exactness and
// ties), and context roots at precisions of hundreds of digits, all
// against the oracle.
func TestSqrtLongCoefficients(t *testing.T) {
	r := rand.New(rand.NewPCG(53, 8))
	count := 120
	if testing.Short() {
		count = 30
	}
	for i := range count {
		root := randomDigits(r, 100+r.IntN(300))
		c := new(big.Int).Mul(root, root)
		e := int64(2 * (r.IntN(41) - 20))
		v := sqrtDecimal(c, e)
		got, err := v.Sqrt()
		if err != nil || got.coefficientDigits() != root.String() || int64(got.exponent()) != e/2 {
			t.Fatalf("case %d: bare √ of a %d-digit square: %v", i, len(c.String()), err)
		}
		next := sqrtDecimal(new(big.Int).Add(c, big.NewInt(1)), e)
		if _, err := next.Sqrt(); !errors.Is(err, ErrInexact) {
			t.Fatalf("case %d: bare √(square+1): %v", i, err)
		}
		for _, p := range []int64{1, 2, 5, 16, 34, int64(len(root.String())) - 1, int64(len(root.String())), int64(len(root.String())) + 7, 300} {
			for _, x := range []*big.Int{c, new(big.Int).Add(c, big.NewInt(1)), new(big.Int).Sub(c, big.NewInt(1)), randomDigits(r, 200+r.IntN(400))} {
				mode := RoundingMode(r.IntN(8))
				v := sqrtDecimal(x, e)
				got, conditions, err := v.SqrtWithContext(mustContext(t, uint32(p), mode))
				sqrtCheck(t, fmt.Sprintf("long %d p=%d %v", i, p, mode), v, got, conditions, err, sqrtOracle(x, e, p, mode, sqrtGuards{}))
			}
		}
	}
	// A 600-digit tie: (10·root+5)² followed by zeros at p = digits(root)+1.
	root := randomDigits(r, 299)
	tie := new(big.Int).Add(new(big.Int).Mul(root, big.NewInt(10)), big.NewInt(5))
	c := new(big.Int).Mul(tie, tie)
	c.Mul(c, new(big.Int).Exp(big.NewInt(10), big.NewInt(40), nil))
	for mode := TiesToEven; mode <= Exact; mode++ {
		v := sqrtDecimal(c, 0)
		got, conditions, err := v.SqrtWithContext(mustContext(t, 299, mode))
		sqrtCheck(t, fmt.Sprintf("600-digit tie %v", mode), v, got, conditions, err, sqrtOracle(c, 0, 299, mode, sqrtGuards{}))
	}
}

// TestSqrtContextTargetDigits pins the root scaling, the premise of
// the context tariff: unguarded, the root is taken at the exponent t′
// where ⌊√v/10^t′⌋ has exactly p+1 digits (a base-100 pair of the scaled
// coefficient per result digit, so N has 2p+1 or 2p+2 digits), checked
// with big.Int.Sqrt; under guards t′ is raised to Etiny and no further.
func TestSqrtContextTargetDigits(t *testing.T) {
	r := rand.New(rand.NewPCG(53, 11))
	raised := 0
	for range 3000 {
		p := int64(1 + r.IntN(60))
		c := randomDigits(r, 1+r.IntN(90))
		e := int64(r.IntN(401) - 200)
		v := sqrtDecimal(c, e)
		ctx := mustContext(t, uint32(p), TiesToEven)
		tPrime, _ := sqrtContextTarget(v.CoefficientDigits(), v.exponent(), &ctx)
		x := sqrtScaled(c, e-2*tPrime)
		q := new(big.Int).Sqrt(new(big.Int).Quo(x.Num(), x.Denom()))
		if int64(len(q.String())) != p+1 {
			t.Fatalf("√%v p=%d: t′ = %d leaves %d root digits", v, p, tPrime, len(q.String()))
		}
		emin := int64(r.IntN(200) - 150)
		guarded, err := NewContext(uint32(p), TiesToEven, &ExponentGuards{Emin: int32(emin), Emax: 400}, 0)
		if err != nil {
			t.Fatal(err)
		}
		gPrime, etiny := sqrtContextTarget(v.CoefficientDigits(), v.exponent(), &guarded)
		if etiny != emin-p+1 || gPrime != max(tPrime, etiny) {
			t.Fatalf("√%v p=%d Emin=%d: guarded t′ = %d, want max(%d, %d)", v, p, emin, gPrime, tPrime, emin-p+1)
		}
		raised += boolInt(gPrime > tPrime)
	}
	if raised < 300 {
		t.Fatalf("vacuous guard corpus: %d raised targets", raised)
	}
}

// TestSqrtDeepStickyDigits pins the sticky read of dropped input digits:
// when the kept part N of the scaled operand is an
// exact square, or an exact tie at p digits, and the only nonzero dropped
// digit lies three or more places down ("00…0x"), the root is Inexact,
// Exact refuses it, and a tie is broken upward in every tie mode.
// √4000001 at p = 1 is 2E+3 with Inexact, not a zero-only Rounded.
func TestSqrtDeepStickyDigits(t *testing.T) {
	got, conditions, err := MustParse("4000001").SqrtWithContext(mustContext(t, 1, TiesToEven))
	if err != nil || got.String() != "2E+3" || conditions != Inexact|Rounded|Decreased {
		t.Fatalf("√4000001 p=1: %v %v %v", got, conditions, err)
	}
	if _, _, err := MustParse("4000001").SqrtWithContext(mustContext(t, 1, Exact)); !errors.Is(err, ErrInexact) {
		t.Fatalf("Exact √4000001 p=1: %v", err)
	}
	r := rand.New(rand.NewPCG(53, 12))
	for i := range 400 {
		p := int64(1 + r.IntN(30))
		root := randomDigits(r, int(p))
		tie := i%2 == 0
		if tie {
			root.Mul(root, big.NewInt(10)).Add(root, big.NewInt(5))
		}
		// The square, then an odd count of 3 to 39 zeros and a final
		// nonzero digit: an even shift keeps the square a square.
		zeros := int64(3 + 2*r.IntN(19))
		c := new(big.Int).Mul(root, root)
		c.Mul(c, new(big.Int).Exp(big.NewInt(10), big.NewInt(zeros+1), nil))
		c.Add(c, big.NewInt(int64(1+r.IntN(9))))
		e := int64(r.IntN(21)-10) * 2
		v := sqrtDecimal(c, e)
		for mode := TiesToEven; mode <= Exact; mode++ {
			got, conditions, err := v.SqrtWithContext(mustContext(t, uint32(p), mode))
			want := sqrtOracle(c, e, p, mode, sqrtGuards{})
			sqrtCheck(t, fmt.Sprintf("deep %d √%v p=%d %v", i, v, p, mode), v, got, conditions, err, want)
			if mode == Exact {
				if !want.refused {
					t.Fatalf("deep %d: the oracle accepts an inexact root under Exact", i)
				}
				continue
			}
			if conditions&Inexact == 0 {
				t.Fatalf("deep %d √%v p=%d %v: %v lacks Inexact", i, v, p, mode, conditions)
			}
			if tie && (mode == TiesToEven || mode == TiesTowardZero || mode == TiesAwayFromZero) && conditions&Increased == 0 {
				t.Fatalf("deep %d √%v p=%d %v: tie not broken upward (%v)", i, v, p, mode, conditions)
			}
		}
	}
}

// sqrtClosedIterations is max(1, ⌈log2(R/15)⌉) + 3, from floating log2.
func sqrtClosedIterations(r uint64) uint64 {
	j := math.Ceil(math.Log2(float64(r) / 15))
	return uint64(max(1, j)) + 3
}

// sqrtClosedCharge is the Sqrt precharge d + I·D(2R, R) + t(R)² in
// closed form, with the Div family's charge D(2m, m) = 2(t(2m)−t(m)+1)(t(m)+1)
// + 2(t(2m)+t(m)+1) + 3m + t(m).
func sqrtClosedCharge(d, r uint64) uint64 {
	tf := func(n uint64) uint64 { return 1 + (n-1)/9 }
	tn, n := tf(2*r), tf(r)
	div := 2*(tn-n+1)*(n+1) + 2*(tn+n+1) + 3*r + n
	return d + sqrtClosedIterations(r)*div + n*n
}

// TestSqrtBudget covers the budget of Sqrt: the smallest admitting work cap
// of an exact bare root is d′ + I·D + t(R)² and its smallest digit cap is
// R = ⌈d′/2⌉; a context root charges B + 2N + 1 with B at R = p + 1 and
// N the result's digits; a zero costs one digit and one unit bare, four
// under a context; and refusals below either cap allocate nothing, even
// where the scratch would be on the heap.
func TestSqrtBudget(t *testing.T) {
	smallest := func(hi uint64, run func(Budget) error, digits bool) uint64 {
		return smallestAdmitting(hi, func(n uint64) bool {
			if digits {
				return run(Budget{MaxDigits: n}) == nil
			}
			return run(Budget{MaxWork: n}) == nil
		})
	}
	r := rand.New(rand.NewPCG(53, 9))
	for _, rootDigits := range []int{1, 2, 8, 9, 10, 15, 16, 17, 18, 19, 29, 30, 31, 60, 81, 120, 400} {
		root := randomDigits(r, rootDigits)
		for _, odd := range []bool{false, true} {
			c := new(big.Int).Mul(root, root)
			e := int64(-6)
			if odd {
				// √(C·10^−7) with 10·C = root²·100 exact: C = root²·10.
				c.Mul(c, big.NewInt(10))
				e = -7
			}
			v := sqrtDecimal(c, e)
			d := uint64(len(c.String()))
			if odd {
				d++
			}
			rd := (d + 1) / 2
			run := func(b Budget) error { _, _, err := v.SqrtWithContext(Context{}.WithBudget(b)); return err }
			want := sqrtClosedCharge(d, rd)
			if err := run(Budget{MaxWork: want, MaxDigits: rd}); err != nil {
				t.Fatalf("√%v: refused at its tariff: %v", v, err)
			}
			if w := smallest(want, run, false); w != want {
				t.Fatalf("√ of %d digits: smallest work %d, want %d", d, w, want)
			}
			if n := smallest(rd, run, true); n != rd {
				t.Fatalf("√ of %d digits: smallest digits %d, want %d", d, n, rd)
			}
			for _, b := range []Budget{{MaxWork: want - 1}, {MaxDigits: rd - 1}} {
				if b == (Budget{}) {
					continue
				}
				if n := testing.AllocsPerRun(5, func() { _ = run(b) }); n != 1 {
					// The refusal allocates only its *Error.
					t.Fatalf("√ of %d digits refused under %+v with %v allocations", d, b, n)
				}
				if err := run(b); !errors.Is(err, ErrInsufficientStorage) {
					t.Fatalf("√ of %d digits under %+v: %v", d, b, err)
				}
			}
		}
	}
	for _, p := range []uint32{1, 3, 16, 34, 81, 200, 500} {
		for _, in := range []string{"2", "1E+10", "4", strings.Repeat("7", 700), "0.000123"} {
			v := MustParse(in)
			ctx := mustContext(t, p, TiesToEven)
			got, _, err := v.SqrtWithContext(ctx)
			if err != nil {
				t.Fatal(err)
			}
			d := v.CoefficientDigits()
			base := sqrtClosedCharge(d, uint64(p)+1)
			want := base + 2*got.CoefficientDigits() + 1
			run := func(b Budget) error { _, _, err := v.SqrtWithContext(ctx.WithBudget(b)); return err }
			if w := smallest(want, run, false); w != want {
				t.Fatalf("√%s p=%d: smallest work %d, want %d", in, p, w, want)
			}
			if n := smallest(uint64(p), run, true); n != got.CoefficientDigits() {
				t.Fatalf("√%s p=%d: smallest digits %d, want %d", in, p, n, got.CoefficientDigits())
			}
			if n := testing.AllocsPerRun(5, func() { _ = run(Budget{MaxWork: base - 1}) }); n != 1 {
				t.Fatalf("√%s p=%d: precharge refusal made %v allocations", in, p, n)
			}
		}
	}
	for _, tc := range []struct {
		name string
		run  func(Budget) error
		work uint64
	}{
		{"bare", func(b Budget) error {
			_, _, err := MustParse("0E-7").SqrtWithContext(Context{}.WithBudget(b))
			return err
		}, 1},
		{"context", func(b Budget) error {
			_, _, err := MustParse("0E-7").SqrtWithContext(Decimal64Context().WithBudget(b))
			return err
		}, 4},
	} {
		if w := smallest(100, tc.run, false); w != tc.work {
			t.Fatalf("zero %s: work %d, want %d", tc.name, w, tc.work)
		}
		if n := smallest(100, tc.run, true); n != 1 {
			t.Fatalf("zero %s: digits %d", tc.name, n)
		}
	}
}

// TestSqrtCountedWorkWithinTariff checks the counted loop against the tariff:
// over a size sweep of exact and inexact roots, bare and in context
// (including every root length near the Newton plan's thresholds R ≈
// 15·2^j), the kernel's counted work never exceeds the precharge B and
// its Newton iterations never exceed the planned max(1, ⌈log2(R/15)⌉)+3.
func TestSqrtCountedWorkWithinTariff(t *testing.T) {
	r := rand.New(rand.NewPCG(53, 10))
	sizes := []int{1, 2, 3, 9, 10, 14, 15, 16, 17, 18, 28, 29, 30, 31, 58, 59, 60, 61, 118, 119, 120, 121, 238, 239, 240, 241, 400}
	checks := 0
	for _, rootDigits := range sizes {
		for range 12 {
			var c *big.Int
			switch r.IntN(4) {
			case 0:
				root := randomDigits(r, rootDigits)
				c = new(big.Int).Mul(root, root)
			case 1: // 10^(2R) − 1, whose root is all nines
				c = new(big.Int).Sub(new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(2*rootDigits)), nil), big.NewInt(1))
			case 2: // 10^(2R−2), whose root is a power of ten
				c = new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(2*rootDigits-2)), nil)
			default:
				c = randomDigits(r, 2*rootDigits-r.IntN(2))
			}
			v := sqrtDecimal(c, int64(r.IntN(9)-4))
			var count sqrtCount
			if _, _, err := v.sqrtUnlimited(limits{}, "Sqrt", &count); err != nil && !errors.Is(err, ErrInexact) {
				t.Fatal(err)
			}
			vw := coefficientViewOf(v)
			d, _ := arithmeticDigits(&vw)
			if v.exponent()%2 != 0 {
				d++
			}
			rd := (d + 1) / 2
			charge, _ := sqrtCharge(d, rd)
			if count.work.units > charge || count.iterations > sqrtIterations(rd) {
				t.Fatalf("bare √ of %d digits: work %d > %d or iterations %d > %d", d, count.work.units, charge, count.iterations, sqrtIterations(rd))
			}
			p := uint32(max(1, rootDigits-1))
			count = sqrtCount{}
			if _, _, err := v.sqrtContext(mustContext(t, p, TiesToEven), limits{}, "SqrtWithContext", &count); err != nil {
				t.Fatal(err)
			}
			charge, _ = sqrtCharge(v.CoefficientDigits(), uint64(p)+1)
			if count.work.units > charge || count.iterations > sqrtIterations(uint64(p)+1) {
				t.Fatalf("context √ p=%d: work %d > %d or iterations %d > %d", p, count.work.units, charge, count.iterations, sqrtIterations(uint64(p)+1))
			}
			checks++
		}
	}
	if checks < len(sizes)*12 {
		t.Fatal("vacuous sweep")
	}
	// Every root length: random, all-nines and square-minus-one inputs.
	top := 400
	if testing.Short() {
		top = 100
	}
	tight := 0
	for rootDigits := 1; rootDigits <= top; rootDigits++ {
		root := randomDigits(r, rootDigits)
		square := new(big.Int).Mul(root, root)
		for _, c := range []*big.Int{
			randomDigits(r, 2*rootDigits), randomDigits(r, 2*rootDigits-1),
			new(big.Int).Sub(new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(2*rootDigits)), nil), big.NewInt(1)),
			square.Sub(square, big.NewInt(1)),
		} {
			if c.Sign() == 0 {
				continue
			}
			v := sqrtDecimal(c, 0)
			var count sqrtCount
			_, _, _ = v.sqrtUnlimited(limits{}, "Sqrt", &count)
			d := uint64(len(c.String()))
			rd := (d + 1) / 2
			charge, _ := sqrtCharge(d, rd)
			if count.work.units > charge || count.iterations > sqrtIterations(rd) {
				t.Fatalf("√ of %d digits: work %d > %d or iterations %d > %d", d, count.work.units, charge, count.iterations, sqrtIterations(rd))
			}
			tight += boolInt(count.iterations == sqrtIterations(rd))
		}
	}
	if tight == 0 {
		t.Fatal("no root reached the planned iteration count; the bound is untested at its edge")
	}
	for r := uint64(1); r <= 2000; r++ {
		if sqrtIterations(r) != sqrtClosedIterations(r) {
			t.Fatalf("sqrtIterations(%d) = %d, closed form %d", r, sqrtIterations(r), sqrtClosedIterations(r))
		}
		if got, _ := sqrtCharge(3*r, r); got != sqrtClosedCharge(3*r, r) {
			t.Fatalf("sqrtCharge(%d) = %d, closed form %d", r, got, sqrtClosedCharge(3*r, r))
		}
	}
}

// TestSqrtWorkIndependentOfExponent checks that the counted work,
// the Newton iterations and the smallest admitting work cap of a context
// root do not depend on the operand's exponent, from 0 to ±2·10⁹.
func TestSqrtWorkIndependentOfExponent(t *testing.T) {
	ctx := mustContext(t, 34, TiesToEven)
	for _, coefficient := range []string{"2", "123456789012345678901234567890", strings.Repeat("4", 500)} {
		var first sqrtCount
		var firstCap uint64
		for i, e := range []int32{0, 2, -2, 1000, -1000, 200000000, -200000000, 2000000000, -2000000000} {
			v := MustParse(coefficient + "E" + fmt.Sprint(e))
			var count sqrtCount
			if _, _, err := v.sqrtContext(ctx, limits{}, "SqrtWithContext", &count); err != nil {
				t.Fatal(err)
			}
			run := func(w uint64) bool {
				_, _, err := v.SqrtWithContext(ctx.WithBudget(Budget{MaxWork: w}))
				return err == nil
			}
			limit := smallestAdmitting(1<<40, run)
			if i == 0 {
				first, firstCap = count, limit
				continue
			}
			if count != first || limit != firstCap {
				t.Fatalf("√%sE%d: work %+v cap %d, at exponent 0 %+v %d", coefficient, e, count, limit, first, firstCap)
			}
		}
	}
}

// TestSqrtAllocations covers the allocation class of Sqrt: an
// inline result allocates nothing, and a result of at most 81 digits
// allocates only its published holder, bare and in context.
func TestSqrtAllocations(t *testing.T) {
	root81 := strings.Repeat("123456789", 9)
	square81 := new(big.Int)
	square81.SetString(root81, 10)
	square81.Mul(square81, square81)
	long := MustParse(square81.String())
	two, square := MustParse("2"), MustParse("1522756")
	nines, _ := new(big.Int).SetString(strings.Repeat("9", 38), 10)
	long38 := MustParse(new(big.Int).Mul(nines, nines).String())
	for _, tc := range []struct {
		name  string
		run   func()
		allow float64
	}{
		{"bare inline", func() { _, _ = square.Sqrt() }, 0},
		{"bare 38 digits", func() { _, _ = long38.Sqrt() }, 0},
		{"context inline", func() { _, _, _ = two.SqrtWithContext(Decimal128Context()) }, 0},
		{"context 38 digits", func() { _, _, _ = two.SqrtWithContext(mustContext(t, 38, TiesToEven)) }, 0},
		{"context 81 digits", func() { _, _, _ = two.SqrtWithContext(mustContext(t, 81, TiesToEven)) }, 1},
		{"context 81 of a long operand", func() { _, _, _ = long.SqrtWithContext(mustContext(t, 81, AwayFromZero)) }, 1},
		{"bare 81 digits", func() { _, _ = long.Sqrt() }, 1},
	} {
		if n := testing.AllocsPerRun(50, tc.run); n != tc.allow {
			t.Fatalf("%s: %v allocations, want %v", tc.name, n, tc.allow)
		}
	}
	if got, err := long.Sqrt(); err != nil || got.coefficientDigits() != root81 {
		t.Fatalf("bare 81-digit root: %v %v", got, err)
	}
}

// TestSqrtNewtonLevelsMatchBigInt pins the leveled Newton iteration to
// math/big over operand lengths on both sides of every level threshold:
// random operands, all nines, perfect squares and their neighbors (whose
// roots sit just below an integer, the case that needs a third step).
func TestSqrtNewtonLevelsMatchBigInt(t *testing.T) {
	rng := rand.New(rand.NewPCG(0x5152, 8))
	base := big.NewInt(int64(decimalLimbBase))
	one := big.NewInt(1)
	lengths := []int{1, 2, 3, 13, 14, 15, 16, 17, 18, 27, 28, 29, 30, 31, 32, 33, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 127, 128, 129, 130, 255, 256, 257, 700}
	var leveled, plain int
	for _, length := range lengths {
		for sample := range 30 {
			n := new(big.Int)
			pow := new(big.Int).Exp(base, big.NewInt(int64(length)), nil)
			floor := new(big.Int).Exp(base, big.NewInt(int64(length-1)), nil)
			switch sample % 6 {
			case 0:
				n.Sub(pow, one) // all nines
			case 1:
				n.Set(floor) // the smallest operand of this length
			case 2, 3, 4:
				// r², r²−1 and r²+1 for a random root of this length's half.
				root := randomDigits(rng, (9*length+1)/2)
				n.Mul(root, root)
				n.Add(n, big.NewInt(int64(sample%6-3)))
			default:
				n = randomDigits(rng, 9*length-rng.IntN(9))
			}
			if n.Cmp(pow) >= 0 {
				n.Sub(pow, one)
			}
			if n.Cmp(floor) < 0 {
				n.Add(n, floor)
			}
			limbs := bigToLimbs(n)
			if len(limbs) != length {
				t.Fatalf("operand of %d limbs, want %d", len(limbs), length)
			}
			digits := limbsDigits(limbs)
			rootDigits := (digits + 1) / 2
			l := newSqrtLayout(digits, rootDigits)
			operand := make([]uint32, l.n)
			copy(operand, limbs)
			var count sqrtCount
			got := sqrtNewton(operand[:length], rootDigits, make([]uint32, l.u), make([]uint32, l.w), make([]uint32, l.w), &count)
			want := bigToLimbs(new(big.Int).Sqrt(n))
			if !slices.Equal(got, want) {
				t.Fatalf("√ of %d limbs (sample %d): got %v, math/big %v", length, sample, got, want)
			}
			if !slices.Equal(operand[:length], limbs) {
				t.Fatal("sqrtNewton changed its operand")
			}
			if (length+1)/2 >= sqrtLevelLimbs {
				leveled++
			} else {
				plain++
			}
			if count.levelSteps > 3 || (count.levelSteps == 0) != ((length+1)/2 < sqrtLevelLimbs) {
				t.Fatalf("√ of %d limbs (sample %d): a seeded level took %d steps", length, sample, count.levelSteps)
			}
		}
	}
	if leveled < 300 || plain < 100 {
		t.Fatalf("vacuous path coverage: leveled %d, plain %d", leveled, plain)
	}
}

// TestSqrtLevelEndsWithinThreeSteps checks the bound the leveled iteration
// rests on: from x₀ = (s+1)·B^m with s the root of the operand's top part
// and 2m at most the root's limbs less two, Newton's iteration reaches the
// root and confirms it in at most three steps.
func TestSqrtLevelEndsWithinThreeSteps(t *testing.T) {
	rng := rand.New(rand.NewPCG(0x5152, 9))
	base := big.NewInt(int64(decimalLimbBase))
	one := big.NewInt(1)
	three := 0
	for _, length := range []int{15, 16, 17, 18, 31, 32, 33, 64, 65, 200} {
		for sample := range 200 {
			pow := new(big.Int).Exp(base, big.NewInt(int64(length)), nil)
			floor := new(big.Int).Exp(base, big.NewInt(int64(length-1)), nil)
			n := new(big.Int)
			switch sample % 4 {
			case 0, 1:
				// (r+1)²−1: the root's fraction is as close to one as it gets.
				root := randomDigits(rng, (9*length+1)/2)
				n.Mul(root, root).Sub(n, one)
			case 2:
				n.Sub(pow, one)
			default:
				n = randomDigits(rng, 9*length-rng.IntN(9))
			}
			if n.Cmp(pow) >= 0 {
				n.Sub(pow, one)
			}
			if n.Cmp(floor) < 0 {
				n.Add(n, floor)
			}
			limbs := bigToLimbs(n)
			m := ((len(limbs)+1)/2 - 2) / 2
			shift := new(big.Int).Exp(base, big.NewInt(int64(m)), nil)
			seed := new(big.Int).Quo(n, new(big.Int).Mul(shift, shift))
			seed.Sqrt(seed).Add(seed, one).Mul(seed, shift)
			digits := limbsDigits(limbs)
			l := newSqrtLayout(digits, (digits+1)/2)
			xb := make([]uint32, l.w)
			x := xb[:copy(xb, bigToLimbs(seed))]
			got, _, _, steps := sqrtDescend(limbs, x, make([]uint32, l.u), xb, make([]uint32, l.w), nil)
			if want := bigToLimbs(new(big.Int).Sqrt(n)); !slices.Equal(got, want) || steps > 3 {
				t.Fatalf("%d limbs sample %d: %d steps, root %v, math/big %v", length, sample, steps, got, want)
			}
			three += boolInt(steps == 3)
		}
	}
	if three == 0 {
		t.Fatal("no operand needed the third step; the bound is untested at its edge")
	}
}
