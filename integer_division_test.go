// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"errors"
	"fmt"
	"math"
	"math/big"
	"math/bits"
	"math/rand/v2"
	"slices"
	"strings"
	"sync"
	"testing"
)

// quoRemParts returns a result's signed coefficient and exponent from its
// limbs, independently of the arithmetic under test.
func quoRemParts(d Decimal) (*big.Int, int32) {
	v := coefficientViewOf(d)
	limbs := make([]uint32, v.count)
	for i := range limbs {
		limbs[i] = v.limb(i)
	}
	c := bigFromLimbs(limbs)
	if d.negative() {
		c.Neg(c)
	}
	return c, d.Exponent()
}

// quoRemOracle is the math/big integer-division oracle over signed coefficients:
// q = trunc(x/y), r = x − q·y and rn = x − n·y for nearest-even n, with
// both remainders at m = min(ex, ey) and q at exponent 0.
type quoRemOracle struct {
	q, r, rn *big.Int
	m        int32
	qDigits  uint64
}

func newQuoRemOracle(cx *big.Int, ex int32, cy *big.Int, ey int32) quoRemOracle {
	m := min(ex, ey)
	x := new(big.Int).Mul(cx, pow10Big(int64(ex)-int64(m)))
	y := new(big.Int).Mul(cy, pow10Big(int64(ey)-int64(m)))
	q, r := new(big.Int).QuoRem(x, y, new(big.Int))
	n := new(big.Int).Set(q)
	twice := new(big.Int).Lsh(new(big.Int).Abs(r), 1)
	if c := twice.CmpAbs(y); c > 0 || c == 0 && q.Bit(0) == 1 {
		if x.Sign()*y.Sign() > 0 {
			n.Add(n, big.NewInt(1))
		} else {
			n.Sub(n, big.NewInt(1))
		}
	}
	rn := new(big.Int).Sub(x, new(big.Int).Mul(n, y))
	digits := uint64(1)
	if q.Sign() != 0 {
		digits = uint64(len(new(big.Int).Abs(q).String()))
	}
	return quoRemOracle{q: q, r: r, rn: rn, m: m, qDigits: digits}
}

func pow10Big(n int64) *big.Int { return new(big.Int).Exp(big.NewInt(10), big.NewInt(n), nil) }

func (o quoRemOracle) want(op intDivOp) (*big.Int, int32) {
	switch op {
	case intDivQuo:
		return o.q, 0
	case intDivRem:
		return o.r, o.m
	}
	return o.rn, o.m
}

func quoRemOracleOf(x, y Decimal) quoRemOracle {
	cx, ex := quoRemParts(x)
	cy, ey := quoRemParts(y)
	return newQuoRemOracle(cx, ex, cy, ey)
}

var quoRemOps = []intDivOp{intDivQuo, intDivRem, intDivRemNear}

func (op intDivOp) String() string { return [...]string{"Quo", "Rem", "RemNear"}[op] }

func (p intDivPath) String() string {
	return [...]string{"zero-dividend", "q-zero", "q-zero-near", "quotient", "split", "stream", "modular"}[p]
}

// quoRemPublic runs an operation through its public budget twin.
func quoRemPublic(x, y Decimal, op intDivOp, budget Budget) (Decimal, error) {
	switch op {
	case intDivQuo:
		res, _, resErr := x.QuoWithContext(y, Context{}.WithBudget(budget))
		return res, resErr
	case intDivRem:
		res, _, resErr := x.RemWithContext(y, Context{}.WithBudget(budget))
		return res, resErr
	}
	res, _, resErr := x.RemNearWithContext(y, Context{}.WithBudget(budget))
	return res, resErr
}

func quoRemContext(x, y Decimal, op intDivOp, ctx Context, budget Budget) (Decimal, Conditions, error) {
	switch op {
	case intDivQuo:
		return x.QuoWithContext(y, ctx.WithBudget(budget))
	case intDivRem:
		return x.RemWithContext(y, ctx.WithBudget(budget))
	}
	return x.RemNearWithContext(y, ctx.WithBudget(budget))
}

// quoRemDigits draws a coefficient string with patterns that reach every
// path's corners: random digits, all nines, sparse ones, powers of ten and
// runs of nines over zeros (the split's complement scan).
func quoRemDigits(rng *rand.Rand, n int) string {
	b := make([]byte, n)
	switch rng.IntN(8) {
	case 0:
		for i := range b {
			b[i] = '9'
		}
	case 1:
		for i := range b {
			b[i] = '0'
		}
		b[0], b[n-1] = '1', '1'
	case 2:
		for i := range b {
			b[i] = '0'
		}
		b[0] = '1'
	case 3:
		cut := rng.IntN(n)
		for i := range b {
			switch {
			case i <= cut:
				b[i] = '9'
			case rng.IntN(3) == 0:
				b[i] = byte('0' + rng.IntN(10))
			default:
				b[i] = '0'
			}
		}
	default:
		for i := range b {
			b[i] = byte('0' + rng.IntN(10))
		}
		b[0] = byte('1' + rng.IntN(9))
	}
	return string(b)
}

func quoRemOperand(rng *rand.Rand, digits int, exponent int32) Decimal {
	sign := ""
	if rng.IntN(2) == 0 {
		sign = "-"
	}
	return MustParse(fmt.Sprintf("%s%sE%d", sign, quoRemDigits(rng, digits), exponent))
}

// quoRemPair draws operands whose exponent gap and δ span the paths: small
// gaps, limb-boundary gaps, gaps past the stream/modular crossover, and δ
// placed at −2..2.
func quoRemPair(rng *rand.Rand) (Decimal, Decimal) {
	dxMax, dyMax := 40, 30
	if rng.IntN(10) == 0 {
		dxMax, dyMax = 400, 200
	}
	dx, dy := 1+rng.IntN(dxMax), 1+rng.IntN(dyMax)
	ex := int32(rng.IntN(61) - 30)
	var k int64
	switch rng.IntN(6) {
	case 0:
		k = int64(rng.IntN(51) - 25)
	case 1:
		k = []int64{-27, -19, -18, -17, -10, -9, -8, 8, 9, 10, 17, 18, 19, 27}[rng.IntN(14)]
	case 2:
		k = int64(rng.IntN(801) - 400)
	case 3:
		k = int64(1000 + rng.IntN(3000))
	default:
		delta := int64(rng.IntN(5) - 2)
		k = delta + int64(dy) - int64(dx) // δ = dx − dy + k
	}
	ey := int32(int64(ex) - k)
	return quoRemOperand(rng, dx, ex), quoRemOperand(rng, dy, ey)
}

// countedQuoRem runs the private kernel with the test seam.
func countedQuoRem(x, y Decimal, op intDivOp, ctx Context, budget Budget, force intDivForce) (Decimal, Conditions, error, quoRemCount) {
	c := quoRemCount{force: force}
	d, cond, err := x.intDivide(y, op, ctx, budget.arith(), "counted", &c)
	return d, cond, err, c
}

func checkQuoRem(t *testing.T, label string, got Decimal, err error, want *big.Int, exponent int32) {
	t.Helper()
	if err != nil {
		t.Fatalf("%s: unexpected error %v", label, err)
	}
	c, e := quoRemParts(got)
	if c.Cmp(want) != 0 || e != exponent {
		t.Fatalf("%s: got %v (coefficient %v, exponent %d), want coefficient %v at exponent %d", label, got, c, e, want, exponent)
	}
	if want.Sign() == 0 && got.negative() {
		t.Fatalf("%s: zero result is signed", label)
	}
}

// TestQuoRemIdentity covers the quotient and remainder identity against
// the math/big oracle: over random operands spanning every path (both
// gap directions, the 9- and 18-digit limb boundaries, δ at −2..2 and gaps
// past the stream/modular crossover), Quo equals math/big's truncated
// quotient at exponent 0, Rem equals x − q·y and RemNear x − n·y for
// nearest-even n, both at min(ex, ey) with the dividend's sign or unsigned
// zero, through the bare, budget, unlimited-context and counted forms. A
// guard requires every path to run.
func TestQuoRemIdentity(t *testing.T) {
	rng := rand.New(rand.NewPCG(20260928, 59))
	paths := map[string]int{}
	cases := 6000
	if testing.Short() {
		cases = 1500
	}
	for i := range cases {
		x, y := quoRemPair(rng)
		if i%97 == 0 {
			x = MustParse(fmt.Sprintf("0E%d", rng.IntN(41)-20))
		}
		o := quoRemOracleOf(x, y)
		for _, op := range quoRemOps {
			want, exponent := o.want(op)
			label := fmt.Sprintf("%v %s %v", x, op, y)
			got, _, err, c := countedQuoRem(x, y, op, Context{}, Budget{}, intDivForceNone)
			checkQuoRem(t, label+" (counted)", got, err, want, exponent)
			paths[fmt.Sprintf("%s/%s", op, c.taken)]++
			bare, err := quoRemPublic(x, y, op, Budget{})
			checkQuoRem(t, label, bare, err, want, exponent)
			ctxResult, cond, err := quoRemContext(x, y, op, Context{}, Budget{})
			checkQuoRem(t, label+" (Context{})", ctxResult, err, want, exponent)
			if cond != 0 {
				t.Fatalf("%s: Context{} returned conditions %v", label, cond)
			}
		}
	}
	for _, want := range []string{
		"Quo/zero-dividend", "Quo/q-zero", "Quo/quotient",
		"Rem/zero-dividend", "Rem/q-zero", "Rem/split", "Rem/stream", "Rem/modular",
		"RemNear/q-zero", "RemNear/q-zero-near", "RemNear/split", "RemNear/stream", "RemNear/modular",
	} {
		if paths[want] < 10 {
			t.Errorf("path %s ran %d times: %v", want, paths[want], paths)
		}
	}
}

// TestQuoRemMatchesGDAVectors covers a directed table and the GDA
// v1.70 examples for divide-integer, remainder and remainder-near
// (speleotrove.com/decimal/daops.html, hand-copied), plus libmpdec
// rows: Rem and RemNear at exponent min(ex, ey), Quo at 0.
func TestQuoRemMatchesGDAVectors(t *testing.T) {
	for _, v := range []struct{ x, y, quo, rem, near string }{
		// GDA v1.70 examples.
		{"2", "3", "0", "2", "-1"},
		{"10", "3", "3", "1", "1"},
		{"1", "0.3", "3", "0.1", "0.1"},
		{"2.1", "3", "0", "2.1", "-0.9"},
		{"-10", "3", "-3", "-1", "-1"},
		{"10.2", "1", "10", "0.2", "0.2"},
		{"10", "0.3", "33", "0.1", "0.1"},
		{"3.6", "1.3", "2", "1.0", "-0.3"},
		{"10", "6", "1", "4", "-2"},
		{"10", "4", "2", "2", "2"},
		{"10", "5", "2", "0", "0"},
		// libmpdec 2.5.1.
		{"10.5", "3", "3", "1.5", "-1.5"},
		{"10", "3.00", "3", "1.00", "1.00"},
		{"2.400", "2.0", "1", "0.400", "0.400"},
		{"-7", "2", "-3", "-1", "1"},
		{"7", "-2", "-3", "1", "-1"},
		{"3", "2", "1", "1", "-1"},
		{"5", "2", "2", "1", "1"},
		{"-3", "2", "-1", "-1", "1"},
		{"10.0", "2.0", "5", "0.0", "0.0"},
		{"0.000", "1E+2", "0", "0.000", "0.000"},
		{"1E+3", "7", "142", "6", "-1"},
		{"9.9", "1", "9", "0.9", "-0.1"},
		{"1E-40", "1E+40", "0", "1E-40", "1E-40"},
		{"12345E-2", "7E+1", "1", "53.45", "-16.55"},
		{"1E+40", "1E-40", "1" + strings.Repeat("0", 80), "0E-40", "0E-40"},
		{"99", "100", "0", "99", "-1"},
		{"3", "0.29", "10", "0.10", "0.10"},
		{"1000", "0.1", "10000", "0.0", "0.0"},
		// Directed table.
		{"9.9", "10", "0", "9.9", "-0.1"},
		{"10.0", "2.0", "5", "0.0", "0.0"},
	} {
		x, y := MustParse(v.x), MustParse(v.y)
		for _, c := range []struct {
			op   intDivOp
			want string
		}{{intDivQuo, v.quo}, {intDivRem, v.rem}, {intDivRemNear, v.near}} {
			got, err := quoRemPublic(x, y, c.op, Budget{})
			want := MustParse(c.want)
			if err != nil || !got.Equal(want) || got.Exponent() != want.Exponent() || got.IsZero() && got.negative() {
				t.Errorf("%s %s %s = (%v, %v), want %s", v.x, c.op, v.y, got, err, c.want)
			}
		}
	}
}

// TestQuoRemFinitePrecisionRefuses checks that finite precision fails
// rather than rounds: under precision p, each operation
// reports ErrDivisionImpossible without a result iff the truncated
// quotient has more than p digits (math/big), including zero remainders
// (10 Rem 1 at p = 1), and otherwise returns the unlimited result,
// unrounded even when the remainder has more than p digits, with no
// conditions; RemNear has no extra failure when n has p+1 digits (9.9
// RemNear 1 at p = 1).
func TestQuoRemFinitePrecisionRefuses(t *testing.T) {
	rng := rand.New(rand.NewPCG(20260928, 60))
	refused, admitted := 0, 0
	for range 3000 {
		x, y := quoRemPair(rng)
		if x.CoefficientDigits() > 60 || y.CoefficientDigits() > 60 || x.Exponent()-y.Exponent() > 200 {
			continue
		}
		o := quoRemOracleOf(x, y)
		p := uint32(1 + rng.IntN(int(min(o.qDigits+2, 60))))
		ctx, err := NewContext(p, RoundingMode(rng.IntN(8)), nil, 0)
		if err != nil {
			t.Fatal(err)
		}
		for _, op := range quoRemOps {
			got, cond, err := quoRemContext(x, y, op, ctx, Budget{})
			if o.qDigits > uint64(p) {
				refused++
				if !errors.Is(err, ErrDivisionImpossible) || !got.Equal(Decimal{}) || got.Exponent() != 0 || cond != 0 {
					t.Fatalf("%v %s %v at p=%d: (%v, %v, %v), want DivisionImpossible", x, op, y, p, got, cond, err)
				}
				continue
			}
			admitted++
			want, exponent := o.want(op)
			checkQuoRem(t, fmt.Sprintf("%v %s %v p=%d", x, op, y, p), got, err, want, exponent)
			if cond != 0 {
				t.Fatalf("%v %s %v: conditions %v", x, op, y, cond)
			}
		}
	}
	if refused < 500 || admitted < 500 {
		t.Fatalf("vacuous sweep: %d refused, %d admitted", refused, admitted)
	}
	one, _ := NewContext(1, TiesToEven, nil, 0)
	for _, c := range []struct {
		x, y string
		op   intDivOp
		want string
	}{
		{"10", "1", intDivQuo, ""}, {"10", "1", intDivRem, ""}, {"10", "1", intDivRemNear, ""},
		{"9.9", "1", intDivQuo, "9"}, {"9.9", "1", intDivRemNear, "-0.1"}, {"9.9", "10", intDivRem, "9.9"},
		{"12345678901234567890", "12345678901234567891", intDivRem, "12345678901234567890"},
	} {
		got, _, err := quoRemContext(MustParse(c.x), MustParse(c.y), c.op, one, Budget{})
		if c.want == "" {
			if !errors.Is(err, ErrDivisionImpossible) {
				t.Errorf("%s %s %s at p=1: (%v, %v), want DivisionImpossible", c.x, c.op, c.y, got, err)
			}
			continue
		}
		if want := MustParse(c.want); err != nil || !got.Equal(want) || got.Exponent() != want.Exponent() {
			t.Errorf("%s %s %s at p=1: (%v, %v), want %s", c.x, c.op, c.y, got, err, c.want)
		}
	}
}

// quoRemTie builds x with x/y exactly half-way between two integers, on
// the requested path: q = 0 near (x = y/2), split with L = 0 (D = 0) or
// with 2L = 10^j (D = 1), and stream (v2(Cy) = v2(Cx) + k + 1).
func quoRemTie(rng *rand.Rand, path intDivPath, q int64) (Decimal, Decimal) {
	odd := func(n int) *big.Int {
		v, _ := new(big.Int).SetString(quoRemDigits(rng, n), 10)
		if v.Bit(0) == 0 {
			v.Add(v, big.NewInt(1))
		}
		return v
	}
	twoQ1 := big.NewInt(2*q + 1)
	sign := func(v *big.Int) string {
		if rng.IntN(2) == 0 {
			return "-" + v.String()
		}
		return v.String()
	}
	e := int32(rng.IntN(21) - 10)
	switch path {
	case intDivQZeroNear:
		cy := odd(1 + rng.IntN(20))
		return MustParse(fmt.Sprintf("%sE%d", sign(new(big.Int).Mul(cy, big.NewInt(5))), e-1)), MustParse(fmt.Sprintf("%sE%d", sign(cy), e))
	case intDivSplit:
		cy := odd(1 + rng.IntN(20))
		j := 1 + rng.IntN(20)
		if rng.IntN(2) == 0 {
			// D = 1: Cx = 5·Cy·(2q+1)·10^(j−1), so 2L = 10^j.
			cx := new(big.Int).Mul(new(big.Int).Mul(cy, big.NewInt(5)), twoQ1)
			cx.Mul(cx, pow10Big(int64(j-1)))
			return MustParse(fmt.Sprintf("%sE%d", sign(cx), e-int32(j))), MustParse(fmt.Sprintf("%sE%d", sign(cy), e))
		}
		// D = 0: Cy even, Cx = (Cy/2)(2q+1)·10^j, L = 0.
		half := odd(1 + rng.IntN(20))
		cx := new(big.Int).Mul(new(big.Int).Mul(half, twoQ1), pow10Big(int64(j)))
		return MustParse(fmt.Sprintf("%sE%d", sign(cx), e-int32(j))), MustParse(fmt.Sprintf("%sE%d", sign(new(big.Int).Lsh(half, 1)), e))
	}
	// Stream or modular: x·10^k = (Cy/2)(2q+1) with Cy = 2·10^k·B.
	k := rng.IntN(12)
	b := odd(1 + rng.IntN(15))
	cy := new(big.Int).Mul(new(big.Int).Lsh(b, 1), pow10Big(int64(k)))
	cx := new(big.Int).Mul(b, twoQ1)
	return MustParse(fmt.Sprintf("%sE%d", sign(cx), e+int32(k))), MustParse(fmt.Sprintf("%sE%d", sign(cy), e))
}

// TestRemNearTiesToEven checks that remainder-near ties to even: exact
// ties on every remainder path (q = 0 near, split with D = 0 and D = 1,
// stream and forced modular) with even and odd q select the even n, equal
// to math/big, and the directed ties 10 RemNear 4 = 2, 5 RemNear 2 = 1,
// 1.5 RemNear 1 = −0.5 and 2.5 RemNear 1 = 0.5.
func TestRemNearTiesToEven(t *testing.T) {
	rng := rand.New(rand.NewPCG(20260928, 61))
	seen := map[string]int{}
	for i := range 4000 {
		path := []intDivPath{intDivQZeroNear, intDivSplit, intDivStream, intDivModular}[i%4]
		q := int64(rng.IntN(1000))
		if path == intDivQZeroNear {
			q = 0
		}
		x, y := quoRemTie(rng, path, q)
		force := intDivForceNone
		if path == intDivModular {
			force = intDivForceModular
		} else if path == intDivStream {
			force = intDivForceStream
		}
		o := quoRemOracleOf(x, y)
		if twice := new(big.Int).Lsh(new(big.Int).Abs(o.r), 1); twice.CmpAbs(new(big.Int).Mul(quoRemCoefficientAt(y, o.m), big.NewInt(1))) != 0 {
			t.Fatalf("%v, %v is not a tie", x, y)
		}
		got, _, err, c := countedQuoRem(x, y, intDivRemNear, Context{}, Budget{}, force)
		checkQuoRem(t, fmt.Sprintf("%v RemNear %v", x, y), got, err, o.rn, o.m)
		seen[fmt.Sprintf("%s/odd=%t", c.taken, o.q.Bit(0) == 1)]++
	}
	for _, p := range []string{"q-zero-near/odd=false", "split/odd=false", "split/odd=true", "stream/odd=false", "stream/odd=true", "modular/odd=false", "modular/odd=true"} {
		if seen[p] < 50 {
			t.Errorf("tie class %s ran %d times: %v", p, seen[p], seen)
		}
	}
	for _, v := range [][3]string{{"10", "4", "2"}, {"5", "2", "1"}, {"1.5", "1", "-0.5"}, {"2.5", "1", "0.5"}, {"-2.5", "1", "-0.5"}, {"0.5", "1", "0.5"}} {
		got, err := MustParse(v[0]).RemNear(MustParse(v[1]))
		if want := MustParse(v[2]); err != nil || !got.Equal(want) || got.Exponent() != want.Exponent() {
			t.Errorf("%s RemNear %s = (%v, %v), want %s", v[0], v[1], got, err, v[2])
		}
	}
}

// quoRemCoefficientAt is |y|'s coefficient at exponent m ≤ ey.
func quoRemCoefficientAt(y Decimal, m int32) *big.Int {
	c, e := quoRemParts(y)
	return new(big.Int).Abs(new(big.Int).Mul(c, pow10Big(int64(e)-int64(m))))
}

// TestRemStreamMatchesModular covers the modular remainder: with the path
// choice pinned by the test seam, the stream and modular remainders agree
// with each other and with math/big for Rem and RemNear, over random k ≥ 0
// pairs with q ≠ 0; a guard requires both forced paths to run and exact
// ties on the modular path.
func TestRemStreamMatchesModular(t *testing.T) {
	rng := rand.New(rand.NewPCG(20260928, 62))
	modularTies, compared := 0, 0
	for i := range 3000 {
		var x, y Decimal
		if i%5 == 0 {
			x, y = quoRemTie(rng, intDivStream, int64(rng.IntN(500)))
		} else {
			dx, dy := 1+rng.IntN(60), 1+rng.IntN(40)
			k := rng.IntN(300)
			x, y = quoRemOperand(rng, dx, int32(k)), quoRemOperand(rng, dy, 0)
		}
		o := quoRemOracleOf(x, y)
		if o.q.Sign() == 0 || x.Exponent() < y.Exponent() {
			continue
		}
		for _, op := range []intDivOp{intDivRem, intDivRemNear} {
			want, exponent := o.want(op)
			s, _, errS, cs := countedQuoRem(x, y, op, Context{}, Budget{}, intDivForceStream)
			m, _, errM, cm := countedQuoRem(x, y, op, Context{}, Budget{}, intDivForceModular)
			if cs.taken != intDivStream || cm.taken != intDivModular {
				t.Fatalf("seam did not pin the path: %s, %s", cs.taken, cm.taken)
			}
			checkQuoRem(t, fmt.Sprintf("%v %s %v stream", x, op, y), s, errS, want, exponent)
			checkQuoRem(t, fmt.Sprintf("%v %s %v modular", x, op, y), m, errM, want, exponent)
			compared++
			if op == intDivRemNear && new(big.Int).Lsh(new(big.Int).Abs(o.r), 1).Cmp(quoRemCoefficientAt(y, o.m)) == 0 {
				modularTies++
			}
		}
	}
	if compared < 2000 || modularTies < 200 {
		t.Fatalf("vacuous differential: %d compared, %d modular ties", compared, modularTies)
	}
}

// quoRemCharges recomputes B and the plan for a call from the shapes and
// the oracle's classification (q = 0, or q's digit count).
func quoRemCharges(x, y Decimal, op intDivOp, qZero bool, qDigits uint64) (b uint64, plan intDivPlan) {
	s := intDivShape{dx: x.CoefficientDigits(), dy: y.CoefficientDigits(), ex: x.Exponent(), ey: y.Exponent()}
	b, _ = intDivPrecharge(s.dx, s.dy, x.IsZero())
	if x.IsZero() {
		return b, intDivPlan{path: intDivZeroDividend, nEnv: 1, ok: true}
	}
	return b, planIntDiv(op, s, qZero, qDigits, intDivForceNone)
}

// TestQuoRemTariffBoundsCountedWork checks the tariff through the division
// kernel's divCount seam: counted classification work never exceeds B, counted
// path work never exceeds C, output writes stay within 2N+1 and the arena
// within B + C, over a sweep with the tariff and gap witnesses, sparse and
// near-complement tails, all-nines quotients, and the stream/modular crossover
// for 20-digit operands.
func TestQuoRemTariffBoundsCountedWork(t *testing.T) {
	rng := rand.New(rand.NewPCG(20260928, 63))
	type call struct {
		x, y  Decimal
		force intDivForce
	}
	var calls []call
	for range 3000 {
		x, y := quoRemPair(rng)
		calls = append(calls, call{x, y, intDivForce(rng.IntN(3))})
	}
	for _, w := range [][2]string{
		{"1E-40", "1E+40"}, {"99", "100"}, {"12345E-2", "7E+1"}, {"1E+40", "1E-40"},
		{"1001", "1E+3"}, {"10000000001", "1E+10"}, {"1E+2147483647", "7"},
		{"1E-2147483648", "1E+2147483647"}, {"1E+2147483647", "1E-2147483648"},
		{strings.Repeat("9", 400), "1"}, {strings.Repeat("9", 400), "7"},
		{strings.Repeat("9", 300) + "0" + strings.Repeat("0", 50), "1E+51"},
		{"1" + strings.Repeat("0", 200) + "1", "3E+150"},
		{"5" + strings.Repeat("9", 100) + "E-100", "1"},
		{"123456789" + strings.Repeat("9", 90) + "E-90", "987654321"},
	} {
		calls = append(calls, call{MustParse(w[0]), MustParse(w[1]), intDivForceNone})
	}
	// Sparse and near-complement tails: Cx = a·10^k + tail over 10^k.
	for k := 1; k <= 60; k++ {
		for _, tail := range []string{"1", strings.Repeat("9", k), "9" + strings.Repeat("0", k-1), strings.Repeat("9", k/2+1)} {
			if len(tail) > k {
				continue
			}
			cx := "1" + strings.Repeat("0", k-len(tail)) + tail
			calls = append(calls, call{MustParse(cx), MustParse(fmt.Sprintf("1E+%d", k)), intDivForceNone},
				call{MustParse(cx), MustParse(fmt.Sprintf("3E+%d", k)), intDivForceNone})
		}
	}
	// The crossover for 20-digit operands, and the gap sweep up to 2^32−1.
	c20, d20 := "73786976294838206464", "18446744073709551557"
	for _, k := range []int64{0, 100, 499, 500, 501, 900, 1000, 1100, 5000, 10000, 1 << 20, 1<<31 - 1} {
		calls = append(calls, call{MustParse(fmt.Sprintf("%sE%d", c20, k)), MustParse(d20), intDivForceNone},
			call{MustParse(fmt.Sprintf("%sE%d", c20, k)), MustParse(d20), intDivForceStream},
			call{MustParse(fmt.Sprintf("%sE%d", c20, k)), MustParse(d20), intDivForceModular})
	}
	calls = append(calls, call{MustParse(c20 + "E2147483647"), MustParse(d20 + "E-2147483648"), intDivForceNone})
	checked := map[intDivPath]int{}
	for _, cl := range calls {
		for _, op := range quoRemOps {
			s := intDivShape{dx: cl.x.CoefficientDigits(), dy: cl.y.CoefficientDigits(), ex: cl.x.Exponent(), ey: cl.y.Exponent()}
			k := s.k()
			if op == intDivQuo && k > 5000 || cl.force == intDivForceStream && k > 20000 {
				continue // a gap-sized quotient or forced stream: real work, not a tariff question
			}
			got, _, err, c := countedQuoRem(cl.x, cl.y, op, Context{}, Budget{}, cl.force)
			if err != nil {
				t.Fatalf("%v %s %v: %v", cl.x, op, cl.y, err)
			}
			b, _ := intDivPrecharge(s.dx, s.dy, cl.x.IsZero())
			var plan intDivPlan
			if cl.x.IsZero() {
				plan = intDivPlan{path: intDivZeroDividend, nEnv: 1, ok: true}
			} else {
				qZero, q := classifyIntDiv(viewPtr(cl.x), viewPtr(cl.y), s, nil)
				plan = planIntDiv(op, s, qZero, q, cl.force)
			}
			if plan.path != c.taken {
				t.Fatalf("%v %s %v: plan %s, ran %s", cl.x, op, cl.y, plan.path, c.taken)
			}
			n := got.CoefficientDigits()
			label := fmt.Sprintf("%v %s %v (%s, force %d)", cl.x, op, cl.y, c.taken, cl.force)
			if c.classify.units > b {
				t.Fatalf("%s: classification %d > B %d", label, c.classify.units, b)
			}
			if c.path.units > plan.c {
				t.Fatalf("%s: path work %d > C %d", label, c.path.units, plan.c)
			}
			if c.out.units > 2*n+1 {
				t.Fatalf("%s: output %d > 2N+1 = %d", label, c.out.units, 2*n+1)
			}
			if c.arena > b+plan.c {
				t.Fatalf("%s: arena %d > B+C %d", label, c.arena, b+plan.c)
			}
			if n > plan.nEnv {
				t.Fatalf("%s: N %d > envelope %d", label, n, plan.nEnv)
			}
			checked[c.taken]++
		}
	}
	for p := intDivZeroDividend + 1; p <= intDivModular; p++ {
		if checked[p] < 20 {
			t.Errorf("path %s counted %d times", p, checked[p])
		}
	}
}

// viewPtr returns an addressable copy of d's coefficient view.
func viewPtr(d Decimal) *coefficientView {
	v := coefficientViewOf(d)
	return &v
}

// TestQuoRemTariffMatchesHandWitnesses pins the tariff table written
// out: B = dx+dy+1, C per path and W = B+C+2N+1 for 1E−40 Rem 1E+40 (3, 0,
// 1, 6), 99 RemNear 100 (6, 20, 1, 29), 12345E−2 Rem 7E+1 (7, 38, 4, 54),
// 1E+40 Rem 1E−40 (3, 153, 1, 159), 1E+40 Quo 1E−40 (3, 141, 81, 307) and
// 1E+2147483647 Rem 7 (3, 1,260, 1, 1,266), whose modular C expands as
// 1·19 + 31·(20+19) + 20 + 8 + 4; each W admits and W−1 refuses.
func TestQuoRemTariffMatchesHandWitnesses(t *testing.T) {
	muH, muS := uint64(2*1+1+(2*2*2+2*4)), uint64(1+3*1+(2*2*2+2*4)) // n′ = 1: D(2,1) = 16
	if muH != 19 || muS != 20 {
		t.Fatalf("μH %d, μS %d", muH, muS)
	}
	modular := 1*muH + 31*(muS+muH) + muS + 8*1 + 4
	for _, w := range []struct {
		x, y       string
		op         intDivOp
		q          uint64 // hand-derived digits of trunc(x/y), 0 for q = 0
		b, c, n, W uint64
		path       intDivPath
	}{
		{"1E-40", "1E+40", intDivRem, 0, 3, 0, 1, 6, intDivQZero},
		{"99", "100", intDivRemNear, 0, 6, 20, 1, 29, intDivQZeroNear},
		{"12345E-2", "7E+1", intDivRem, 1, 7, 38, 4, 54, intDivSplit},
		{"1E+40", "1E-40", intDivRem, 81, 3, 153, 1, 159, intDivStream},
		{"1E+40", "1E-40", intDivQuo, 81, 3, 141, 81, 307, intDivQuotient},
		{"1E+2147483647", "7", intDivRem, 2147483647, 3, modular, 1, 1266, intDivModular},
	} {
		x, y := MustParse(w.x), MustParse(w.y)
		b, plan := quoRemCharges(x, y, w.op, w.q == 0, max(w.q, 1))
		if b != w.b || plan.c != w.c || plan.path != w.path || b+plan.c+2*w.n+1 != w.W {
			t.Fatalf("%s %s %s: B %d C %d path %s, want %d %d %s W %d", w.x, w.op, w.y, b, plan.c, plan.path, w.b, w.c, w.path, w.W)
		}
		if _, err := quoRemPublic(x, y, w.op, Budget{MaxWork: w.W - 1}); !errors.Is(err, ErrInsufficientStorage) {
			t.Fatalf("%s %s %s at W−1: %v", w.x, w.op, w.y, err)
		}
		got, err := quoRemPublic(x, y, w.op, Budget{MaxWork: w.W, MaxDigits: w.n})
		if err != nil || got.CoefficientDigits() != w.n {
			t.Fatalf("%s %s %s at W: (%v, %v)", w.x, w.op, w.y, got, err)
		}
	}
	if modular != 1260 {
		t.Fatalf("modular C = %d", modular)
	}
}

// quoRemHeapArena is 1 when the plan's arena lives on the heap.
func quoRemHeapArena(plan intDivPlan) float64 {
	if plan.arena > divStackLimbs {
		return 1
	}
	return 0
}

// TestQuoRemBudgetBoundariesEveryPath covers integer division budget
// boundaries: on every path, work caps B−1 and B+C−1
// refuse with no arena allocated (only the error), W−1 refuses with no
// result buffer (the error plus a heap arena, for Rem and RemNear as well
// as Quo, whose W refusal also precedes the arena), W admits the exact
// result, and digit caps N−1 and N refuse and admit likewise. Witnesses
// with heap arenas and results above 38 digits make an early arena or
// result allocation observable.
func TestQuoRemBudgetBoundariesEveryPath(t *testing.T) {
	rng := rand.New(rand.NewPCG(20260928, 64))
	type call struct {
		x, y Decimal
		op   intDivOp
	}
	var calls []call
	for range 1500 {
		x, y := quoRemPair(rng)
		calls = append(calls, call{x, y, quoRemOps[rng.IntN(3)]})
	}
	big1, big2 := strings.Repeat("7", 500), strings.Repeat("3", 300)
	for _, w := range []struct {
		x, y string
		op   intDivOp
	}{
		{big1 + "E-200", big2, intDivRem}, {big1 + "E-200", big2, intDivRemNear},
		{big1 + "E-200", big2, intDivQuo},
		{big1, big2 + "E+3", intDivRem}, {big1, big2 + "E+3", intDivRemNear},
		{big1 + "E+5", big2, intDivRem}, {big1 + "E+5", big2, intDivRemNear},
		{big1 + "E+3000", big2, intDivRem}, {big1 + "E+3000", big2, intDivRemNear},
		{"7E+3000", big2, intDivRem},
		{big1, "9" + big1, intDivRemNear}, {big1, "1" + strings.Repeat("0", 500), intDivRemNear},
		{"7E+3000", "12345678901234567890123456789012345678901234567891", intDivRem}, {"7E+3000", "12345678901234567890123456789012345678901234567891", intDivRemNear},
		{big2 + "E+1", "9" + big1 + "E-1", intDivRem}, {big2 + "E+1", "9" + big1 + "E-1", intDivRemNear},
		{"0E+5", big2, intDivRem}, {"0E+5", big2, intDivQuo},
	} {
		calls = append(calls, call{MustParse(w.x), MustParse(w.y), w.op})
	}
	seen := map[string]int{}
	for _, cl := range calls {
		full, err := quoRemPublic(cl.x, cl.y, cl.op, Budget{})
		if err != nil {
			t.Fatalf("%v %s %v: %v", cl.x, cl.op, cl.y, err)
		}
		o := quoRemOracleOf(cl.x, cl.y)
		b, plan := quoRemCharges(cl.x, cl.y, cl.op, o.q.Sign() == 0, o.qDigits)
		n := full.CoefficientDigits()
		w := b + plan.c + 2*n + 1
		heapArena := quoRemHeapArena(plan)
		seen[fmt.Sprintf("%s/%s/heap=%t/wide=%t", cl.op, plan.path, heapArena == 1, n > 38)]++
		quoFirst := cl.op == intDivQuo
		for _, tc := range []struct {
			name   string
			budget Budget
			ok     bool
			allocs float64 // for a refusal
		}{
			{"B-1", Budget{MaxWork: b - 1}, b == 1, 1},
			{"B+C-1", Budget{MaxWork: b + plan.c - 1}, plan.c == 0 && b == 1, 1},
			{"W-1", Budget{MaxWork: w - 1}, false, map[bool]float64{true: 1, false: 1 + heapArena}[quoFirst]},
			{"W", Budget{MaxWork: w}, true, 0},
			{"N-1", Budget{MaxDigits: n - 1}, n == 1, map[bool]float64{true: 1, false: 1 + heapArena}[quoFirst]},
			{"N", Budget{MaxDigits: n}, true, 0},
		} {
			if tc.budget.MaxWork == 0 && tc.budget.MaxDigits == 0 {
				continue // a zero field is no quota
			}
			if tc.name == "B+C-1" && plan.c == 0 {
				continue // B+C−1 = B−1
			}
			got, err := quoRemPublic(cl.x, cl.y, cl.op, tc.budget)
			label := fmt.Sprintf("%v %s %v %s (B=%d C=%d N=%d path %s)", cl.x, cl.op, cl.y, tc.name, b, plan.c, n, plan.path)
			if tc.ok {
				if err != nil || !got.Equal(full) || got.Exponent() != full.Exponent() {
					t.Fatalf("%s: (%v, %v)", label, got, err)
				}
				continue
			}
			if !errors.Is(err, ErrInsufficientStorage) || !got.Equal(Decimal{}) {
				t.Fatalf("%s: (%v, %v), want InsufficientStorage", label, got, err)
			}
			if allocs := testing.AllocsPerRun(3, func() { _, _ = quoRemPublic(cl.x, cl.y, cl.op, tc.budget) }); allocs != tc.allocs {
				t.Fatalf("%s: %g allocations, want %g", label, allocs, tc.allocs)
			}
		}
	}
	for _, want := range []string{
		"Quo/quotient/heap=true/wide=true", "Rem/split/heap=true/wide=true", "RemNear/split/heap=true/wide=true",
		"Rem/stream/heap=true/wide=true", "RemNear/stream/heap=true/wide=true",
		"Rem/modular/heap=false/wide=true", "RemNear/modular/heap=false/wide=true",
		"RemNear/q-zero-near/heap=true/wide=true", "Rem/q-zero/heap=false/wide=true",
		"Quo/q-zero/heap=false/wide=false", "Rem/zero-dividend/heap=false/wide=false",
		"Rem/split/heap=false/wide=false", "RemNear/stream/heap=false/wide=false",
	} {
		if seen[want] == 0 {
			t.Errorf("boundary class %s never exercised: %v", want, seen)
		}
	}
}

// TestQuoRemPrecedence covers the integer division refusal order: each
// collision witness resolves at its stage.
func TestQuoRemPrecedence(t *testing.T) {
	guarded := func(p uint32, traps Conditions) Context {
		ctx, err := NewContext(p, TiesToEven, &ExponentGuards{}, traps)
		if err != nil {
			t.Fatal(err)
		}
		return ctx
	}
	plain := func(p uint32) Context {
		ctx, err := NewContext(p, TiesToEven, nil, 0)
		if err != nil {
			t.Fatal(err)
		}
		return ctx
	}
	for _, c := range []struct {
		name   string
		x, y   string
		op     intDivOp
		ctx    Context
		budget Budget
		want   ErrorCode // 0: success
		result string
	}{
		{"zero divisor before budget", "1", "0", intDivRemNear, Context{}, Budget{MaxWork: 1}, ErrDivisionByZero, ""},
		{"zero over zero before budget", "0", "0E3", intDivQuo, guarded(1, 0), Budget{MaxWork: 1}, ErrDivisionUndefined, ""},
		{"B before quotient fit", "10", "1", intDivRem, plain(1), Budget{MaxWork: 3}, ErrInsufficientStorage, ""},
		{"quotient fit at B", "10", "1", intDivRem, plain(1), Budget{MaxWork: 4}, ErrDivisionImpossible, ""},
		{"quotient fit before stored guard", "10.0", "1.0", intDivRem, guarded(1, 0), Budget{}, ErrDivisionImpossible, ""},
		{"adjusted guard before digit cap", "99", "100", intDivRem, guarded(2, 0), Budget{MaxDigits: 1}, ErrInvalidOperation, ""},
		{"near result fits", "99", "100", intDivRemNear, guarded(2, 0), Budget{MaxDigits: 1}, 0, "-1"},
		{"C before adjusted guard", "199", "100", intDivRem, guarded(3, 0), Budget{MaxWork: 35}, ErrInsufficientStorage, ""},
		{"adjusted guard at B+C", "199", "100", intDivRem, guarded(3, 0), Budget{MaxWork: 36}, ErrInvalidOperation, ""},
		{"W before trap", "0.1", "1", intDivRem, guarded(2, Subnormal), Budget{MaxWork: 5}, ErrInsufficientStorage, ""},
		{"trap keeps result", "0.1", "1", intDivRem, guarded(2, Subnormal), Budget{}, ErrSubnormal, "0.1"},
		{"digit cap", "9.9", "10", intDivRem, plain(1), Budget{MaxDigits: 1}, ErrInsufficientStorage, ""},
		{"digit cap admits", "9.9", "10", intDivRem, plain(1), Budget{MaxDigits: 2}, 0, "9.9"},
		{"B before stored guard", "1E-3", "1E+2", intDivRem, guarded(2, 0), Budget{MaxWork: 2}, ErrInsufficientStorage, ""},
		{"stored guard at B", "1E-3", "1E+2", intDivRem, guarded(2, 0), Budget{MaxWork: 3}, ErrInvalidOperation, ""},
		{"stored guard on a zero", "0E-3", "7", intDivRem, guarded(2, 0), Budget{}, ErrInvalidOperation, ""},
		{"Quo stored guard", "7", "2", intDivQuo, func() Context {
			ctx, _ := NewContext(5, TiesToEven, &ExponentGuards{Emin: 6, Emax: 9}, 0)
			return ctx
		}(), Budget{}, ErrInvalidOperation, ""},
		{"Quo adjusted guard", "123", "1", intDivQuo, guarded(5, 0), Budget{MaxWork: 7}, ErrInvalidOperation, ""},
		{"Quo digit cap before arena", "1E+2147483647", "7", intDivQuo, Context{}, Budget{MaxDigits: 1 << 20}, ErrInsufficientStorage, ""},
	} {
		x, y := MustParse(c.x), MustParse(c.y)
		got, cond, err := quoRemContext(x, y, c.op, c.ctx, c.budget)
		if c.want == 0 {
			if want := MustParse(c.result); err != nil || !got.Equal(want) || got.Exponent() != want.Exponent() {
				t.Errorf("%s: (%v, %v, %v), want %s", c.name, got, cond, err, c.result)
			}
			continue
		}
		if !errors.Is(err, c.want) {
			t.Errorf("%s: (%v, %v, %v), want %v", c.name, got, cond, err, c.want)
			continue
		}
		if c.want == ErrSubnormal {
			var ce *Error
			if want := MustParse(c.result); !errors.As(err, &ce) || ce.Code != 0 || ce.Condition != Subnormal || !got.Equal(want) || got.Exponent() != want.Exponent() || cond != 0 {
				t.Errorf("%s: (%v, %v, %v), want trapped Subnormal with %s", c.name, got, cond, err, c.result)
			}
			continue
		}
		var oe *Error
		if !errors.As(err, &oe) || !got.Equal(Decimal{}) || got.Exponent() != 0 || cond != 0 {
			t.Errorf("%s: (%v, %v, %v), want Decimal{}, 0 and *Error", c.name, got, cond, err)
		}
	}
	// The 477-million-limb Quo arena is refused before it exists.
	x, y := MustParse("1E+2147483647"), MustParse("7")
	if allocs := testing.AllocsPerRun(3, func() {
		_, _, _ = x.QuoWithContext(y, Context{}.WithBudget(Budget{MaxDigits: 1 << 20}))
	}); allocs != 1 {
		t.Fatalf("huge Quo refusal allocated %g objects", allocs)
	}
}

// TestQuoRemGapWitnesses checks that integer division work is free of
// exponent gaps, with int32 gap witnesses: 1E−40 Rem 1E+40 and
// 1E−2147483648 Rem 1E+2147483647 return the dividend after one unit of
// classification, with no path work and no allocation; 1E+2147483647 Rem 7
// is 3 and RemNear 3 by the modular path in an 11-limb stack arena with no
// allocation, and DivisionImpossible at p = 34; 1E+2147483647 Rem
// 1E−2147483648 is 0E−2147483648. Across a gap sweep of 20-digit operands
// from 2^10 to 2^32−1 the charge depends on bitlen(k) alone and the
// counted work stays within it, while the stream path's charge grows
// with k.
func TestQuoRemGapWitnesses(t *testing.T) {
	for _, w := range []struct{ x, y string }{{"1E-40", "1E+40"}, {"1E-2147483648", "1E+2147483647"}, {"-7E-2147483648", "3E+2147483647"}} {
		x, y := MustParse(w.x), MustParse(w.y)
		for _, op := range []intDivOp{intDivRem, intDivRemNear} {
			got, _, err, c := countedQuoRem(x, y, op, Context{}, Budget{}, intDivForceNone)
			if err != nil || !got.Equal(x) || got.Exponent() != x.Exponent() || c.classify.units != 1 || c.path.units != 0 || c.arena != 0 {
				t.Fatalf("%s %s %s: (%v, %v) classify %d path %d arena %d", w.x, op, w.y, got, err, c.classify.units, c.path.units, c.arena)
			}
			if allocs := testing.AllocsPerRun(20, func() { _, _ = quoRemPublic(x, y, op, Budget{MaxWork: 6}) }); allocs != 0 {
				t.Fatalf("%s %s %s: %g allocations", w.x, op, w.y, allocs)
			}
		}
	}
	x, y := MustParse("1E+2147483647"), MustParse("7")
	// The plan is checked first: a stream plan here is a 477-million-limb arena.
	if plan := planIntDiv(intDivRem, intDivShape{dx: 1, dy: 1, ex: math.MaxInt32}, false, math.MaxInt32, intDivForceNone); plan.path != intDivModular || plan.c != 1260 || plan.arena != 11 {
		t.Fatalf("1E+2147483647 Rem 7 plan: %+v", plan)
	}
	for _, op := range []intDivOp{intDivRem, intDivRemNear} {
		got, _, err, c := countedQuoRem(x, y, op, Context{}, Budget{}, intDivForceNone)
		if err != nil || !got.Equal(MustParse("3")) || got.Exponent() != 0 || c.taken != intDivModular || c.arena != 11 || c.path.units > 1260 {
			t.Fatalf("1E+2147483647 %s 7: (%v, %v) path %s arena %d work %d", op, got, err, c.taken, c.arena, c.path.units)
		}
		if allocs := testing.AllocsPerRun(5, func() { _, _ = quoRemPublic(x, y, op, Budget{MaxWork: 1266}) }); allocs != 0 {
			t.Fatalf("1E+2147483647 %s 7: %g allocations", op, allocs)
		}
	}
	p34, _ := NewContext(34, TiesToEven, nil, 0)
	if _, _, err := x.RemWithContext(y, p34); !errors.Is(err, ErrDivisionImpossible) {
		t.Fatalf("1E+2147483647 Rem 7 at p=34: %v", err)
	}
	if got, err := x.Rem(MustParse("1E-2147483648")); err != nil || !got.IsZero() || got.Exponent() != math.MinInt32 || got.negative() {
		t.Fatalf("1E+2147483647 Rem 1E−2147483648: (%v, %v)", got, err)
	}
	// Independent check of the modular value at a moderate gap: 10^k mod 7
	// cycles with period 6 (3, 2, 6, 4, 5, 1).
	for k := range 60 {
		got, err := MustParse(fmt.Sprintf("1E+%d", 1000+k)).Rem(y)
		want := []int64{1, 3, 2, 6, 4, 5}[(1000+k)%6]
		if err != nil || !got.Equal(New(want, 0)) {
			t.Fatalf("1E+%d Rem 7 = (%v, %v), want %d", 1000+k, got, err, want)
		}
	}
	// Gap sweep: C depends on bitlen(k) alone once modular.
	c20, d20 := "73786976294838206464", "18446744073709551557"
	byBits := map[int]uint64{}
	var lastStream uint64
	for _, k := range []int64{1 << 10, 1<<10 + 1, 1<<11 - 1, 1 << 16, 1<<16 + 12345, 1<<17 - 1, 1 << 24, 1<<31 - 1, 1 << 31, 1<<32 - 1} {
		ex := int32(min(k, math.MaxInt32))
		ey := int32(int64(ex) - k)
		x := MustParse(fmt.Sprintf("%sE%d", c20, ex))
		y := MustParse(fmt.Sprintf("%sE%d", d20, ey))
		s := intDivShape{dx: 20, dy: 20, ex: ex, ey: ey}
		plan := planIntDiv(intDivRem, s, false, 0, intDivForceNone)
		stream := planIntDiv(intDivRem, s, false, 0, intDivForceStream)
		if plan.path != intDivModular || plan.arena != 25 || stream.c <= lastStream {
			t.Fatalf("k=%d: path %s arena %d, stream C %d after %d", k, plan.path, plan.arena, stream.c, lastStream)
		}
		lastStream = stream.c
		if prev, ok := byBits[bits.Len64(uint64(k))]; ok && prev != plan.c {
			t.Fatalf("k=%d: C %d differs from %d at the same bit length", k, plan.c, prev)
		}
		byBits[bits.Len64(uint64(k))] = plan.c
		got, _, err, c := countedQuoRem(x, y, intDivRem, Context{}, Budget{}, intDivForceNone)
		if err != nil || c.path.units > plan.c || c.arena != 25 {
			t.Fatalf("k=%d: (%v, %v) work %d > C %d, arena %d", k, got, err, c.path.units, plan.c, c.arena)
		}
		cy, _ := new(big.Int).SetString(d20, 10)
		cx, _ := new(big.Int).SetString(c20, 10)
		want := new(big.Int).Exp(big.NewInt(10), big.NewInt(k), cy)
		want.Mul(want, cx).Mod(want, cy)
		if gc, _ := quoRemParts(got); gc.Cmp(want) != 0 || got.Exponent() != ey {
			t.Fatalf("k=%d: %v, want %v at %d", k, got, want, ey)
		}
	}
}

// TestRemReusedOperandIsImmutable checks that a reused remainder operand
// stays immutable: a q = 0 Rem with ex ≤ ey returns the
// dividend's own coefficient holder. Shallow copies of the slow-coefficient
// operand and of the result, read concurrently and used in later
// operations, keep each other's value and holder unchanged; the digit cap
// still applies to N = dx.
func TestRemReusedOperandIsImmutable(t *testing.T) {
	text := "-" + strings.Repeat("1234567890", 10) + "E-7"
	x := MustParse(text)
	y := MustParse("1E+200")
	if x.slow == nil {
		t.Fatal("operand is not a slow coefficient")
	}
	r, err := x.Rem(y)
	if err != nil || r.slow != x.slow || !r.Equal(x) || r.Exponent() != x.Exponent() {
		t.Fatalf("q = 0 Rem did not return the dividend: (%v, %v)", r, err)
	}
	if _, _, err := x.RemWithContext(y, Context{}.WithBudget(Budget{MaxDigits: 99})); !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("digit cap below N = dx: %v", err)
	}
	if _, _, err := x.RemWithContext(y, Context{}.WithBudget(Budget{MaxDigits: 100})); err != nil {
		t.Fatalf("digit cap at N = dx: %v", err)
	}
	holder, limbs := x.slow, append([]uint32(nil), x.slow.limbs...)
	xc, rc := x, r
	var wg sync.WaitGroup
	for i := range 8 {
		wg.Go(func() {
			for range 200 {
				v := xc
				if i%2 == 1 {
					v = rc
				}
				if s := v.String(); s != MustParse(text).String() {
					t.Errorf("concurrent read: %s", s)
					return
				}
				sum, err := v.Add(New(int64(i+1), 0))
				if err != nil || sum.Equal(v) {
					t.Errorf("later operation: (%v, %v)", sum, err)
					return
				}
				if _, err := v.Rem(y); err != nil {
					t.Error(err)
					return
				}
				if _, err := v.Mul(v); err != nil {
					t.Error(err)
					return
				}
			}
		})
	}
	wg.Wait()
	if x.slow != holder || r.slow != holder || !slices.Equal(holder.limbs, limbs) || x.String() != MustParse(text).String() || r.String() != x.String() {
		t.Fatalf("operand or result changed: %v %v", x, r)
	}
}

// TestQuoRemGuardedContextAgainstOracle covers guarded contexts for the
// family: under random guards, precisions and Subnormal traps, stored
// exponents outside [Etiny, Emax] and adjusted exponents above Emax are
// InvalidOperation, a finite result whose adjusted exponent is below Emin
// reports Subnormal alone, and a selected trap returns that result with an
// *Error; every other outcome equals the unlimited oracle result.
func TestQuoRemGuardedContextAgainstOracle(t *testing.T) {
	rng := rand.New(rand.NewPCG(20260928, 65))
	counts := map[string]int{}
	for range 4000 {
		dx, dy := 1+rng.IntN(12), 1+rng.IntN(10)
		x := quoRemOperand(rng, dx, int32(rng.IntN(31)-15))
		y := quoRemOperand(rng, dy, int32(rng.IntN(31)-15))
		o := quoRemOracleOf(x, y)
		p := uint32(1 + rng.IntN(25))
		emin := int32(rng.IntN(31) - 15)
		emax := emin + int32(rng.IntN(20))
		traps := Conditions(0)
		if rng.IntN(2) == 0 {
			traps = Subnormal
		}
		ctx, err := NewContext(p, TiesToEven, &ExponentGuards{Emin: emin, Emax: emax}, traps)
		if err != nil {
			t.Fatal(err)
		}
		etiny := int64(emin) - int64(p) + 1
		for _, op := range quoRemOps {
			want, exponent := o.want(op)
			got, cond, err := quoRemContext(x, y, op, ctx, Budget{})
			label := fmt.Sprintf("%v %s %v p=%d [%d,%d]", x, op, y, p, emin, emax)
			adjusted := int64(exponent) + int64(len(new(big.Int).Abs(want).String())) - 1
			switch {
			case o.qDigits > uint64(p):
				counts["impossible"]++
				if !errors.Is(err, ErrDivisionImpossible) {
					t.Fatalf("%s: %v, want DivisionImpossible", label, err)
				}
			case int64(exponent) < etiny || int64(exponent) > int64(emax) || want.Sign() != 0 && adjusted > int64(emax):
				counts["invalid"]++
				if !errors.Is(err, ErrInvalidOperation) || cond != 0 || !got.Equal(Decimal{}) {
					t.Fatalf("%s: (%v, %v, %v), want InvalidOperation", label, got, cond, err)
				}
			case want.Sign() != 0 && adjusted < int64(emin):
				counts["subnormal"]++
				if traps != 0 {
					var ce *Error
					if !errors.As(err, &ce) || ce.Code != 0 || ce.Condition != Subnormal || cond != 0 {
						t.Fatalf("%s: (%v, %v, %v), want trapped Subnormal", label, got, cond, err)
					}
					err = nil
				} else if cond != Subnormal {
					t.Fatalf("%s: conditions %v, want Subnormal", label, cond)
				}
				checkQuoRem(t, label, got, err, want, exponent)
			default:
				counts["normal"]++
				checkQuoRem(t, label, got, err, want, exponent)
				if cond != 0 {
					t.Fatalf("%s: conditions %v", label, cond)
				}
			}
		}
	}
	for _, k := range []string{"impossible", "invalid", "subnormal", "normal"} {
		if counts[k] < 200 {
			t.Fatalf("vacuous class %s: %v", k, counts)
		}
	}
}

var quoRemSink Decimal

// TestQuoRemStackCasesDoNotAllocate covers the allocation guarantee: results
// of at most 38 digits whose arena fits the 48-limb stack allocate nothing, on
// the q = 0, q = 0 near, Quo, split, stream and modular paths.
func TestQuoRemStackCasesDoNotAllocate(t *testing.T) {
	for _, c := range []struct {
		x, y string
		op   intDivOp
	}{
		{"12345678901234567890123456789012345678", "987654321", intDivQuo},
		{"12345678901234567890123456789012345678", "987654321", intDivRem},
		{"12345678901234567890123456789012345678E-30", "987654321", intDivRemNear},
		{"12345678901234567890123456789012345678", "9876543210987654321E+3", intDivRemNear},
		{"7E+100000", "12345678901234567", intDivRemNear},
		{"99", "100", intDivRemNear},
		{"-1.5", "1E+30", intDivRem},
		{"15", "1E-3", intDivRem},
	} {
		x, y := MustParse(c.x), MustParse(c.y)
		if allocs := testing.AllocsPerRun(50, func() { quoRemSink, _ = quoRemPublic(x, y, c.op, Budget{}) }); allocs != 0 {
			t.Errorf("%s %s %s: %g allocations", c.x, c.op, c.y, allocs)
		}
	}
}

// TestRemNearSplitComplementLength covers the split path's length pass for
// 10^j − L: with Hrem = Cy − 1 the RemNear up has a zero high part, and
// L = 10^j − 10^m (L = 990 at j = 3 gives 10) leaves the
// complement 10^m of exactly m+1 digits, which the digit cap admits at
// N = m+1 and refuses at m; values against math/big, for j up to 40
// across the 9- and 18-digit limb boundaries.
func TestRemNearSplitComplementLength(t *testing.T) {
	rng := rand.New(rand.NewPCG(20260928, 68))
	for j := 1; j <= 40; j++ {
		for m := 0; m < j; m++ {
			cy, _ := new(big.Int).SetString(quoRemDigits(rng, 1+rng.IntN(25)), 10)
			if cy.Cmp(big.NewInt(3)) < 0 {
				cy.SetInt64(7)
			}
			hrem := new(big.Int).Sub(cy, big.NewInt(1))
			h := new(big.Int).Add(new(big.Int).Mul(cy, big.NewInt(int64(1+rng.IntN(1000)))), hrem)
			l := new(big.Int).Sub(pow10Big(int64(j)), pow10Big(int64(m)))
			cx := new(big.Int).Add(new(big.Int).Mul(h, pow10Big(int64(j))), l)
			ey := int32(rng.IntN(21) - 10)
			x := MustParse(fmt.Sprintf("%sE%d", cx, ey-int32(j)))
			y := MustParse(fmt.Sprintf("%sE%d", cy, ey))
			o := quoRemOracleOf(x, y)
			got, _, err, c := countedQuoRem(x, y, intDivRemNear, Context{}, Budget{}, intDivForceNone)
			checkQuoRem(t, fmt.Sprintf("%v RemNear %v", x, y), got, err, o.rn, o.m)
			if c.taken != intDivSplit || got.CoefficientDigits() != uint64(m+1) || !got.negative() {
				t.Fatalf("j=%d m=%d: %v path %s", j, m, got, c.taken)
			}
			if _, _, err := x.RemNearWithContext(y, Context{}.WithBudget(Budget{MaxDigits: uint64(m + 1)})); err != nil {
				t.Fatalf("j=%d m=%d: digit cap N refused: %v", j, m, err)
			}
			if m > 0 {
				if _, _, err := x.RemNearWithContext(y, Context{}.WithBudget(Budget{MaxDigits: uint64(m)})); !errors.Is(err, ErrInsufficientStorage) {
					t.Fatalf("j=%d m=%d: digit cap N−1 admitted: %v", j, m, err)
				}
			}
		}
	}
}
