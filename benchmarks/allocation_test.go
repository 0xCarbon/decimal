// SPDX-License-Identifier: Apache-2.0

// Allocation class of the hot operations. The counts follow from the
// representation, so each is an exact bound, not a statistical threshold.

package benchmarks

import (
	"encoding/binary"
	"hash/maphash"
	"math/big"
	"strings"
	"testing"

	decimal "github.com/0xCarbon/decimal"
)

// allocationRow is one public operation, its independent math/big value and
// its allocation class: 0 for inline results (below 2^128), 1 for a slow
// result of at most 81 digits (one fused holder), 2 above (holder and
// exact slice).
var (
	sinkBool   bool
	sinkUint64 uint64
)

type allocationRow struct {
	name   string
	op     func() (decimal.Decimal, error)
	want   string
	budget float64
}

func mustDecimal(tb testing.TB, s string) decimal.Decimal {
	tb.Helper()
	d, err := decimal.Parse(s)
	if err != nil {
		tb.Fatalf("Parse(%q): %v", s, err)
	}
	return d
}

func ratOf(tb testing.TB, s string) *big.Rat {
	tb.Helper()
	r, ok := new(big.Rat).SetString(s)
	if !ok {
		tb.Fatalf("big.Rat(%q)", s)
	}
	return r
}

// allocationRows returns the hot-operation table; every expected value is
// computed with math/big, independently of the library.
func allocationRows(tb testing.TB) []allocationRow {
	nines38 := strings.Repeat("9", 38)
	sevens38 := strings.Repeat("7", 38)
	threes18 := strings.Repeat("3", 18) + "E-4"
	d37a, d37b := strings.Repeat("4", 37)+"E-2", strings.Repeat("5", 36)+"1E-2"
	d19a, d19b := strings.Repeat("7", 19), strings.Repeat("3", 18)+"9"
	nines41 := strings.Repeat("9", 41)
	big45 := strings.Repeat("123456789", 5)
	q60 := strings.Repeat("9", 60) + "E-10"
	money := "12345678901234567.89"

	x38, y38, z18 := mustDecimal(tb, nines38), mustDecimal(tb, sevens38), mustDecimal(tb, threes18)
	a37, b37 := mustDecimal(tb, d37a), mustDecimal(tb, d37b)
	a19, b19 := mustDecimal(tb, d19a), mustDecimal(tb, d19b)
	s41, q := mustDecimal(tb, nines41), mustDecimal(tb, q60)
	m := mustDecimal(tb, money)
	four := mustDecimal(tb, "4")

	r := func(s string) *big.Rat { return ratOf(tb, s) }
	str := func(x *big.Rat) string { return x.RatString() }
	quo := func(x, y *big.Rat, exp int) string {
		// Round x/y half to even at 10^exp with math/big.
		scale := new(big.Rat).SetInt(new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(-exp)), nil))
		v := new(big.Rat).Mul(new(big.Rat).Quo(x, y), scale)
		n, rem := new(big.Int).QuoRem(v.Num(), v.Denom(), new(big.Int))
		twice := new(big.Int).Mul(rem, big.NewInt(2))
		if c := twice.CmpAbs(v.Denom()); c > 0 || c == 0 && n.Bit(0) == 1 {
			n.Add(n, big.NewInt(int64(v.Sign())))
		}
		return new(big.Rat).Quo(new(big.Rat).SetInt(n), scale).RatString()
	}
	ctx := decimal.Decimal128Context()
	// x38/y38 rounded half to even to 34 significant digits, by math/big.
	divContextWant := sigRound(new(big.Rat).Quo(r(nines38), r(sevens38)), 34)

	nines81, ten81 := strings.Repeat("9", 81), "1"+strings.Repeat("0", 81)
	big81, _ := new(big.Int).SetString(nines81, 10)
	big82, _ := new(big.Int).SetString(ten81, 10)
	bytes60, _ := new(big.Int).SetString(strings.Repeat("7", 60), 10)
	d60a, d60b := strings.Repeat("8", 60), strings.Repeat("6", 60)
	x60, y60 := mustDecimal(tb, d60a), mustDecimal(tb, d60b)
	raw81, raw60 := big81.Bytes(), bytes60.Bytes()
	ctx60, err := decimal.NewContext(60, decimal.TiesToEven, nil, 0)
	if err != nil {
		tb.Fatal(err)
	}
	guarded60, err := decimal.NewContext(60, decimal.TiesToEven, &decimal.ExponentGuards{Emin: -99, Emax: 99}, 0)
	if err != nil {
		tb.Fatal(err)
	}
	p50a, p49b := strings.Repeat("9", 50), strings.Repeat("3", 49)+"E-7"
	x50, y49 := mustDecimal(tb, p50a), mustDecimal(tb, p49b)
	top, ten := mustDecimal(tb, "9E99"), mustDecimal(tb, "10")

	return []allocationRow{
		{"inline/add37", func() (decimal.Decimal, error) { return a37.Add(b37) }, str(new(big.Rat).Add(r(d37a), r(d37b))), 0},
		{"inline/sub37", func() (decimal.Decimal, error) { return a37.Sub(b37) }, str(new(big.Rat).Sub(r(d37a), r(d37b))), 0},
		{"inline/mul19x19", func() (decimal.Decimal, error) { return a19.Mul(b19) }, str(new(big.Rat).Mul(r(d19a), r(d19b))), 0},
		{"inline/quantize-money", func() (decimal.Decimal, error) {
			d, _, err := m.Quantize(-1, decimal.TiesToEven)
			return d, err
		}, quo(r(money), r("1"), -1), 0},
		{"inline/div-exact", func() (decimal.Decimal, error) { return m.Div(four) }, str(new(big.Rat).Quo(r(money), r("4"))), 0},
		{"inline/div-to-exponent", func() (decimal.Decimal, error) {
			d, _, err := a19.DivToExponent(b19, -2, decimal.TiesToEven)
			return d, err
		}, quo(r(d19a), r(d19b), -2), 0},
		{"inline/div-context34", func() (decimal.Decimal, error) {
			d, _, err := x38.DivWithContext(y38, ctx)
			return d, err
		}, divContextWant, 0},
		{"inline/fma19", func() (decimal.Decimal, error) { return fmaExact(a19, b19, four) },
			str(new(big.Rat).Add(new(big.Rat).Mul(r(d19a), r(d19b)), r("4"))), 0},
		{"inline/fma-context34", func() (decimal.Decimal, error) {
			d, _, err := x38.FMAWithContext(y38, z18, ctx)
			return d, err
		}, sigRound(new(big.Rat).Add(new(big.Rat).Mul(r(nines38), r(sevens38)), r(threes18)), 34), 0},
		{"slow/fma38x38", func() (decimal.Decimal, error) { return fmaExact(x38, y38, z18) },
			str(new(big.Rat).Add(new(big.Rat).Mul(r(nines38), r(sevens38)), r(threes18))), 1},
		{"slow/sub41", func() (decimal.Decimal, error) { return s41.Sub(y38) }, str(new(big.Rat).Sub(r(nines41), r(sevens38))), 1},
		{"slow/add-above-2^128", func() (decimal.Decimal, error) { return s41.Add(x38) }, str(new(big.Rat).Add(r(nines41), r(nines38))), 1},
		{"slow/mul38x18", func() (decimal.Decimal, error) { return x38.Mul(z18) }, str(new(big.Rat).Mul(r(nines38), r(threes18))), 1},
		{"slow/mul38x38", func() (decimal.Decimal, error) { return x38.Mul(y38) }, str(new(big.Rat).Mul(r(nines38), r(sevens38))), 1},
		{"slow/div-to-exponent-30", func() (decimal.Decimal, error) {
			d, _, err := x38.DivToExponent(z18, -30, decimal.TiesToEven)
			return d, err
		}, quo(r(nines38), r(threes18), -30), 1},
		{"slow/quantize62", func() (decimal.Decimal, error) {
			d, _, err := q.Quantize(-12, decimal.TiesToEven)
			return d, err
		}, str(r(q60)), 1},
		{"slow/parse45", func() (decimal.Decimal, error) { return decimal.Parse(big45) }, big45, 1},
		{"slow/from-big-int81", func() (decimal.Decimal, error) { return decimal.FromBigInt(big81) }, nines81, 1},
		{"slow/compose81", func() (decimal.Decimal, error) {
			var d decimal.Decimal
			err := d.Compose(0, false, raw81, -2)
			return d, err
		}, nines81 + "/100", 1},
		{"slow/twos-complement60", func() (decimal.Decimal, error) {
			return decimal.NewTwosComplement(raw60, binary.BigEndian, 0)
		}, bytes60.String(), 1},
		{"slow/from-float64-exact", func() (decimal.Decimal, error) { return decimal.FromFloat64Exact(1e-5) }, str(new(big.Rat).SetFloat64(1e-5)), 1},
		{"slow/context60-add", func() (decimal.Decimal, error) {
			d, _, err := x50.AddWithContext(y49, ctx60)
			return d, err
		}, str(new(big.Rat).Add(r(p50a), r(p49b))), 1},
		{"slow/context60-overflow", func() (decimal.Decimal, error) {
			// Overflow under guards publishes the largest finite value:
			// sixty nines at Emax (conditions checked elsewhere).
			d, _, err := top.MulWithContext(ten, guarded60)
			return d, err
		}, strings.Repeat("9", 60) + strings.Repeat("0", 40), 1},
		{"wide/from-big-int82", func() (decimal.Decimal, error) { return decimal.FromBigInt(big82) }, ten81, 2},
		{"wide/mul60x60", func() (decimal.Decimal, error) { return x60.Mul(y60) }, str(new(big.Rat).Mul(r(d60a), r(d60b))), 2},
	}
}

// sigRound rounds a positive rational half to even to p significant
// digits with math/big and returns it as a RatString.
func sigRound(x *big.Rat, p int) string {
	ten := big.NewInt(10)
	e := 0
	scaled := new(big.Rat).Set(x)
	lo := new(big.Rat).SetInt(new(big.Int).Exp(ten, big.NewInt(int64(p-1)), nil))
	hi := new(big.Rat).SetInt(new(big.Int).Exp(ten, big.NewInt(int64(p)), nil))
	tenRat := new(big.Rat).SetInt64(10)
	for scaled.Cmp(lo) < 0 {
		scaled.Mul(scaled, tenRat)
		e--
	}
	for scaled.Cmp(hi) >= 0 {
		scaled.Quo(scaled, tenRat)
		e++
	}
	n, rem := new(big.Int).QuoRem(scaled.Num(), scaled.Denom(), new(big.Int))
	twice := new(big.Int).Mul(rem, big.NewInt(2))
	if c := twice.Cmp(scaled.Denom()); c > 0 || c == 0 && n.Bit(0) == 1 {
		n.Add(n, big.NewInt(1))
	}
	v := new(big.Rat).SetInt(n)
	for ; e < 0; e++ {
		v.Quo(v, tenRat)
	}
	for ; e > 0; e-- {
		v.Mul(v, tenRat)
	}
	return v.RatString()
}

// TestAllocationBudgets pins that hot operations avoid a per-operation heap
// profile: every hot public operation is
// checked against math/big, then held to its allocation class (0 inline, 1
// for a slow result up to 81 digits); the F2 and F6 timed bodies allocate
// nothing; a running sum allocates at most once per Add after it leaves 128
// bits and never below.
func TestAllocationBudgets(t *testing.T) {
	exceeded := "allocation class exceeded: the representation no longer meets its allocation budget"
	for _, row := range allocationRows(t) {
		got, err := row.op()
		if err != nil {
			t.Fatalf("%s: %v", row.name, err)
		}
		if row.want != "" {
			if text, _ := got.Text(0); ratOf(t, text).Cmp(ratOf(t, row.want)) != 0 {
				t.Fatalf("%s = %s, math/big %s", row.name, text, row.want)
			}
		}
		allocs := testing.AllocsPerRun(200, func() { sinkDecimal, _ = row.op() })
		if allocs > row.budget {
			t.Errorf("%s: %v allocs/op, budget %v; %s", row.name, allocs, row.budget, exceeded)
		}
	}

	x, y := mustDecimal(t, strings.Repeat("9", 38)), mustDecimal(t, strings.Repeat("9", 37)+"8")
	var h maphash.Hash
	hasher := decimal.Hasher{}
	observers := map[string]func(){
		"inline/compare38": func() { sinkInt = x.Compare(y) },
		"inline/equal38":   func() { sinkBool = x.Equal(y) },
		"inline/hash38":    func() { h.Reset(); hasher.Hash(&h, x); sinkUint64 = h.Sum64() },
	}
	for name, f := range observers {
		if allocs := testing.AllocsPerRun(200, f); allocs != 0 {
			t.Errorf("%s: %v allocs/op, budget 0; %s", name, allocs, exceeded)
		}
	}

	f2 := make([]decimal.Decimal, len(portfolioF2Inputs))
	for i, input := range portfolioF2Inputs {
		f2[i] = mustDecimal(t, input)
	}
	if allocs := testing.AllocsPerRun(20, func() {
		var sum decimal.Decimal
		for _, v := range f2 {
			sum, _ = sum.Add(v)
		}
		sinkDecimal = sum
	}); allocs != 0 {
		t.Errorf("F2Aggregate/mixed1000: %v allocs per batch, budget 0; %s", allocs, exceeded)
	}
	for variant, pair := range portfolioF6Inputs {
		left, right := mustDecimal(t, pair[0]), mustDecimal(t, pair[1])
		ops := map[string]func(){
			"add19":    func() { sinkDecimal, _ = left.Add(right) },
			"mul19":    func() { sinkDecimal, _ = left.Mul(right) },
			"mulsmall": func() { sinkDecimal, _ = left.Mul(right) },
			"div2dp":   func() { sinkDecimal, _, _ = left.DivToExponent(right, -2, decimal.TiesToEven) },
			"divby4":   func() { sinkDecimal, _ = left.Div(right) },
			"cmp19":    func() { sinkInt = left.Compare(right) },
		}
		if allocs := testing.AllocsPerRun(200, ops[variant]); allocs != 0 {
			t.Errorf("F6TightArith/%s: %v allocs/op, budget 0; %s", variant, allocs, exceeded)
		}
	}

	// A running sum that leaves 128 bits costs at most one allocation per
	// Add (its fused holder); below 2^128 it costs none.
	for _, tc := range []struct {
		name   string
		start  string
		budget float64
	}{
		{"running-sum/below-2^128", "1", 0},
		{"running-sum/above-2^128", strings.Repeat("9", 40), 1},
	} {
		sum, step := mustDecimal(t, tc.start), mustDecimal(t, "123456789.123456789")
		oracle, stepRat := ratOf(t, tc.start), ratOf(t, "123456789.123456789")
		allocs := testing.AllocsPerRun(1000, func() {
			sum, _ = sum.Add(step)
			oracle.Add(oracle, stepRat)
		})
		if text, _ := sum.Text(0); ratOf(t, text).Cmp(oracle) != 0 {
			t.Fatalf("%s = %s, math/big %s", tc.name, text, oracle.RatString())
		}
		// The oracle's own allocations are measured out separately.
		oracleOnly := testing.AllocsPerRun(1000, func() { oracle.Add(oracle, stepRat) })
		if allocs-oracleOnly > tc.budget {
			t.Errorf("%s: %v allocs/Add, budget %v; %s", tc.name, allocs-oracleOnly, tc.budget, exceeded)
		}
	}
}

// TestAllocationClassBoundaries covers the edges of the allocation classes:
// for every producer, a result of exactly 81 digits
// (nine limbs, one fused allocation) and one of 82 digits (holder plus exact
// slice), including additions whose planned carry limb makes the scratch
// ten limbs, and the operand-bound rows where an operation's own scratch
// exceeds the stack even though its result is inline. Values are checked
// against math/big first.
func TestAllocationClassBoundaries(t *testing.T) {
	pow := func(n int) *big.Int { return new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(n)), nil) }
	nines := func(n int) string { return strings.Repeat("9", n) }
	dec := func(n *big.Int) decimal.Decimal { return mustDecimal(t, n.String()) }
	one := big.NewInt(1)
	p80, p81 := pow(80), pow(81)
	p40, p41 := dec(pow(40)), dec(new(big.Int).Sub(pow(41), one))
	d80a, d80b := strings.Repeat("6", 80), strings.Repeat("4", 80)
	x80, y80, one1 := mustDecimal(t, d80a), mustDecimal(t, d80b), mustDecimal(t, "1")
	x81, x82 := dec(p80), dec(p81)
	n80e1 := mustDecimal(t, nines(80)+"E1")
	q60 := mustDecimal(t, strings.Repeat("7", 60))
	ctx81, _ := decimal.NewContext(81, decimal.TiesToEven, nil, 0)
	ctx82, _ := decimal.NewContext(82, decimal.TiesToEven, nil, 0)
	g81, _ := decimal.NewContext(81, decimal.TiesToEven, &decimal.ExponentGuards{Emin: -99, Emax: 99}, 0)
	g82, _ := decimal.NewContext(82, decimal.TiesToEven, &decimal.ExponentGuards{Emin: -99, Emax: 99}, 0)
	top, ten := mustDecimal(t, "9E99"), mustDecimal(t, "10")
	b81, b82 := new(big.Int).Sub(p81, one), new(big.Int).Sub(pow(82), one)
	raw81, raw82 := b81.Bytes(), b82.Bytes()
	lane81, lane82 := append([]byte{0}, raw81...), append([]byte{0}, raw82...)
	x83 := dec(pow(82))
	text81, text82 := nines(81), nines(82)
	red81, red82 := mustDecimal(t, nines(81)+strings.Repeat("0", 10)), mustDecimal(t, nines(82)+strings.Repeat("0", 10))
	h100a, h100b := mustDecimal(t, "1"+strings.Repeat("0", 99)), mustDecimal(t, nines(99))
	num, den := mustDecimal(t, strings.Repeat("3", 600)), mustDecimal(t, strings.Repeat("1", 599))
	ctx := func(f func() (decimal.Decimal, decimal.Conditions, error)) func() (decimal.Decimal, error) {
		return func() (decimal.Decimal, error) { d, _, err := f(); return d, err }
	}
	quo600 := new(big.Rat).SetFrac(new(big.Int).Div(pow(600), big.NewInt(3)), new(big.Int).Div(pow(599), big.NewInt(9)))
	quo600Int := new(big.Int).Quo(quo600.Num(), quo600.Denom())
	for _, tc := range []struct {
		name   string
		op     func() (decimal.Decimal, error)
		want   string
		budget float64
	}{
		{"add/carry-81", func() (decimal.Decimal, error) { return x81.Add(one1) }, new(big.Int).Add(p80, one).String(), 1},
		{"add/nines-carry-81", func() (decimal.Decimal, error) { return n80e1.Add(one1) }, new(big.Int).Add(new(big.Int).Mul(new(big.Int).Sub(p80, one), big.NewInt(10)), one).String(), 1},
		{"add/80+80-81", func() (decimal.Decimal, error) { return x80.Add(y80) }, new(big.Rat).Add(ratOf(t, d80a), ratOf(t, d80b)).RatString(), 1},
		{"add/82", func() (decimal.Decimal, error) { return x82.Add(one1) }, new(big.Int).Add(p81, one).String(), 2},
		{"sub/borrow-81", func() (decimal.Decimal, error) { return x82.Sub(one1) }, b81.String(), 1},
		{"sub/82", func() (decimal.Decimal, error) { return x83.Sub(one1) }, b82.String(), 2},
		{"mul/41x41-81", func() (decimal.Decimal, error) { return p40.Mul(p40) }, p80.String(), 1},
		{"mul/41x41-82", func() (decimal.Decimal, error) { return p41.Mul(p41) }, new(big.Int).Mul(new(big.Int).Sub(pow(41), one), new(big.Int).Sub(pow(41), one)).String(), 2},
		{"quantize/81", ctx(func() (decimal.Decimal, decimal.Conditions, error) { return q60.Quantize(-21, decimal.TiesToEven) }), ratOf(t, strings.Repeat("7", 60)).RatString(), 1},
		{"quantize/82", ctx(func() (decimal.Decimal, decimal.Conditions, error) { return q60.Quantize(-22, decimal.TiesToEven) }), ratOf(t, strings.Repeat("7", 60)).RatString(), 2},
		{"context-stream/81", ctx(func() (decimal.Decimal, decimal.Conditions, error) { return x80.AddWithContext(y80, ctx81) }), new(big.Rat).Add(ratOf(t, d80a), ratOf(t, d80b)).RatString(), 1},
		{"context-stream/82", ctx(func() (decimal.Decimal, decimal.Conditions, error) { return x82.AddWithContext(one1, ctx82) }), new(big.Int).Add(p81, one).String(), 2},
		{"context-overflow/81", ctx(func() (decimal.Decimal, decimal.Conditions, error) { return top.MulWithContext(ten, g81) }), nines(81) + strings.Repeat("0", 19), 1},
		{"context-overflow/82", ctx(func() (decimal.Decimal, decimal.Conditions, error) { return top.MulWithContext(ten, g82) }), nines(82) + strings.Repeat("0", 18), 2},
		{"parse/81", func() (decimal.Decimal, error) { return decimal.Parse(text81) }, text81, 1},
		{"parse/82", func() (decimal.Decimal, error) { return decimal.Parse(text82) }, text82, 2},
		{"div-to-exponent/81", ctx(func() (decimal.Decimal, decimal.Conditions, error) {
			return x81.DivToExponent(one1, 0, decimal.TiesToEven)
		}), p80.String(), 1},
		{"div-to-exponent/82", ctx(func() (decimal.Decimal, decimal.Conditions, error) {
			return x82.DivToExponent(one1, 0, decimal.TiesToEven)
		}), p81.String(), 2},
		{"from-big-int/81", func() (decimal.Decimal, error) { return decimal.FromBigInt(b81) }, b81.String(), 1},
		{"from-big-int/82", func() (decimal.Decimal, error) { return decimal.FromBigInt(b82) }, b82.String(), 2},
		{"compose/81", func() (decimal.Decimal, error) {
			var d decimal.Decimal
			err := d.Compose(0, false, raw81, 0)
			return d, err
		}, b81.String(), 1},
		{"compose/82", func() (decimal.Decimal, error) {
			var d decimal.Decimal
			err := d.Compose(0, false, raw82, 0)
			return d, err
		}, b82.String(), 2},
		{"twos-complement/81", func() (decimal.Decimal, error) {
			return decimal.NewTwosComplement(lane81, binary.BigEndian, 0)
		}, b81.String(), 1},
		{"twos-complement/82", func() (decimal.Decimal, error) {
			return decimal.NewTwosComplement(lane82, binary.BigEndian, 0)
		}, b82.String(), 2},
		{"reduce/81", func() (decimal.Decimal, error) { return red81.Reduce(), nil }, nines(81) + strings.Repeat("0", 10), 1},
		{"reduce/82", func() (decimal.Decimal, error) { return red82.Reduce(), nil }, nines(82) + strings.Repeat("0", 10), 2},
		// Operand-bound rows: the result is inline, but the operation's own
		// buffer follows its operands (the operand envelope).
		{"operand/sub-cancel-100", func() (decimal.Decimal, error) { return h100a.Sub(h100b) }, "1", 1},
		{"operand/div-600-by-599", ctx(func() (decimal.Decimal, decimal.Conditions, error) {
			return num.DivToExponent(den, 0, decimal.TiesToEven)
		}), quo600Int.String(), 1},
	} {
		got, err := tc.op()
		if err != nil {
			t.Fatalf("%s: %v", tc.name, err)
		}
		if text, _ := got.Text(0); ratOf(t, text).Cmp(ratOf(t, tc.want)) != 0 {
			t.Fatalf("%s = %s, math/big %s", tc.name, text, tc.want)
		}
		if allocs := testing.AllocsPerRun(100, func() { sinkDecimal, _ = tc.op() }); allocs != tc.budget {
			t.Errorf("%s: %v allocs/op, class %v; allocation class exceeded or misstated", tc.name, allocs, tc.budget)
		}
	}
}
