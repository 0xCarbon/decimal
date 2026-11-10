// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"errors"
	"fmt"
	"math"
	"math/big"
	"math/rand/v2"
	"slices"
	"strconv"
	"strings"
	"testing"
)

// float64Oracle is the independent binary64 egress oracle: the exact value
// as a big.Rat, the floor on the binary64 grid by big.Float truncation (or
// integer division by 2^−1074 below 2^−1022), and the mode applied by
// exact comparison with the midpoint. It never uses big.Rat.Float64's
// exactness flag.
type float64Expect struct {
	value      float64
	conditions Conditions
}

var (
	oracleTwo1024   = new(big.Rat).SetInt(new(big.Int).Lsh(big.NewInt(1), 1024))
	oracleMinNormal = new(big.Rat).SetFrac(big.NewInt(1), new(big.Int).Lsh(big.NewInt(1), 1022))
	oracleQuantum   = new(big.Rat).SetFrac(big.NewInt(1), new(big.Int).Lsh(big.NewInt(1), 1074))
)

func float64Rat(f float64) *big.Rat {
	if math.IsInf(f, 0) {
		r := new(big.Rat).Set(oracleTwo1024)
		if f < 0 {
			r.Neg(r)
		}
		return r
	}
	return new(big.Rat).SetFloat64(f)
}

func oracleFloat64(value *big.Rat, mode RoundingMode) float64Expect {
	if value.Sign() == 0 {
		return float64Expect{}
	}
	negative := value.Sign() < 0
	magnitude := new(big.Rat).Abs(value)
	var conditions Conditions
	if magnitude.Cmp(oracleMinNormal) < 0 {
		conditions |= Subnormal
	}
	overflow := func() float64Expect {
		infinite := !(mode == TowardZero || mode == TowardPositiveInfinity && negative || mode == TowardNegativeInfinity && !negative)
		result := math.MaxFloat64
		if infinite {
			result = math.Inf(1)
		}
		direction := Decreased
		if infinite != negative {
			direction = Increased
		}
		if negative {
			result = -result
		}
		return float64Expect{result, Overflow | Inexact | Rounded | direction}
	}
	if magnitude.Cmp(oracleTwo1024) >= 0 {
		return overflow()
	}
	// floor on the binary64 grid, extended to MaxFloat64 below 2^1024.
	var floor float64
	if conditions&Subnormal != 0 {
		units := new(big.Rat).Quo(magnitude, oracleQuantum)
		k := new(big.Int).Quo(units.Num(), units.Denom())
		floor = math.Ldexp(float64(k.Int64()), -1074)
	} else {
		f, _ := new(big.Float).SetPrec(53).SetMode(big.ToZero).SetRat(magnitude).Float64()
		floor = f
	}
	floorRat := float64Rat(floor)
	if floorRat.Cmp(magnitude) == 0 {
		result := floor
		if negative {
			result = -result
		}
		return float64Expect{result, conditions}
	}
	ceil := math.Nextafter(floor, math.Inf(1))
	mid := new(big.Rat).Add(floorRat, float64Rat(ceil))
	mid.Quo(mid, big.NewRat(2, 1))
	half := magnitude.Cmp(mid)
	var up bool
	switch mode {
	case TowardZero:
	case AwayFromZero:
		up = true
	case TowardPositiveInfinity:
		up = !negative
	case TowardNegativeInfinity:
		up = negative
	case TiesToEven:
		up = half > 0 || half == 0 && math.Float64bits(floor)&1 == 1
	case TiesAwayFromZero:
		up = half >= 0
	case TiesTowardZero:
		up = half > 0
	}
	result := floor
	if up {
		result = ceil
		if math.IsInf(ceil, 1) {
			return overflow()
		}
	}
	direction := Decreased
	if up != negative {
		direction = Increased
	}
	conditions |= Inexact | Rounded | direction
	if conditions&Subnormal != 0 {
		conditions |= Underflow
	}
	if negative {
		result = -result
	}
	return float64Expect{result, conditions}
}

func checkFloat64(t *testing.T, label string, got float64, conditions Conditions, want float64Expect) {
	t.Helper()
	if math.Float64bits(got) != math.Float64bits(want.value) || conditions != want.conditions {
		t.Fatalf("%s: got (%v [%#x], %v), want (%v [%#x], %v)", label, got, math.Float64bits(got), conditions, want.value, math.Float64bits(want.value), want.conditions)
	}
}

func decimalRat(t *testing.T, d Decimal) *big.Rat {
	t.Helper()
	r, ok := new(big.Rat).SetString(d.String())
	if !ok {
		t.Fatalf("oracle cannot read %s", d)
	}
	return r
}

// randomFloat64Decimal draws decimals across and beyond the binary64
// range: short and long coefficients, exponents from the subnormal floor
// to past 2^1024, and exact expansions of random doubles and midpoints
// with one-unit neighbours.
func randomFloat64Decimal(rng *rand.Rand) Decimal {
	switch rng.IntN(4) {
	case 0: // exact double, its midpoint with the next, or a neighbour
		f := math.Float64frombits(rng.Uint64() &^ (1 << 63))
		if math.IsNaN(f) || math.IsInf(f, 0) {
			f = math.MaxFloat64
		}
		r := new(big.Rat).SetFloat64(f)
		if next := math.Nextafter(f, math.Inf(1)); rng.IntN(2) == 0 {
			r.Add(r, float64Rat(next)).Quo(r, big.NewRat(2, 1))
		}
		d := mustDecimalFromRat(r)
		if rng.IntN(3) == 0 {
			unit := New(int64(rng.IntN(3)-1), d.Exponent()-int32(rng.IntN(3)))
			d, _ = d.Add(unit)
		}
		if rng.IntN(2) == 0 {
			d = d.Neg()
		}
		return d
	default:
		digits := 1 + rng.IntN(40)
		if rng.IntN(8) == 0 {
			digits = 800 + rng.IntN(400)
		}
		var b strings.Builder
		if rng.IntN(2) == 0 {
			b.WriteByte('-')
		}
		b.WriteByte(byte('1' + rng.IntN(9)))
		for range digits - 1 {
			b.WriteByte(byte('0' + rng.IntN(10)))
		}
		adjusted := rng.IntN(700) - 345
		fmt.Fprintf(&b, "E%d", adjusted-digits+1)
		d, err := Parse(b.String())
		if err != nil {
			panic(err)
		}
		return d
	}
}

func mustDecimalFromRat(r *big.Rat) Decimal {
	d, err := FromRat(r)
	if err != nil {
		panic(err)
	}
	return d
}

// TestFloat64AgainstRationalOracle covers Float64's value, its exactness
// signal and its direction, overflow and underflow rules: every mode, against
// the independent oracle.
func TestFloat64AgainstRationalOracle(t *testing.T) {
	rng := rand.New(rand.NewPCG(47, 1))
	for range 12000 {
		d := randomFloat64Decimal(rng)
		exact := decimalRat(t, d)
		got, conditions := d.Float64()
		checkFloat64(t, fmt.Sprintf("Float64(%s)", d), got, conditions, oracleFloat64(exact, TiesToEven))
		mode := allDivModes[rng.IntN(len(allDivModes))]
		want := oracleFloat64(exact, mode)
		got, conditions, err := d.Float64Rounded(mode)
		if mode == Exact && want.conditions&Inexact != 0 {
			var ce *Error
			if !errors.As(err, &ce) || ce.Code != 0 || ce.Condition != Inexact || got != 0 {
				t.Fatalf("Float64Rounded(%s, Exact): (%v, %v, %v), want the Inexact refusal", d, got, conditions, err)
			}
			continue
		}
		if mode == Exact {
			want = oracleFloat64(exact, TowardZero)
		}
		if err != nil {
			t.Fatal(err)
		}
		checkFloat64(t, fmt.Sprintf("Float64Rounded(%s, %v)", d, mode), got, conditions, want)
	}
}

// TestFloat64EnclosureEveryExponentField checks directed egress: for every
// binary64 exponent field, values, midpoints and one-unit neighbours of
// midpoints are bracketed by TowardNegativeInfinity and
// TowardPositiveInfinity with adjacent doubles (or MaxFloat64 and +Inf),
// and each result matches the oracle.
func TestFloat64EnclosureEveryExponentField(t *testing.T) {
	rng := rand.New(rand.NewPCG(47, 2))
	for field := uint64(0); field <= 2046; field++ {
		for range 3 {
			f := math.Float64frombits(field<<52 | rng.Uint64()&(1<<52-1))
			next := math.Nextafter(f, math.Inf(1))
			mid := new(big.Rat).Add(float64Rat(f), float64Rat(next))
			mid.Quo(mid, big.NewRat(2, 1))
			m := mustDecimalFromRat(mid)
			unit := New(1, m.Exponent()-1)
			above, _ := m.Add(unit)
			below, _ := m.Sub(unit)
			exactF := mustDecimalFromRat(new(big.Rat).SetFloat64(f))
			for _, d := range []Decimal{exactF, m, above, below, m.Neg(), above.Neg()} {
				exact := decimalRat(t, d)
				lo, lc, _ := d.Float64Rounded(TowardNegativeInfinity)
				hi, hc, _ := d.Float64Rounded(TowardPositiveInfinity)
				checkFloat64(t, fmt.Sprintf("floor %s", d), lo, lc, oracleFloat64(exact, TowardNegativeInfinity))
				checkFloat64(t, fmt.Sprintf("ceil %s", d), hi, hc, oracleFloat64(exact, TowardPositiveInfinity))
				if float64Rat(lo).Cmp(exact) > 0 || float64Rat(hi).Cmp(exact) < 0 || lo != hi && math.Nextafter(lo, math.Inf(1)) != hi || lc&Increased != 0 || hc&Decreased != 0 {
					t.Fatalf("%s: enclosure (%v %v, %v %v)", d, lo, lc, hi, hc)
				}
				for _, mode := range []RoundingMode{TiesToEven, TiesAwayFromZero, TiesTowardZero, TowardZero, AwayFromZero} {
					got, c, _ := d.Float64Rounded(mode)
					checkFloat64(t, fmt.Sprintf("%s %v", d, mode), got, c, oracleFloat64(exact, mode))
				}
			}
		}
	}
}

// TestFloat64BoundaryVectors pins the subnormal and directed-rounding
// vectors, basic
// conversion vectors, and overflow and tie cases.
func TestFloat64BoundaryVectors(t *testing.T) {
	pow2 := func(k int) Decimal { // exact 2^k
		return mustDecimalFromRat(new(big.Rat).SetFloat64(math.Ldexp(1, k)))
	}
	half := func(k int) Decimal { // exact 2^k for k below the subnormal floor
		return mustDecimalFromRat(new(big.Rat).SetFrac(big.NewInt(1), new(big.Int).Lsh(big.NewInt(1), uint(-k))))
	}
	minSub := math.SmallestNonzeroFloat64
	maxHalfUlp := mustDecimalFromRat(new(big.Rat).Add(float64Rat(math.MaxFloat64), new(big.Rat).SetFrac(new(big.Int).Lsh(big.NewInt(1), 970), big.NewInt(1))))
	for _, tc := range []struct {
		name  string
		d     Decimal
		mode  RoundingMode
		value float64
		cond  Conditions
	}{
		{"0.5 exact", MustParse("0.5"), TiesToEven, 0.5, 0},
		{"2^53+1", MustParse("9007199254740993"), TiesToEven, 9007199254740992, Inexact | Rounded | Decreased},
		{"0.1", MustParse("0.1"), TiesToEven, 0.1, Inexact | Rounded | Increased},
		{"subnormal 2^-1074 exact", pow2(-1074), TiesToEven, minSub, Subnormal},
		{"subnormal -2^-1074 exact", pow2(-1074).Neg(), TiesToEven, -minSub, Subnormal},
		{"subnormal 2^-1075 tie to even", half(-1075), TiesToEven, 0, Inexact | Rounded | Decreased | Subnormal | Underflow},
		{"subnormal -2^-1075 tie to even", half(-1075).Neg(), TiesToEven, math.Copysign(0, -1), Inexact | Rounded | Increased | Subnormal | Underflow},
		{"subnormal 2^-1076 nearest", half(-1076), TiesToEven, 0, Inexact | Rounded | Decreased | Subnormal | Underflow},
		{"subnormal 2^-1076 ceiling", half(-1076), TowardPositiveInfinity, minSub, Inexact | Rounded | Increased | Subnormal | Underflow},
		{"subnormal -2^-1076 floor", half(-1076).Neg(), TowardNegativeInfinity, -minSub, Inexact | Rounded | Decreased | Subnormal | Underflow},
		{"directed 0.1 floor", MustParse("0.1"), TowardNegativeInfinity, math.Nextafter(0.1, 0), Inexact | Rounded | Decreased},
		{"directed 0.1 ceiling", MustParse("0.1"), TowardPositiveInfinity, 0.1, Inexact | Rounded | Increased},
		{"directed 1E+400 floor", MustParse("1E+400"), TowardNegativeInfinity, math.MaxFloat64, Overflow | Inexact | Rounded | Decreased},
		{"directed 1E+400 ceiling", MustParse("1E+400"), TowardPositiveInfinity, math.Inf(1), Overflow | Inexact | Rounded | Increased},
		{"directed -1E+400 floor", MustParse("-1E+400"), TowardNegativeInfinity, math.Inf(-1), Overflow | Inexact | Rounded | Decreased},
		{"directed -1E+400 ceiling", MustParse("-1E+400"), TowardPositiveInfinity, -math.MaxFloat64, Overflow | Inexact | Rounded | Increased},
		{"1E+400 toward zero", MustParse("1E+400"), TowardZero, math.MaxFloat64, Overflow | Inexact | Rounded | Decreased},
		{"2^1024 nearest", addExact(pow2(1023), pow2(1023)), TiesToEven, math.Inf(1), Overflow | Inexact | Rounded | Increased},
		{"Max+½ulp TiesToEven", maxHalfUlp, TiesToEven, math.Inf(1), Overflow | Inexact | Rounded | Increased},
		{"Max+½ulp TiesAwayFromZero", maxHalfUlp, TiesAwayFromZero, math.Inf(1), Overflow | Inexact | Rounded | Increased},
		{"Max+½ulp TiesTowardZero", maxHalfUlp, TiesTowardZero, math.MaxFloat64, Inexact | Rounded | Decreased},
		{"Max+½ulp TowardZero", maxHalfUlp, TowardZero, math.MaxFloat64, Inexact | Rounded | Decreased},
		{"Max+½ulp AwayFromZero", maxHalfUlp, AwayFromZero, math.Inf(1), Overflow | Inexact | Rounded | Increased},
		{"2^1024 toward zero", addExact(pow2(1023), pow2(1023)), TowardZero, math.MaxFloat64, Overflow | Inexact | Rounded | Decreased},
		{"largest subnormal + ½ulp", mustDecimalFromRat(new(big.Rat).Add(float64Rat(math.Float64frombits(1<<52-1)), new(big.Rat).Quo(oracleQuantum, big.NewRat(2, 1)))), TowardZero, math.Float64frombits(1<<52 - 1), Inexact | Rounded | Decreased | Subnormal | Underflow},
		{"2^-1022 exact is normal", pow2(-1022), TiesToEven, math.Ldexp(1, -1022), 0},
		{"zero", MustParse("0E-7"), TiesToEven, 0, 0},
		{"1E-400 away", MustParse("1E-400"), AwayFromZero, minSub, Inexact | Rounded | Increased | Subnormal | Underflow},
	} {
		got, conditions, err := tc.d.Float64Rounded(tc.mode)
		if err != nil || math.Float64bits(got) != math.Float64bits(tc.value) || conditions != tc.cond {
			t.Fatalf("%s: (%v, %v, %v), want (%v, %v)", tc.name, got, conditions, err, tc.value, tc.cond)
		}
		checkFloat64(t, tc.name+" oracle", got, conditions, oracleFloat64(decimalRat(t, tc.d), tc.mode))
	}
	if f, c := MustParse("0.1").Float64(); f != 0.1 || c != Inexact|Rounded|Increased {
		t.Fatalf("Float64(0.1) = (%v, %v)", f, c)
	}
	if _, _, err := MustParse("1").Float64Rounded(RoundingMode(99)); !errors.Is(err, ErrInvalidContext) {
		t.Fatalf("invalid mode: %v", err)
	}
}

// addExact is Add for test vectors that cannot fail.
func addExact(a, b Decimal) Decimal {
	sum, err := a.Add(b)
	if err != nil {
		panic(err)
	}
	return sum
}

// TestFloat64LongCoefficientSticky covers the prefix rule: a 10^5-digit
// coefficient whose only deciding digit is its last one rounds by that
// digit, in both directions from a midpoint.
func TestFloat64LongCoefficientSticky(t *testing.T) {
	for _, f := range []float64{1, 0.1, 1e300, 5e-324, math.MaxFloat64 / 3} {
		next := math.Nextafter(f, math.Inf(1))
		mid := new(big.Rat).Add(float64Rat(f), float64Rat(next))
		mid.Quo(mid, big.NewRat(2, 1))
		m := mustDecimalFromRat(mid)
		tail := New(1, m.Exponent()-100000)
		for _, d := range []Decimal{m, addExact(m, tail), addExact(m, tail.Neg())} {
			exact := decimalRat(t, d)
			for _, mode := range allDivModes[:7] {
				got, c, _ := d.Float64Rounded(mode)
				checkFloat64(t, fmt.Sprintf("%g mid %d digits %v", f, d.CoefficientDigits(), mode), got, c, oracleFloat64(exact, mode))
			}
			cmp, _ := d.CompareFloat64(next)
			if cmp != -1 {
				t.Fatalf("%g: long midpoint must be below the next double", f)
			}
		}
	}
}

// TestFloat64LongExactValue pins the prefix length: the longest binary64
// value (767 digits) padded with 1,000 zeros is still exact.
func TestFloat64LongExactValue(t *testing.T) {
	longest, _ := FromFloat64Exact(math.Float64frombits(1<<52 - 1))
	padded, _, err := longest.Quantize(longest.Exponent()-1000, Exact)
	if err != nil || padded.CoefficientDigits() <= 90*9 {
		t.Fatalf("padded: (%v digits, %v)", padded.CoefficientDigits(), err)
	}
	if f, c := padded.Float64(); f != math.Float64frombits(1<<52-1) || c != Subnormal {
		t.Fatalf("padded longest value: (%v, %v)", f, c)
	}
	if cmp, _ := padded.CompareFloat64(math.Float64frombits(1<<52 - 1)); cmp != 0 {
		t.Fatalf("padded longest value compares %d", cmp)
	}
	// The longest midpoint (768 digits) padded to every limb alignment, one
	// unit above at the last place: a prefix shorter than 768 digits plus
	// the two-decade margin would lose its deciding digits.
	f := math.Float64frombits(0x001FFFFFFFFFFFFF)
	mid := new(big.Rat).Add(float64Rat(f), float64Rat(math.Nextafter(f, 1)))
	mid.Quo(mid, big.NewRat(2, 1))
	m := mustDecimalFromRat(mid)
	if m.CoefficientDigits() != 768 {
		t.Fatalf("midpoint has %d digits", m.CoefficientDigits())
	}
	for pad := int32(790); pad < 810; pad++ {
		p, _, _ := m.Quantize(m.Exponent()-pad, Exact)
		for _, d := range []Decimal{p, addExact(p, New(1, p.Exponent())), addExact(p, New(-1, p.Exponent()))} {
			exact := decimalRat(t, d)
			for _, mode := range []RoundingMode{TiesToEven, TiesTowardZero, TowardZero} {
				got, c, _ := d.Float64Rounded(mode)
				checkFloat64(t, fmt.Sprintf("pad %d %v", pad, mode), got, c, oracleFloat64(exact, mode))
			}
		}
	}
}

// TestBinary64ExpansionDigitMaxima pins the bounds the stack buffers rest
// on: the longest binary64 value has 767 significant digits and the
// longest midpoint 768, both within 86 limbs.
func TestBinary64ExpansionDigitMaxima(t *testing.T) {
	var buf [binary64Limbs]uint32
	limbs, _ := expandDyadic(&buf, 1<<53-1, -1074)
	if got := limbsDigits(limbs); got != 767 {
		t.Fatalf("value maximum %d digits", got)
	}
	limbs, _ = expandDyadic(&buf, 1<<54-1, -1075)
	if got := limbsDigits(limbs); got != 768 || len(limbs) > 86 {
		t.Fatalf("midpoint maximum %d digits in %d limbs", got, len(limbs))
	}
	limbs, _ = expandDyadic(&buf, 1<<53-1, 971)
	if got := limbsDigits(limbs); got != 309 {
		t.Fatalf("MaxFloat64 %d digits", got)
	}
	for k := int64(-1100); k <= 1100; k++ { // ⌊k·log10 2⌋ exactly
		v := new(big.Float).SetPrec(400).SetMantExp(big.NewFloat(1), int(k))
		text := v.Text('e', 60)
		want, _ := strconv.ParseInt(text[strings.IndexByte(text, 'e')+1:], 10, 64)
		if got := dyadicAdjustedLow(k); got != want {
			t.Fatalf("⌊%d·log10 2⌋ = %d, want %d", k, got, want)
		}
	}
}

// TestCompareFloat64AgainstRationalOracle checks CompareFloat64:
// the sign of CompareFloat64 equals big.Rat's, across magnitudes, long
// coefficients and zeros, with the ±Inf order and the NaN error.
func TestCompareFloat64AgainstRationalOracle(t *testing.T) {
	rng := rand.New(rand.NewPCG(47, 3))
	for range 20000 {
		d := randomFloat64Decimal(rng)
		var f float64
		switch rng.IntN(3) {
		case 0:
			f, _ = d.Float64()
			if math.IsInf(f, 0) {
				f = math.Copysign(math.MaxFloat64, f)
			}
			if f = math.Nextafter(f, math.Inf(rng.IntN(3)-1)); math.IsInf(f, 0) {
				f = math.Copysign(math.MaxFloat64, f)
			}
		case 1:
			f = math.Float64frombits(rng.Uint64())
			if math.IsNaN(f) || math.IsInf(f, 0) {
				f = 0
			}
		default:
			f, _ = d.Float64()
			if math.IsInf(f, 0) {
				f = 0
			}
		}
		got, err := d.CompareFloat64(f)
		if want := decimalRat(t, d).Cmp(float64Rat(f)); err != nil || got != want {
			t.Fatalf("CompareFloat64(%s, %v) = (%d, %v), want %d", d, f, got, err, want)
		}
	}
	for _, tc := range []struct {
		d    string
		f    float64
		want int
	}{
		{"0.1", 0.1, -1}, {"9007199254740993", 9007199254740992, 1}, {"9007199254740992", 9007199254740992, 0},
		{"-9007199254740993", -9007199254740992, -1}, {"0", math.Copysign(0, -1), 0}, {"0E-9", 0, 0},
		{"1E+400", math.Inf(1), -1}, {"-1E+400", math.Inf(-1), 1}, {"0", 5e-324, -1}, {"-0.0", -5e-324, 1},
		{"12345678901234567890123456789012345678E-38", 0.12345678901234568, 1}, // Fraction oracle: the decimal is above the double
	} {
		got, err := MustParse(tc.d).CompareFloat64(tc.f)
		if err != nil || got != tc.want {
			t.Fatalf("CompareFloat64(%s, %v) = (%d, %v), want %d", tc.d, tc.f, got, err, tc.want)
		}
	}
	if _, err := MustParse("1").CompareFloat64(math.NaN()); !errors.Is(err, ErrInvalidOperation) {
		t.Fatalf("NaN: %v", err)
	}
	for scale := int32(0); scale <= 38; scale++ { // 38-digit coefficients at scales 0..38
		d := New(0, 0)
		c, _ := new(big.Int).SetString("12345678901234567890123456789012345678", 10)
		d, _ = FromBigInt(c)
		d = inlineDecimal(d.words, -scale, false)
		f, _ := d.Float64()
		for _, g := range []float64{f, math.Nextafter(f, 0), math.Nextafter(f, math.Inf(1))} {
			got, _ := d.CompareFloat64(g)
			if want := decimalRat(t, d).Cmp(float64Rat(g)); got != want {
				t.Fatalf("scale %d vs %v: %d, want %d", scale, g, got, want)
			}
		}
	}
}

// TestFromFloat64Regimes covers the two named regimes, their cohorts, signed
// zero and non-finite input.
func TestFromFloat64Regimes(t *testing.T) {
	exact, err := FromFloat64Exact(0.1)
	if err != nil || exact.String() != "0.1000000000000000055511151231257827021181583404541015625" {
		t.Fatalf("FromFloat64Exact(0.1) = (%v, %v)", exact, err)
	}
	shortest, err := FromFloat64(0.1)
	if err != nil || shortest.String() != "0.1" {
		t.Fatalf("FromFloat64(0.1) = (%v, %v)", shortest, err)
	}
	tiny, _ := FromFloat64Exact(math.SmallestNonzeroFloat64)
	if tiny.CoefficientDigits() != 751 || tiny.Exponent() != -1074 {
		t.Fatalf("SmallestNonzeroFloat64: %d digits at %d", tiny.CoefficientDigits(), tiny.Exponent())
	}
	if back, c := tiny.Float64(); back != math.SmallestNonzeroFloat64 || c != Subnormal {
		t.Fatalf("SmallestNonzeroFloat64 round trip: (%v, %v)", back, c)
	}
	for _, tc := range []struct {
		f               float64
		shortest, exact string
	}{
		{100, "100", "100"}, {1e21, "1000000000000000000000", "1000000000000000000000"}, {0.5, "0.5", "0.5"},
		{-2.5, "-2.5", "-2.5"}, {20, "20", "20"}, {math.Copysign(0, -1), "0", "0"}, {1.5, "1.5", "1.5"},
	} {
		s, err1 := FromFloat64(tc.f)
		e, err2 := FromFloat64Exact(tc.f)
		if err1 != nil || err2 != nil || s.String() != tc.shortest || e.String() != tc.exact || s.Exponent() > 0 || e.Exponent() > 0 {
			t.Fatalf("%v: shortest (%v, %v), exact (%v, %v)", tc.f, s, err1, e, err2)
		}
	}
	rng := rand.New(rand.NewPCG(47, 4))
	for range 20000 {
		f := math.Float64frombits(rng.Uint64())
		if math.IsNaN(f) || math.IsInf(f, 0) {
			continue
		}
		s, err := FromFloat64(f)
		if err != nil {
			t.Fatal(err)
		}
		want, _ := new(big.Rat).SetString(strconv.FormatFloat(f, 'e', -1, 64))
		if decimalRat(t, s).Cmp(want) != 0 || s.Exponent() > 0 {
			t.Fatalf("FromFloat64(%v) = %s", f, s)
		}
		if back, _ := s.Float64(); back != f && f != 0 {
			t.Fatalf("shortest round trip %v -> %s -> %v", f, s, back)
		}
		e, err := FromFloat64Exact(f)
		if err != nil || decimalRat(t, e).Cmp(new(big.Rat).SetFloat64(f)) != 0 {
			t.Fatalf("FromFloat64Exact(%v) = (%s, %v)", f, e, err)
		}
		if back, c := e.Float64(); back != f && f != 0 || c&Inexact != 0 {
			t.Fatalf("exact round trip %v -> (%v, %v)", f, back, c)
		}
	}
	for _, f := range []float64{math.NaN(), math.Inf(1), math.Inf(-1)} {
		for name, call := range map[string]func() error{
			"FromFloat64":           func() error { _, err := FromFloat64(f); return err },
			"FromFloat64Exact":      func() error { _, err := FromFloat64Exact(f); return err },
			"FromFloat64ToExponent": func() error { _, _, err := FromFloat64ToExponent(f, 0, TiesToEven); return err },
			"FromFloat64WithContext": func() error {
				_, _, err := FromFloat64WithContext(f, Decimal64Context())
				return err
			},
		} {
			if err := call(); !errors.Is(err, ErrConversionSyntax) {
				t.Fatalf("%s(%v): %v", name, f, err)
			}
		}
	}
	for _, text := range []string{"NaN", "Infinity", "-Infinity"} { // non-finite text is refused too
		if _, err := Parse(text); !errors.Is(err, ErrConversionSyntax) {
			t.Fatalf("Parse(%q): %v", text, err)
		}
	}
	// Refusal order: an unknown mode precedes the non-finite source.
	if _, _, err := FromFloat64ToExponent(math.NaN(), 0, RoundingMode(99)); !errors.Is(err, ErrInvalidContext) {
		t.Fatalf("NaN with unknown mode: %v", err)
	}
}

// TestFromFloat64RoundedAgainstRationalOracle covers rounded binary64
// ingress against the division oracles on the double's exact rational, and
// the differential with FromRat under a zero budget, in every mode,
// guarded and unguarded.
func TestFromFloat64RoundedAgainstRationalOracle(t *testing.T) {
	rng := rand.New(rand.NewPCG(47, 5))
	for range 12000 {
		f := math.Float64frombits(rng.Uint64())
		if math.IsNaN(f) || math.IsInf(f, 0) || f == 0 {
			continue
		}
		r := new(big.Rat).SetFloat64(f)
		mode := allDivModes[rng.IntN(len(allDivModes))]
		target := int64(rng.IntN(2200) - 1400)
		if rng.IntN(2) == 0 { // near the value's own scale
			target = int64(math.Floor(math.Log10(math.Abs(f)))) - int64(rng.IntN(40))
		}
		got, conditions, err := FromFloat64ToExponent(f, int32(target), mode)
		label := fmt.Sprintf("%v t=%d %v", f, target, mode)
		checkDivOutcome(t, label, got, conditions, err, oracleToExponent(r, 0, target, mode), f < 0)
		rg, rc, re := FromRatToExponent(r, int32(target), mode)
		if (err == nil) != (re == nil) || err == nil && (!got.Equal(rg) || got.Exponent() != rg.Exponent() || conditions != rc) {
			t.Fatalf("%s: FromRat differential (%v, %v, %v)", label, rg, rc, re)
		}
		p := int64(1 + rng.IntN(60))
		var ctx Context
		var want divExpect
		if rng.IntN(2) == 0 {
			ctx, _ = NewContext(uint32(p), mode, nil, 0)
			want = oracleContext(r, 0, p, mode)
		} else {
			emin := int64(rng.IntN(700) - 400)
			emax := emin + int64(rng.IntN(700))
			ctx, _ = NewContext(uint32(p), mode, &ExponentGuards{Emin: int32(emin), Emax: int32(emax)}, 0)
			want = oracleGuarded(r, 0, p, emin, emax, mode)
		}
		got, conditions, err = FromFloat64WithContext(f, ctx)
		checkDivOutcome(t, fmt.Sprintf("%v p=%d %v", f, p, mode), got, conditions, err, want, f < 0)
		rg, rc, re = FromRatWithContext(r, ctx)
		if (err == nil) != (re == nil) || err == nil && (!got.Equal(rg) || got.Exponent() != rg.Exponent() || conditions != rc) {
			t.Fatalf("%v p=%d: FromRat differential (%v, %v, %v)", f, p, rg, rc, re)
		}
	}
	for _, tc := range []struct {
		f      float64
		target int32
		mode   RoundingMode
		want   string
	}{
		{2.675, -2, TiesToEven, "2.67"}, {0.125, -2, TiesToEven, "0.12"}, {0.125, -2, TiesAwayFromZero, "0.13"},
		{1e-300, -2, TiesToEven, "0.00"}, {1e-300, -2, TowardPositiveInfinity, "0.01"}, {-1e-300, -2, TowardNegativeInfinity, "-0.01"},
		{math.Ldexp(1, -183), -55, TiesToEven, "1E-55"},
	} {
		got, _, err := FromFloat64ToExponent(tc.f, tc.target, tc.mode)
		if err != nil || got.String() != tc.want {
			t.Fatalf("FromFloat64ToExponent(%v, %d, %v) = (%v, %v), want %s", tc.f, tc.target, tc.mode, got, err, tc.want)
		}
	}
}

// TestFromFloat64ContextWorkIndependentOfPrecision covers the exact-first
// rule: at the largest precisions the exact
// expansion is published with memory bounded by its own size.
func TestFromFloat64ContextWorkIndependentOfPrecision(t *testing.T) {
	for _, f := range []float64{math.SmallestNonzeroFloat64, 0.1, -1e300, math.MaxFloat64} {
		for _, guards := range []*ExponentGuards{nil, {Emin: -2000, Emax: 2000}} {
			precision := uint32(math.MaxUint32)
			if guards != nil {
				precision = uint32(int64(guards.Emin) - math.MinInt32 + 1)
			}
			ctx, err := NewContext(precision, TiesToEven, guards, 0)
			if err != nil {
				t.Fatal(err)
			}
			got, conditions, err := FromFloat64WithContext(f, ctx)
			bytes := coldAllocatedWithin(func() { _, _, _ = FromFloat64WithContext(f, ctx) }, 8<<10)
			want, _ := FromFloat64Exact(f)
			if err != nil || conditions != 0 || !got.Equal(want) || got.Exponent() != want.Exponent() {
				t.Fatalf("%v: (%v, %v, %v), want %v", f, got, conditions, err, want)
			}
			if bytes > 8<<10 {
				t.Fatalf("%v: allocated %d bytes", f, bytes)
			}
		}
	}
}

// TestFromFloat64ToExponentTariff pins the tariff B = P·87 + ⌈pad/9⌉ at
// values computed outside the code:
// B−1 and W−1 refuse, W admits, and the digit quota refuses at N−1 before
// the pad is allocated.
func TestFromFloat64ToExponentTariff(t *testing.T) {
	for _, tc := range []struct {
		f      float64
		target int32
		charge uint64
		digits uint64
	}{
		{0.1, -60, 436, 60},              // e = −55: 5 passes, pad 5
		{0.1, -2, 435, 2},                // drop to 0.10
		{1e300, 0, 2871, 301},            // e = 946: 33 passes, no pad
		{5e-324, -2000, 7324, 1677},      // e = −1074: 83 passes, pad 926
		{0.5, -1, 87, 1},                 // e = −1: one pass (−e ≡ 1 mod 13)
		{3.0517578125e-05, -20, 175, 16}, // 2^−15: 2 passes, pad 5
	} {
		full, _, err := FromFloat64ToExponent(tc.f, tc.target, TiesToEven)
		if err != nil || full.CoefficientDigits() != tc.digits {
			t.Fatalf("%v at %d: (%v, %v), want %d digits", tc.f, tc.target, full, err, tc.digits)
		}
		w := tc.charge + 2*tc.digits + 1
		for _, b := range []Budget{{MaxWork: tc.charge - 1}, {MaxWork: w - 1}, {MaxDigits: tc.digits - 1}} {
			if b == (Budget{}) { // a zero quota means no limit
				continue
			}
			if _, _, err := FromFloat64ToExponentWithBudget(tc.f, tc.target, TiesToEven, b); !errors.Is(err, ErrInsufficientStorage) {
				t.Fatalf("%v at %d under %+v: %v", tc.f, tc.target, b, err)
			}
			// B−1 and N−1 refuse before any allocation but the error, and so
			// does W−1 when padding (its digit count is final).
			if b.MaxWork != w-1 || int64(tc.target) < min(binary64Exponent(tc.f), 0) {
				if allocs := testing.AllocsPerRun(5, func() { _, _, _ = FromFloat64ToExponentWithBudget(tc.f, tc.target, TiesToEven, b) }); allocs > 1 {
					t.Fatalf("%v at %d under %+v allocated %v times", tc.f, tc.target, b, allocs)
				}
			}
		}
		got, _, err := FromFloat64ToExponentWithBudget(tc.f, tc.target, TiesToEven, Budget{MaxWork: w, MaxDigits: tc.digits})
		if err != nil || !got.Equal(full) {
			t.Fatalf("%v at %d at W: (%v, %v)", tc.f, tc.target, got, err)
		}
	}
	zero, _, err := FromFloat64ToExponentWithBudget(0, -2, TiesToEven, Budget{MaxWork: 4})
	if err != nil || zero.String() != "0.00" {
		t.Fatalf("zero at W = 4: (%v, %v)", zero, err)
	}
	if _, _, err := FromFloat64ToExponentWithBudget(0, -2, TiesToEven, Budget{MaxWork: 3}); !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("zero at 3: %v", err)
	}
}

// binary64Exponent is e of the double's odd-significand form ±m·2^e.
func binary64Exponent(f float64) int64 {
	_, _, e := binary64Parts(f)
	return e
}

// TestBinary64Allocations covers the binary64 allocation criterion on
// success paths: egress and comparison allocate nothing for inline and
// slow values, and ingress allocates nothing for inline results.
func TestBinary64Allocations(t *testing.T) {
	inline := MustParse("12345678901234567890.123456789")
	slow := MustParse(strings.Repeat("7", 2000) + "E-1900")
	ctx := Decimal64Context()
	for name, f := range map[string]func(){
		"Float64 inline":         func() { _, _ = inline.Float64() },
		"Float64 slow":           func() { _, _ = slow.Float64() },
		"Float64Rounded floor":   func() { _, _, _ = inline.Float64Rounded(TowardNegativeInfinity) },
		"CompareFloat64 inline":  func() { _, _ = inline.CompareFloat64(1.2345678901234567e19) },
		"CompareFloat64 slow":    func() { _, _ = slow.CompareFloat64(7.7e99) },
		"FromFloat64":            func() { _, _ = FromFloat64(0.1) },
		"FromFloat64Exact 0.5":   func() { _, _ = FromFloat64Exact(0.5) },
		"FromFloat64ToExponent":  func() { _, _, _ = FromFloat64ToExponent(2.675, -2, TiesToEven) },
		"FromFloat64WithContext": func() { _, _, _ = FromFloat64WithContext(0.1, ctx) },
		"pad 7 at -2":            func() { _, _, _ = FromFloat64ToExponent(7, -2, TiesToEven) },
		"pad 1.5 at -2":          func() { _, _, _ = FromFloat64ToExponent(1.5, -2, TiesToEven) },
		"pad 100 at -2":          func() { _, _, _ = FromFloat64ToExponent(100, -2, TiesToEven) },
		"pad 2.5 at -4":          func() { _, _, _ = FromFloat64ToExponent(2.5, -4, TiesToEven) },
		"pad 0.5 at -3":          func() { _, _, _ = FromFloat64ToExponent(0.5, -3, TiesToEven) },
	} {
		if allocs := testing.AllocsPerRun(50, f); allocs != 0 {
			t.Fatalf("%s allocated %v times", name, allocs)
		}
	}
	// A 100-digit pad is built in the stack expansion buffer: only the
	// published holder and its limbs are allocated.
	if allocs := testing.AllocsPerRun(50, func() { _, _, _ = FromFloat64ToExponent(1, -99, TiesToEven) }); allocs != 2 {
		t.Fatalf("100-digit pad allocated %v times, want 2", allocs)
	}
}

// BenchmarkBinary64 is a smoke benchmark: egress,
// comparison and ingress on inline values and one 767-digit subnormal.
func BenchmarkBinary64(b *testing.B) {
	money := MustParse("12345.67")
	long, _ := FromFloat64Exact(math.Float64frombits(1<<52 - 1))
	for _, bc := range []struct {
		name string
		f    func()
	}{
		{"Float64-money", func() { _, _ = money.Float64() }},
		{"Float64-subnormal767", func() { _, _ = long.Float64() }},
		{"Float64Rounded-floor-money", func() { _, _, _ = money.Float64Rounded(TowardNegativeInfinity) }},
		{"CompareFloat64-money", func() { _, _ = money.CompareFloat64(12345.67) }},
		{"FromFloat64-0.1", func() { _, _ = FromFloat64(0.1) }},
		{"FromFloat64Exact-0.1", func() { _, _ = FromFloat64Exact(0.1) }},
		{"FromFloat64ToExponent-cast", func() { _, _, _ = FromFloat64ToExponent(2.675, -2, TiesToEven) }},
		{"FromFloat64WithContext-d64", func() { _, _, _ = FromFloat64WithContext(0.1, Decimal64Context()) }},
	} {
		b.Run(bc.name, func(b *testing.B) {
			b.ReportAllocs()
			for b.Loop() {
				bc.f()
			}
		})
	}
}

// TestBinary64AnchorBoundaryCorpus is a differential test in both
// directions over the binary64 boundary corpus: for the smallest, largest
// and a middle significand of every exponent field, the exact expansion
// equals big.Rat's, rounded ingress at the value's own decades equals the
// division oracle, the expansion converts back exactly, and the midpoint
// with the next double converts by the egress oracle in every mode.
func TestBinary64AnchorBoundaryCorpus(t *testing.T) {
	for field := uint64(0); field <= 2046; field++ {
		for _, fraction := range []uint64{0, 1, 1 << 51, 1<<52 - 1} {
			f := math.Float64frombits(field<<52 | fraction)
			if f == 0 {
				continue
			}
			r := new(big.Rat).SetFloat64(f)
			exact, err := FromFloat64Exact(f)
			if err != nil || decimalRat(t, exact).Cmp(r) != 0 {
				t.Fatalf("FromFloat64Exact(%v) = (%v, %v)", f, exact, err)
			}
			if back, c := exact.Float64(); back != f || c&Inexact != 0 {
				t.Fatalf("round trip %v -> (%v, %v)", f, back, c)
			}
			decade := int64(math.Floor(math.Log10(f)))
			for _, target := range []int64{decade - 17, decade - 1, decade + 1} {
				for _, mode := range []RoundingMode{TiesToEven, TowardNegativeInfinity, AwayFromZero} {
					got, conditions, err := FromFloat64ToExponent(f, int32(target), mode)
					checkDivOutcome(t, fmt.Sprintf("%v t=%d %v", f, target, mode), got, conditions, err, oracleToExponent(r, 0, target, mode), false)
				}
			}
			next := math.Nextafter(f, math.Inf(1))
			mid := new(big.Rat).Add(r, float64Rat(next))
			mid.Quo(mid, big.NewRat(2, 1))
			m := mustDecimalFromRat(mid)
			for _, mode := range allDivModes[:7] {
				got, c, _ := m.Float64Rounded(mode)
				checkFloat64(t, fmt.Sprintf("mid %v %v", f, mode), got, c, oracleFloat64(mid, mode))
			}
		}
	}
}

// float64BoundaryGap returns the distance from r > 0 to the nearest
// binary64 rounding boundary (a double or a midpoint between adjacent
// doubles), relative to r, as a float64; ok is false beyond MaxFloat64.
func float64BoundaryGap(r *big.Rat) (gap float64, ok bool) {
	f, _ := r.Float64()
	if math.IsInf(f, 0) || f >= math.MaxFloat64 {
		return 0, false
	}
	b := math.Float64bits(f)
	best := new(big.Rat)
	first := true
	for i := max(b, 1) - 1; i <= b+1; i++ {
		v := float64Rat(math.Float64frombits(i))
		points := []*big.Rat{v}
		if i < b+1 {
			half := new(big.Rat).Add(v, float64Rat(math.Float64frombits(i+1)))
			points = append(points, half.Quo(half, big.NewRat(2, 1)))
		}
		for _, p := range points {
			d := new(big.Rat).Sub(r, p)
			d.Abs(d)
			if first || d.Cmp(best) < 0 {
				best, first = d, false
			}
		}
	}
	gap, _ = best.Quo(best, r).Float64()
	return gap, true
}

// TestFloat64WorkBoundedAcrossExponents pins the egress work bound.
// Float64 and CompareFloat64 do at most one exact dyadic comparison
// whatever the exponent, and none when the value is more than 2^−58
// (relative) from every rounding boundary or from the compared double.
// That gap lies between the 2^−59 enclosure width and the 2^−54 half-ulp
// cell, so it covers most normal values; a guard requires it to. Each
// comparison spends between one and 3·binary64Limbs limb products, the
// tabulated expansion's bound, never a pass per power. The gaps come from
// math/big.
func TestFloat64WorkBoundedAcrossExponents(t *testing.T) {
	rng := rand.New(rand.NewPCG(61, 1))
	var floatCovered, compareCovered int
	checkWork := func(label string, work dyadicWork, gap float64, far bool) {
		t.Helper()
		switch {
		case work.compares > 1:
			t.Fatalf("%s: %d exact comparisons", label, work.compares)
		case far && gap > 0x1p-58 && work.compares != 0:
			t.Fatalf("%s: an exact comparison %.3g from every boundary", label, gap)
		case work.compares == 1 && (work.products == 0 || work.products > 3*binary64Limbs):
			t.Fatalf("%s: %d limb products for one comparison", label, work.products)
		case work.compares == 0 && work.products != 0:
			t.Fatalf("%s: %d limb products without a comparison", label, work.products)
		}
	}
	check := func(d Decimal) {
		t.Helper()
		exact := decimalRat(t, d)
		exact.Abs(exact)
		gap, inRange := float64BoundaryGap(exact)
		for _, mode := range []RoundingMode{TiesToEven, TowardZero, AwayFromZero} {
			_, _, work := d.float64Work(mode)
			checkWork(fmt.Sprintf("Float64Rounded(%s, %v)", d, mode), work, gap, inRange)
		}
		if inRange && gap > 0x1p-58 {
			floatCovered++
		}
		f, _ := exact.Float64()
		f = math.Nextafter(f, 0)
		if d.Sign() < 0 {
			f = -f
		}
		_, work, err := d.compareFloat64Work(f)
		if err != nil {
			t.Fatal(err)
		}
		apart := new(big.Rat).Sub(exact, new(big.Rat).Abs(float64Rat(f)))
		g, _ := apart.Abs(apart).Quo(apart, exact).Float64()
		checkWork(fmt.Sprintf("CompareFloat64(%s, %v)", d, f), work, g, true)
		if g > 0x1p-58 && f != 0 {
			compareCovered++
		}
	}
	for e := int32(-340); e <= 302; e++ {
		check(New(1234567, e))
		check(New(-5, e))
		check(MustParse(fmt.Sprintf("123456789012345678E%d", e-11)))
	}
	for range 3000 {
		check(randomFloat64Decimal(rng))
	}
	if floatCovered < 2000 || compareCovered < 2000 {
		t.Fatalf("vacuous: %d Float64 and %d CompareFloat64 checks beyond 2^-58", floatCovered, compareCovered)
	}
}

// TestFloat64MatchesStrconv checks Float64 against strconv.ParseFloat of
// the decimal's own text over random decimals across and beyond the
// binary64 range, a second independent oracle for the bounded path.
func TestFloat64MatchesStrconv(t *testing.T) {
	rng := rand.New(rand.NewPCG(61, 5))
	for range 20000 {
		d := randomFloat64Decimal(rng)
		want, _ := strconv.ParseFloat(d.String(), 64)
		if got, _ := d.Float64(); math.Float64bits(got) != math.Float64bits(want) {
			t.Fatalf("Float64(%s) = %v, strconv %v", d, got, want)
		}
	}
}

// binary64BoundaryCorpus returns decimals on and next to binary64 rounding
// boundaries: exact doubles, midpoints, and midpoints one unit in their
// last digit away, across every exponent field, plus the overflow and
// underflow edges.
func binary64BoundaryCorpus(rng *rand.Rand) []Decimal {
	var out []Decimal
	add := func(r *big.Rat) {
		m := mustDecimalFromRat(r)
		unit := New(1, m.Exponent()-1)
		above, _ := m.Add(unit)
		below, _ := m.Sub(unit)
		out = append(out, m, above, below)
	}
	half := big.NewRat(1, 2)
	for field := uint64(0); field <= 2046; field += 3 {
		f := math.Float64frombits(field<<52 | rng.Uint64()&(1<<52-1))
		next := math.Nextafter(f, math.Inf(1))
		mid := new(big.Rat).Add(float64Rat(f), float64Rat(next))
		add(float64Rat(f))
		add(mid.Mul(mid, half))
	}
	top := new(big.Rat).SetInt(new(big.Int).Lsh(big.NewInt(1), 1024))
	maxMid := new(big.Rat).Add(float64Rat(math.MaxFloat64), top)
	add(top)
	add(maxMid.Mul(maxMid, half))
	add(new(big.Rat).SetFrac(big.NewInt(1), new(big.Int).Lsh(big.NewInt(1), 1075)))
	// 2^60·10^22 is an exact double held in limbs (41 digits); adding
	// 10^(k−1) leaves a nonzero digit in the partial limb or the tail that
	// only sticky reports.
	anchor := new(big.Int).Mul(new(big.Int).Lsh(big.NewInt(1), 60), new(big.Int).Exp(big.NewInt(10), big.NewInt(22), nil))
	for _, k := range []int64{1, 2, 5, 9, 10, 11, 18, 19, 21, 22, 30, 40} {
		v := new(big.Int).Add(anchor, new(big.Int).Exp(big.NewInt(10), big.NewInt(k-1), nil))
		out = append(out, MustParse(v.String()), MustParse(v.String()+"E-340"))
	}
	for _, text := range []string{"0.5", "0.25", "12345.5", "1E22", "1E23", "1E308", "9E308", "1E-363", "5E-324", "2.5E-324", "9007199254740993", "1.7976931348623157E308"} {
		out = append(out, MustParse(text))
	}
	return out
}

// TestBinary64PlaceBoundedMatchesGeneral pins the bounded placement
// to the general search over random decimals and the boundary
// corpus: the same bit pattern and class whenever it answers, and it
// always answers. The guard requires every branch — the enclosure alone,
// one exact comparison, an exact product — to be exercised.
func TestBinary64PlaceBoundedMatchesGeneral(t *testing.T) {
	rng := rand.New(rand.NewPCG(61, 2))
	inputs := binary64BoundaryCorpus(rng)
	for range 20000 {
		inputs = append(inputs, randomFloat64Decimal(rng))
	}
	var interior, compared, exact int
	for _, d := range inputs {
		if d.isZero() {
			continue
		}
		got, work, ok := d.binary64PlaceBounded()
		if !ok {
			t.Fatalf("%s: bounded placement declined", d)
		}
		want, _ := d.binary64PlaceGeneral()
		if got != want {
			t.Fatalf("%s: bounded %+v, general %+v", d, got, want)
		}
		if work.compares > 1 {
			t.Fatalf("%s: %d exact comparisons", d, work.compares)
		}
		w, sticky, tt, q, verdict := binary64Lead(d)
		if verdict != 0 {
			continue
		}
		lo, hi, isExact, e := binary64Enclosure(w, sticky, tt, q)
		posLo, _ := binary64Position(lo, e)
		posHi, _ := binary64Position(hi, e)
		switch {
		case isExact:
			exact++
		case posLo == posHi:
			interior++
		default:
			compared++
		}
	}
	if interior < 10000 || compared < 1000 || exact < 20 {
		t.Fatalf("vacuous: %d by enclosure, %d by one comparison, %d exact", interior, compared, exact)
	}
}

// TestCompareBinary64MatchesGeneral pins the bounded CompareFloat64
// core to the exact dyadic comparison over random and boundary decimals
// against their nearest doubles and those doubles' neighbours, with a
// guard that both the enclosure and the exact fallback decide cases.
func TestCompareBinary64MatchesGeneral(t *testing.T) {
	rng := rand.New(rand.NewPCG(61, 3))
	inputs := binary64BoundaryCorpus(rng)
	for range 5000 {
		inputs = append(inputs, randomFloat64Decimal(rng))
	}
	var decided, fallback int
	for _, d := range inputs {
		if d.isZero() {
			continue
		}
		f, _ := d.Abs().Float64()
		for _, g := range []float64{f, math.Nextafter(f, 0), math.Nextafter(f, math.Inf(1))} {
			if g == 0 || math.IsInf(g, 0) {
				continue
			}
			_, m, e := binary64Parts(g)
			got, work := d.compareBinary64(m, e)
			c := newDyadicComparer(d)
			if want := c.compare(m, e); got != want {
				t.Fatalf("|%s| vs %v: bounded %d, exact %d", d, g, got, want)
			}
			if work.compares == 0 {
				decided++
			} else {
				fallback++
			}
		}
	}
	if decided < 10000 || fallback < 500 {
		t.Fatalf("vacuous: %d by enclosure, %d by exact comparison", decided, fallback)
	}
}

// TestExpandDyadicPointMatchesExpansion pins the table expansion to
// the pass-by-pass expandDyadic for every exponent an egress comparison
// meets, with the smallest, largest and random significands, and checks
// the 5^(13j) and 2^(29j) limb tables against math/big.
func TestExpandDyadicPointMatchesExpansion(t *testing.T) {
	billion := big.NewInt(1_000_000_000)
	check := func(name string, first, count int, base, step int64) {
		for j := range count {
			p := new(big.Int).Exp(big.NewInt(base), big.NewInt(step*int64(j)), nil)
			for _, limb := range float64DyadicLimbs[float64DyadicOffsets[first+j]:float64DyadicOffsets[first+j+1]] {
				var r big.Int
				p.QuoRem(p, billion, &r)
				if r.Uint64() != uint64(limb) {
					t.Fatalf("%s table power %d: limb %d, want %d", name, j, limb, r.Uint64())
				}
			}
			if p.Sign() != 0 {
				t.Fatalf("%s table power %d is short", name, j)
			}
		}
	}
	check("five", 0, float64TwoPowers, 5, 13)
	check("two", float64TwoPowers, len(float64DyadicOffsets)-1-float64TwoPowers, 2, 29)
	rng := rand.New(rand.NewPCG(61, 4))
	for e := int64(-1075); e <= 1024; e++ {
		for _, m := range []uint64{1, 3, 1<<53 - 1, 1<<55 - 1, rng.Uint64() >> 9} {
			var a, b [binary64Limbs]uint32
			want, wx := expandDyadic(&a, m, e)
			got, gx, products := expandDyadicPoint(&b, m, e)
			if gx != wx || !slices.Equal(got, want) {
				t.Fatalf("%d·2^%d: table %v at %d, passes %v at %d", m, e, got, gx, want, wx)
			}
			if products == 0 || products > 3*binary64Limbs {
				t.Fatalf("%d·2^%d: %d limb products", m, e, products)
			}
		}
	}
}

// TestBinary64PlaceSmallMatchesGeneral pins the one-division placement to
// the bounded and general placements, Float64 to strconv, and CompareFloat64
// to the enclosure comparison, over random and boundary money-shaped values.
func TestBinary64PlaceSmallMatchesGeneral(t *testing.T) {
	rng := rand.New(rand.NewPCG(13, 17))
	classes := map[divHalf]int{}
	for i := range 200000 {
		var w uint64
		switch rng.IntN(5) {
		case 0:
			w = 1 + rng.Uint64N(1<<53-1)
		case 1:
			w = 1 + rng.Uint64N(100_000_000)
		case 2:
			w = 1<<uint(rng.IntN(53)) + uint64(rng.IntN(3)) - 1
		case 3:
			// a multiple of 5^k·2^j: exact quotients
			w = (1 + rng.Uint64N(1<<20)) * pow10Words[rng.IntN(10)]
		default:
			w = 1<<53 - 1 - rng.Uint64N(1000)
		}
		if w == 0 || w >= 1<<53 {
			continue
		}
		d := inlineDecimal(uint128{lo: w}, int32(-rng.IntN(23)), rng.IntN(2) == 0)
		got, ok := d.binary64PlaceSmall()
		if !ok {
			t.Fatalf("%v: not taken", d)
		}
		want, _, ok := d.binary64PlaceBounded()
		if !ok {
			want, _ = d.binary64PlaceGeneral()
		}
		if got != want {
			t.Fatalf("%v: place %+v, bounded %+v", d, got, want)
		}
		classes[got.class]++
		if i%64 == 0 {
			if general, _ := d.binary64PlaceGeneral(); got != general {
				t.Fatalf("%v: place %+v, general %+v", d, got, general)
			}
			f, _ := d.Float64()
			if s, _ := strconv.ParseFloat(d.String(), 64); f != s {
				t.Fatalf("%v: Float64 %v, strconv %v", d, f, s)
			}
		}
		// CompareFloat64 against the nearest double and its neighbours.
		f, _ := d.Float64()
		for _, x := range []float64{f, math.Nextafter(f, math.Inf(1)), math.Nextafter(f, math.Inf(-1)), -f, f * 3, f / 3, float64(rng.Int64N(1000)) / 100} {
			gotCmp, err := d.CompareFloat64(x)
			if err != nil {
				t.Fatal(err)
			}
			negative, m, e := binary64Parts(x)
			var wantCmp int
			switch {
			case m == 0 || negative != d.negative():
				wantCmp = 1
				if d.negative() {
					wantCmp = -1
				}
			default:
				wantCmp, _ = d.compareBinary64(m, e)
				if d.negative() {
					wantCmp = -wantCmp
				}
			}
			if gotCmp != wantCmp {
				t.Fatalf("%v vs %v: CompareFloat64 %d, enclosure %d", d, x, gotCmp, wantCmp)
			}
		}
	}
	if classes[divExactClass] < 100 || classes[divBelow] < 1000 || classes[divAbove] < 1000 {
		t.Fatalf("vacuous path coverage: %v", classes)
	}
	// Shapes outside the path defer.
	for _, d := range []Decimal{New(1, 1), New(1, -23), New(1<<53, -2), inlineDecimal(uint128{1, 1}, -2, false)} {
		if _, ok := d.binary64PlaceSmall(); ok {
			t.Fatalf("%v: taken", d)
		}
	}
}

// ingressFloat draws doubles shaped like money, integers, halves, dyadic
// fractions and arbitrary bit patterns, of either sign.
func ingressFloat(rng *rand.Rand) float64 {
	var f float64
	switch rng.IntN(8) {
	case 0:
		f = float64(rng.Int64N(100_000_000_000)) / 100
	case 1:
		f = float64(rng.Int64N(1 << 53))
	case 2:
		f = math.Float64frombits(rng.Uint64())
	case 3:
		f = float64(rng.Int64N(1000)) + 0.5
	case 4:
		f = math.Ldexp(float64(1+rng.Int64N(1<<20)), rng.IntN(140)-70)
	case 5:
		f = float64(rng.Int64N(1_000_000)) / float64(pow10Words[rng.IntN(10)])
	case 6:
		f = math.Ldexp(float64(rng.Int64N(1<<53)), rng.IntN(80))
	default:
		f = float64(rng.IntN(2000)) / 8
	}
	if rng.IntN(2) == 0 {
		f = -f
	}
	return f
}

// TestFromFloat64InlineMatchesGeneral pins FromFloat64's integer path to
// the shortest-text path and FromFloat64ToExponent's shift path to the limb
// expansion, with the conditions and every refusal.
func TestFromFloat64InlineMatchesGeneral(t *testing.T) {
	rng := rand.New(rand.NewPCG(47, 53))
	integers, taken, inexact, ties := 0, 0, 0, 0
	for range 200000 {
		f := ingressFloat(rng)
		if math.IsNaN(f) || math.IsInf(f, 0) {
			continue
		}
		if i := rng.IntN(4); i == 0 {
			got, err := FromFloat64(f)
			var want Decimal
			var werr error
			if f != 0 {
				var buf [32]byte
				if werr = want.UnmarshalText(strconv.AppendFloat(buf[:0], f, 'e', -1, 64)); werr == nil && want.exponent() > 0 {
					want, _, werr = want.Quantize(0, Exact)
				}
			}
			requireSameOutcome(t, "FromFloat64", strconv.FormatFloat(f, 'g', -1, 64), got, 0, err, want, 0, werr)
			if f != 0 && math.Abs(f) < 1<<53 && f == math.Trunc(f) {
				integers++
			}
		}
		target := int32(-rng.IntN(20))
		if rng.IntN(40) == 0 {
			target = int32(rng.IntN(50) - 30)
		}
		mode := RoundingMode(rng.IntN(8))
		got, gc, gerr := FromFloat64ToExponent(f, target, mode)
		want, wc, werr := fromFloat64ToExponent(f, target, mode, limits{}, "FromFloat64ToExponent")
		requireSameOutcome(t, "FromFloat64ToExponent", strconv.FormatFloat(f, 'g', -1, 64), got, gc, gerr, want, wc, werr)
		if _, _, ok := float64ToExponentInline(f, target, mode); ok {
			taken++
			if gc&Inexact != 0 {
				inexact++
			}
		}
		if _, m, e := binary64Parts(f); m != 0 && e < 0 && e > -60 && target == 0 && m>>uint(-e-1) != 0 && m&(1<<uint(-e-1)-1) == 0 && -e-1 >= 0 {
			ties++ // exactly half a unit beyond an integer
		}
	}
	if integers < 2000 || taken < 50000 || inexact < 10000 || ties < 50 {
		t.Fatalf("vacuous path coverage: %d integers, %d taken, %d inexact, %d ties", integers, taken, inexact, ties)
	}
}
