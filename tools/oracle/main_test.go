// SPDX-License-Identifier: Apache-2.0

package main

import (
	"math/big"
	"testing"

	"github.com/0xCarbon/decimal"
)

// TestOracleDifferential checks every rounding operation, in every mode, on
// the fixed seed's random and constructed-tie inputs, agrees with the exact math/big
// reference in value, exponent or digit count, Inexact, Rounded and
// direction. The harness supplies each target and mode. Each operation must
// see ties, inexact and exact cases, so the run cannot pass vacuously.
func TestOracleDifferential(t *testing.T) {
	for _, op := range ops {
		t.Run(op.name, func(t *testing.T) {
			st := runOp(op, defaultSeed, defaultRandom, defaultTies, faultNone)
			for _, m := range st.mismatches {
				t.Error(m)
			}
			if want := int(modeCount) * (defaultRandom + defaultTies); st.checks != want || st.ties == 0 || st.inexact == 0 || st.exact == 0 {
				t.Errorf("vacuous run: %d checks (want %d), %d ties, %d inexact, %d exact", st.checks, want, st.ties, st.inexact, st.exact)
			}
		})
	}
}

// TestOracleFaultInjection is the differential's negative control: each deliberately defective use of the
// library (a confusable ties mode, truncation instead of the mode, an
// operand cut below the guard digit, swapped direction bits, a one-unit
// boundary error) must be reported for every operation it applies to.
func TestOracleFaultInjection(t *testing.T) {
	noOperandTarget := map[string]bool{"PowWithContext": true, "FromRatToExponent": true, "FromRatWithContext": true,
		"FromFloat64ToExponent": true, "FromFloat64WithContext": true}
	for _, fl := range []fault{faultTieSwap, faultTruncate, faultSticky, faultDirection, faultULP} {
		t.Run(faultNames[fl], func(t *testing.T) {
			for _, op := range ops {
				if fl == faultSticky && noOperandTarget[op.name] {
					continue
				}
				if st := runOp(op, defaultSeed, 8, 12, fl); len(st.mismatches) == 0 {
					t.Errorf("%s: the %s fault went undetected", op.name, faultNames[fl])
				}
			}
		})
	}
}

// TestModeMappingByName pins that each reference mode drives the library
// constant of the same name.
func TestModeMappingByName(t *testing.T) {
	for m := range modeCount {
		if got := libModes[m].String(); got != m.String() {
			t.Errorf("reference mode %s maps to library %s", m, got)
		}
	}
}

// TestReferenceRounding checks the reference itself on hand-derived
// vectors (an oracle can be wrong too): the negative-tie table at one decimal, tie-with-tail and
// below-half cases, digit targets with carry, square roots and binary64.
func TestReferenceRounding(t *testing.T) {
	type row struct {
		x    string
		k    int
		m    mode
		want string
		dir  int
	}
	for _, r := range []row{
		{"-2.5", 0, tiesToEven, "-2", 1}, {"-2.5", 0, tiesAwayFromZero, "-3", -1}, {"-2.5", 0, tiesTowardZero, "-2", 1},
		{"-2.5", 0, towardZero, "-2", 1}, {"-2.5", 0, awayFromZero, "-3", -1}, {"-2.5", 0, towardPositive, "-2", 1},
		{"-2.5", 0, towardNegative, "-3", -1}, {"3.5", 0, tiesToEven, "4", 1}, {"2.50001", 0, tiesToEven, "3", 1},
		{"2.49999", 0, tiesAwayFromZero, "2", -1}, {"-0.05", -1, tiesToEven, "0", 1}, {"1.25", -1, tiesTowardZero, "1.2", -1},
		{"125", 1, tiesToEven, "120", -1}, {"-125", 1, tiesAwayFromZero, "-130", -1}, {"7", 0, exactOnly, "7", 0},
	} {
		got := roundToExponent(ratOf(r.x), r.k, r.m)
		if got.value.Cmp(ratOf(r.want)) != 0 || got.dir != r.dir {
			t.Errorf("round(%s, 10^%d, %s) = %s dir %d, want %s dir %d", r.x, r.k, r.m, got.value.RatString(), got.dir, r.want, r.dir)
		}
	}
	if got := roundToExponent(ratOf("7.1"), 0, exactOnly); !got.refused || !got.inexact {
		t.Errorf("Exact did not refuse 7.1 at 10^0: %+v", got)
	}
	for _, r := range []struct {
		x    string
		p    int
		m    mode
		want string
	}{
		{"99999", 3, tiesToEven, "1.00E+5"}, {"0.0012345", 3, tiesToEven, "0.00123"}, {"-0.0012355", 4, tiesToEven, "-0.001236"},
		{"1234.5", 4, tiesToEven, "1234"}, {"1234.5", 4, tiesAwayFromZero, "1235"},
	} {
		if got := roundToDigits(ratOf(r.x), r.p, r.m); got.value.Cmp(ratOf(r.want)) != 0 {
			t.Errorf("round(%s, %d digits, %s) = %s, want %s", r.x, r.p, r.m, got.value.RatString(), r.want)
		}
	}
	for _, r := range []struct {
		x    string
		p    int
		m    mode
		want string
		dir  int
	}{
		{"2", 5, towardZero, "1.4142", -1}, {"2", 5, awayFromZero, "1.4143", 1}, {"2", 5, tiesToEven, "1.4142", -1},
		{"1.5625", 2, tiesToEven, "1.2", -1}, {"1.5625", 2, tiesAwayFromZero, "1.3", 1}, {"1E+10", 3, exactOnly, "100000", 0},
		{"0.0001", 1, tiesToEven, "0.01", 0}, {"1E-9", 2, tiesToEven, "0.000032", 1},
	} {
		got := roundSqrtToDigits(ratOf(r.x), r.p, r.m)
		if got.value.Cmp(ratOf(r.want)) != 0 || got.dir != r.dir {
			t.Errorf("sqrt(%s) to %d digits %s = %s dir %d, want %s dir %d", r.x, r.p, r.m, got.value.RatString(), got.dir, r.want, r.dir)
		}
	}
	for _, r := range []struct {
		x    string
		m    mode
		want float64
	}{
		{"0.1", tiesToEven, 0.1}, {"0.1", towardZero, 0.09999999999999999}, {"1.00000000000000011102230246251565404236316680908203125", tiesToEven, 1},
		{"1.00000000000000011102230246251565404236316680908203125", tiesAwayFromZero, 1.0000000000000002},
		{"-1.00000000000000011102230246251565404236316680908203125", tiesTowardZero, -1},
	} {
		if got, _ := roundToFloat64(ratOf(r.x), r.m); got != r.want {
			t.Errorf("binary64(%s, %s) = %v, want %v", r.x, r.m, got, r.want)
		}
	}
	for _, r := range []struct {
		x *big.Rat
		a int
	}{{ratOf("1"), 0}, {ratOf("9.99"), 0}, {ratOf("10"), 1}, {ratOf("0.001"), -3}, {ratOf("0.00099"), -4}, {big.NewRat(1, 3), -1}, {big.NewRat(-200, 3), 1}} {
		if got := adjusted(r.x); got != r.a {
			t.Errorf("adjusted(%s) = %d, want %d", r.x, got, r.a)
		}
	}
}

// TestVerifyReportsEachLeg pins that the checker compares every leg: value,
// exponent, digit count, Inexact, Rounded, direction, extra conditions and
// the expected refusals.
func TestVerifyReportsEachLeg(t *testing.T) {
	good := expect{r: rounded{value: ratOf("1.25"), inexact: true, dir: 1}, exponent: new(int), digits: 3}
	*good.exponent = -2
	ok := output{text: "1.25", conds: decimal.Inexact | decimal.Rounded | decimal.Increased}
	if msg := verify(good, ok); msg != "" {
		t.Fatalf("agreeing output rejected: %s", msg)
	}
	for name, out := range map[string]output{
		"value":     {text: "1.26", conds: ok.conds},
		"exponent":  {text: "1.250", conds: ok.conds},
		"inexact":   {text: "1.25", conds: decimal.Rounded},
		"rounded":   {text: "1.25", conds: decimal.Inexact | decimal.Increased},
		"direction": {text: "1.25", conds: decimal.Inexact | decimal.Rounded | decimal.Decreased},
		"extra":     {text: "1.25", conds: ok.conds | decimal.Subnormal},
		"refusal":   {err: &decimal.Error{Condition: decimal.InvalidOperation}},
	} {
		if verify(good, out) == "" {
			t.Errorf("%s disagreement not reported", name)
		}
	}
	exactNoRound := expAtFrom(rounded{value: ratOf("1.2")}, -1, -1)
	if verify(exactNoRound, output{text: "1.2", conds: decimal.Rounded}) == "" {
		t.Error("spurious Rounded on an exact result not reported")
	}
	if verify(expAtFrom(rounded{value: ratOf("1.2")}, -1, -3), output{text: "1.2"}) == "" {
		t.Error("missing Rounded on a zero-only discard not reported")
	}
	ideal := expDigitsIdeal(rounded{value: ratOf("1.20")}, 5, -2)
	if verify(ideal, output{text: "1.2"}) == "" {
		t.Error("digit-target exponent not checked against the ideal")
	}
	digits := expect{r: rounded{value: ratOf("100")}, digits: 2}
	if verify(digits, output{text: "100"}) == "" {
		t.Error("digit count not checked")
	}
	if verify(expect{r: rounded{value: ratOf("1"), refused: true}}, output{text: "1"}) == "" {
		t.Error("missing Exact refusal not reported")
	}
	if verify(expect{r: rounded{value: ratOf("1")}, invalid: true}, output{text: "1"}) == "" {
		t.Error("missing InvalidOperation not reported")
	}
	if verify(expect{r: rounded{value: ratOf("0.5")}, f: 0.5, isFloat: true}, output{f: 0.25}) == "" {
		t.Error("binary64 value not checked")
	}
}

// TestOracleFMAWitnesses pins the ternary oracle to hand-derived
// single-rounding, carry and cancellation examples of fused multiply-add.
func TestOracleFMAWitnesses(t *testing.T) {
	var fma opSpec
	for _, op := range ops {
		if op.name == "FMAWithContext" {
			fma = op
		}
	}
	if fma.lib == nil {
		t.Fatal("FMA missing from rational oracle operation inventory")
	}
	for _, row := range []struct {
		x, y, z string
		p       int
		even    string
	}{
		{"1.01", "1.01", "-1.02", 3, "0.0001"},
		{"1.0", "2.0", "3.00", 3, "5.00"},
		{"1.25", "1.01", "0.001", 3, "1.26"},
		{"99999999", "1", "0.5", 8, "1.0000000E+8"},
		{"9999999999", "1", "0.50001", 10, "1.000000000E+10"},
		{"-99999999", "1", "-0.49999", 8, "-99999999"},
		{"3.25", "-2", "6.50", 8, "0.00"},
	} {
		in := input{x: row.x, y: row.y, z: row.z, p: row.p}
		for m := range modeCount {
			ref := fma.ref(in, m)
			if m == tiesToEven && ref.r.value.Cmp(ratOf(row.even)) != 0 {
				t.Fatalf("reference %s: want hand-derived %s, got %s", describe(in), row.even, ref.r.value)
			}
			if msg := verify(ref, fma.lib(in, libModes[m])); msg != "" {
				t.Errorf("%s %s: %s", describe(in), m, msg)
			}
		}
	}
}

var faultNames = map[fault]string{faultTieSwap: "tie-swap", faultTruncate: "truncate", faultSticky: "dropped-sticky", faultDirection: "direction", faultULP: "ulp"}
