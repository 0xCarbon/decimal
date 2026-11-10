// SPDX-License-Identifier: Apache-2.0

package decimal_test

import (
	"crypto/sha256"
	"database/sql/driver"
	"encoding"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"go/ast"
	"go/doc"
	"go/parser"
	"go/token"
	"hash/maphash"
	"io"
	"io/fs"
	"maps"
	"math"
	"math/big"
	"math/rand"
	randv2 "math/rand/v2"
	"os"
	"path"
	"path/filepath"
	"reflect"
	"regexp"
	"slices"
	"strconv"
	"strings"
	"testing"
	"testing/fstest"
	"time"

	decimal "github.com/0xCarbon/decimal"
)

// TestAccessorsReportStoredScale checks that the stored scale is reported
// as constructed: 1.10 keeps exponent -2 and three coefficient digits, and
// normalization happens only through Reduce.
func TestAccessorsReportStoredScale(t *testing.T) {
	for _, tc := range []struct {
		text     string
		exponent int32
		digits   uint64
	}{
		{"1.10", -2, 3},
		{"0", 0, 1},
		{"0.000", -3, 1},
		{"-5E+3", 3, 1},
		{"100", 0, 3},
		{"340282366920938463463374607431768211455", 0, 39}, // 2^128-1, inline
		{"340282366920938463463374607431768211456", 0, 39}, // 2^128, slow band
		{strings.Repeat("9", 100) + "E-7", -7, 100},
	} {
		d := decimal.MustParse(tc.text)
		if d.Exponent() != tc.exponent || d.CoefficientDigits() != tc.digits {
			t.Errorf("%s: Exponent %d CoefficientDigits %d; want %d, %d", tc.text, d.Exponent(), d.CoefficientDigits(), tc.exponent, tc.digits)
		}
	}
	reduced := decimal.MustParse("1.10").Reduce()
	if reduced.Exponent() != -1 || reduced.CoefficientDigits() != 2 {
		t.Fatalf("Reduce(1.10) accessors = %d, %d; want -1, 2", reduced.Exponent(), reduced.CoefficientDigits())
	}
}

// TestAccessorsStableAcrossInternalPaths checks that accessors are stable
// across internal paths: one value built by parsing, by constructor, by
// inline arithmetic and by slow-band arithmetic that cancels back below
// 2^128 has identical text, accessors, equality, order and hash.
func TestAccessorsStableAcrossInternalPaths(t *testing.T) {
	big := decimal.MustParse("1" + strings.Repeat("0", 60))
	viaSlow, err := big.Add(decimal.MustParse("12.345"))
	if err != nil {
		t.Fatal(err)
	}
	viaSlow, err = viaSlow.Sub(big)
	if err != nil {
		t.Fatal(err)
	}
	viaMul, err := decimal.New(12345, -4).Mul(decimal.New(1, 1))
	if err != nil {
		t.Fatal(err)
	}
	paths := []decimal.Decimal{
		decimal.MustParse("12.345"),
		decimal.New(12345, -3),
		viaSlow,
		viaMul,
	}
	seed := maphash.MakeSeed()
	digest := func(d decimal.Decimal) uint64 {
		var h maphash.Hash
		h.SetSeed(seed)
		decimal.Hasher{}.Hash(&h, d)
		return h.Sum64()
	}
	first := paths[0]
	for i, d := range paths {
		if d.String() != "12.345" || d.Exponent() != -3 || d.CoefficientDigits() != 5 ||
			!d.Equal(first) || d.Compare(first) != 0 || digest(d) != digest(first) {
			t.Errorf("path %d: %s exponent %d digits %d", i, d, d.Exponent(), d.CoefficientDigits())
		}
	}
}

// boxOnly has Decimal's size and a Format that writes a constant, so
// formatting it measures only fmt's operand boxing.
type boxOnly struct{ words [6]uint64 }

func (boxOnly) Format(state fmt.State, _ rune) { _, _ = io.WriteString(state, "x") }

type jsonOnly struct{ words [6]uint64 }

func (jsonOnly) MarshalJSON() ([]byte, error) { return []byte{'1'}, nil }

// TestAllocationBudgets pins the per-call heap allocation count of the
// outbound text paths for inline values. Owned result bytes or strings cost
// exactly one allocation; formatting into a caller's fmt.State adds only
// the owned text string beyond fmt's argument boxing, measured by a baseline.
func TestAllocationBudgets(t *testing.T) {
	value := decimal.MustParse("-12345.6789")
	sink := 0
	for _, tc := range []struct {
		name string
		want float64
		fn   func()
	}{
		{"Text", 1, func() { s, _ := value.Text(0); sink += len(s) }},
		{"String", 1, func() { sink += len(value.String()) }},
		{"MarshalText", 1, func() { b, _ := value.MarshalText(); sink += len(b) }},
		{"MarshalJSON", 1, func() { b, _ := value.MarshalJSON(); sink += len(b) }},
		{"AppendText", 0, func() {
			var buf [64]byte
			b, _ := value.AppendText(buf[:0])
			sink += len(b)
		}},
	} {
		if got := testing.AllocsPerRun(200, tc.fn); got != tc.want {
			t.Errorf("%s allocations = %v, want %v", tc.name, got, tc.want)
		}
	}
	// Inbound byte parsing must not copy the caller's bytes on success.
	for _, raw := range []string{"-12345.6789", `"-12345.6789"`, " 1E+5 "} {
		text, target := []byte(raw), decimal.Decimal{}
		got := testing.AllocsPerRun(200, func() {
			if raw[0] == '-' {
				_ = target.UnmarshalText(text)
			}
			_ = target.UnmarshalJSON(text)
		})
		if got != 0 {
			t.Errorf("UnmarshalText/UnmarshalJSON(%s) allocations = %v, want 0", raw, got)
		}
	}
	// encoding/json adds its own boxing and result copy; MarshalJSON must add
	// no more than a same-size marshaler returning one fresh byte slice.
	var marshal jsonOnly
	jsonBaseline := testing.AllocsPerRun(200, func() {
		marshal.words[0]++
		b, _ := json.Marshal(marshal)
		sink += len(b)
	})
	if got := testing.AllocsPerRun(200, func() { b, _ := json.Marshal(value); sink += len(b) }); got > jsonBaseline {
		t.Errorf("json.Marshal allocations = %v, want <= %v", got, jsonBaseline)
	}
	// fmt boxes the Decimal operand once; Format itself must add nothing,
	// with or without width padding and for every supported verb.
	var box boxOnly
	baseline := testing.AllocsPerRun(200, func() {
		box.words[0]++ // a runtime value, so fmt must box a copy
		fmt.Fprintf(io.Discard, "%v", box)
	})
	for _, format := range []string{"%v", "%s", "%20v", "%-20s", "%.2f", "%.3e", "%f", "%e"} {
		got := testing.AllocsPerRun(200, func() { fmt.Fprintf(io.Discard, format, value) })
		limit := baseline + 1 // Text, Fixed and Scientific return an owned string
		if got > limit {
			t.Errorf("Fprintf(%q) allocations = %v, want <= %v", format, got, limit)
		}
	}
	_ = sink
}

// TestTextRefusalIsTypedOperationError checks that a Text
// refusal must carry the same typed error as every other checked operation.
func TestTextRefusalIsTypedOperationError(t *testing.T) {
	_, err := decimal.MustParse("12345").Text(3)
	var operation *decimal.Error
	if !errors.As(err, &operation) || operation.Op != "Text" || operation.Condition != decimal.InsufficientStorage ||
		!errors.Is(err, decimal.ErrInsufficientStorage) || err.Error() != "decimal: Text: insufficient storage" {
		t.Fatalf("Text(3) error = %#v", err)
	}
}

// TestContextSubnormalCarryKeepsEtiny checks that a tiny result rounded at
// the Etiny quantum that carries through all nines keeps the Etiny
// exponent. Python
// decimal and decNumber agree: 0.00999 at p=3, Emin=-2 rounds to 0.0100.
func TestContextSubnormalCarryKeepsEtiny(t *testing.T) {
	ctx, err := decimal.NewContext(3, decimal.TiesToEven, &decimal.ExponentGuards{Emin: -2, Emax: 5}, 0)
	if err != nil {
		t.Fatal(err)
	}
	const want = "0.0100"
	// Increased: 0.0100 is greater than the exact 0.00999.
	const flags = decimal.Subnormal | decimal.Underflow | decimal.Inexact | decimal.Rounded | decimal.Increased
	for _, tc := range []struct {
		name string
		run  func() (decimal.Decimal, decimal.Conditions, error)
	}{
		{"0.00999+0", func() (decimal.Decimal, decimal.Conditions, error) {
			return decimal.MustParse("0.00999").AddWithContext(decimal.MustParse("0"), ctx)
		}},
		{"0.00999-0", func() (decimal.Decimal, decimal.Conditions, error) {
			return decimal.MustParse("0.00999").SubWithContext(decimal.MustParse("0"), ctx)
		}},
		{"0.0999*0.1", func() (decimal.Decimal, decimal.Conditions, error) {
			return decimal.MustParse("0.0999").MulWithContext(decimal.MustParse("0.1"), ctx)
		}},
	} {
		got, conditions, err := tc.run()
		text, _ := got.Text(0)
		if err != nil || text != want || conditions != flags {
			t.Errorf("%s = %q, %b, %v; want %q, %b, nil", tc.name, text, conditions, err, want, flags)
		}
	}
}

// TestContextSubnormalRoundsOnceAtEtiny checks that subnormal results
// round once at Etiny. At p=3,
// Emin=-2 the Etiny quantum is 10^(Emin-(p-1)) = 10^-4, so a nonzero result
// below Emin rounds once at 1E-4 under the context mode, may keep fewer than
// three digits, and is an ordinary finite Decimal. Hand-derived vectors:
// 0.00123 = 12.3E-4 gives 0.0012 (Decreased); 0.00129 = 12.9E-4 gives 0.0013
// under TiesToEven and 0.0012 under TowardZero; 0.001250001 = 12.50001E-4
// gives 0.0013, where rounding first to three digits (0.00125) and then at
// Etiny would tie to 0.0012; the exact 0.0012 reports Subnormal alone.
func TestContextSubnormalRoundsOnceAtEtiny(t *testing.T) {
	const inexact = decimal.Subnormal | decimal.Underflow | decimal.Inexact | decimal.Rounded
	for _, tc := range []struct {
		input, want string
		mode        decimal.RoundingMode
		conditions  decimal.Conditions
	}{
		{"0.00123", "0.0012", decimal.TiesToEven, inexact | decimal.Decreased},
		{"0.00129", "0.0013", decimal.TiesToEven, inexact | decimal.Increased},
		{"0.00129", "0.0012", decimal.TowardZero, inexact | decimal.Decreased},
		{"0.001250001", "0.0013", decimal.TiesToEven, inexact | decimal.Increased},
		{"0.0012", "0.0012", decimal.TiesToEven, decimal.Subnormal},
	} {
		ctx, err := decimal.NewContext(3, tc.mode, &decimal.ExponentGuards{Emin: -2, Emax: 2}, 0)
		if err != nil {
			t.Fatal(err)
		}
		for _, op := range []struct {
			name string
			run  func(decimal.Decimal) (decimal.Decimal, decimal.Conditions, error)
		}{
			{"Mul", func(x decimal.Decimal) (decimal.Decimal, decimal.Conditions, error) {
				return x.MulWithContext(decimal.One(), ctx)
			}},
			{"Add", func(x decimal.Decimal) (decimal.Decimal, decimal.Conditions, error) {
				return x.AddWithContext(decimal.Zero(), ctx)
			}},
			{"RoundToPrecision", func(x decimal.Decimal) (decimal.Decimal, decimal.Conditions, error) {
				return x.RoundToPrecisionWithContext(ctx)
			}},
		} {
			got, conditions, err := op.run(decimal.MustParse(tc.input))
			text, textErr := got.Text(0)
			if err != nil || textErr != nil || text != tc.want || got.Exponent() != -4 || conditions != tc.conditions {
				t.Errorf("%s(%s) mode %v = %q e%d, %v, %v/%v; want %q e-4, %v", op.name, tc.input, tc.mode, text, got.Exponent(), conditions, err, textErr, tc.want, tc.conditions)
			}
		}
	}
}

// TestEngineRulesComposeFromCoreOperations checks that database engine
// rules compose from core operations and SQL scale domains stay out of the
// core: no engine-fidelity
// profile exists, so a caller applies an engine's result scale with a
// Context and Quantize, or a division rounded to the engine's exponent.
// Hand-derived vectors: SQL Server's decimal(38,6) quotient 1/3 = 0.333333;
// MySQL's division scale with div_precision_increment 4 gives 2/3 = 0.6667
// (half away from zero); PostgreSQL's 16383-digit dscale limit applied to
// 15E-16384 gives 2E-16383 under TiesToEven. The exported surface has no
// profile or engine identifier and Context has no exported field.
func TestEngineRulesComposeFromCoreOperations(t *testing.T) {
	ctx38, err := decimal.NewContext(38, decimal.TiesAwayFromZero, nil, 0)
	if err != nil {
		t.Fatal(err)
	}
	wide, _, err := decimal.MustParse("1").DivWithContext(decimal.MustParse("3"), ctx38)
	if err != nil {
		t.Fatal(err)
	}
	sqlServer, _, err := wide.Quantize(-6, decimal.TiesAwayFromZero)
	if text, _ := sqlServer.Text(0); err != nil || text != "0.333333" {
		t.Errorf("SQL Server decimal(38,6) 1/3 = %q, %v; want 0.333333", text, err)
	}
	mysql, conditions, err := decimal.MustParse("2").DivToExponent(decimal.MustParse("3"), -4, decimal.TiesAwayFromZero)
	if text, _ := mysql.Text(0); err != nil || text != "0.6667" || conditions != decimal.Inexact|decimal.Rounded|decimal.Increased {
		t.Errorf("MySQL 2/3 at scale 4 = %q, %v, %v; want 0.6667, Inexact|Rounded|Increased", text, conditions, err)
	}
	postgres, conditions, err := decimal.New(15, -16384).Quantize(-16383, decimal.TiesToEven)
	if err != nil || postgres.Exponent() != -16383 || !postgres.Equal(decimal.New(2, -16383)) || conditions != decimal.Inexact|decimal.Rounded|decimal.Increased {
		t.Errorf("PostgreSQL dscale 16383 of 15E-16384 = %v, %v, %v; want 2E-16383, Inexact|Rounded|Increased", postgres, conditions, err)
	}
	surface := parseExportedSurface(t)
	engine := regexp.MustCompile(`Profile|Dialect|Postgres|MySQL|SQLServer|Engine($|[A-Z])`)
	for name, want := range map[string]bool{
		"EngineProfile": true, "Decimal.WithEngine": true, "MySQLDivScale": true, "Decimal.Engineering": false, "EstimateEngineering": false, "Quantize": false,
	} {
		if engine.MatchString(name) != want {
			t.Fatalf("engine pattern on %s = %v, want %v", name, !want, want)
		}
	}
	for name := range surface.funcs {
		if engine.MatchString(name) {
			t.Errorf("exported function %s names an engine profile", name)
		}
	}
	for name := range surface.types {
		if engine.MatchString(name) {
			t.Errorf("exported type %s names an engine profile", name)
		}
	}
	contextType := reflect.TypeFor[decimal.Context]()
	for field := range contextType.Fields() {
		if field.IsExported() {
			t.Errorf("Context has exported field %s", field.Name)
		}
	}
}

// TestContextRoundingAgainstBigIntOracle compares guarded and unguarded
// context Add/Sub/Mul with an independent math/big implementation of the GDA
// rounding rules: round once at max(length-p, Etiny-exponent) digits, shift
// the exponent only when the rounded coefficient exceeds p digits, and raise
// Subnormal (plus Underflow when inexact) for tiny exact results. The
// direction bit is the sign of the oracle's rounded value minus the exact
// result. Overflowing results are outside this oracle and are skipped.
func TestContextRoundingAgainstBigIntOracle(t *testing.T) {
	r := rand.New(rand.NewSource(20260929))
	modes := []decimal.RoundingMode{
		decimal.TiesToEven, decimal.TiesAwayFromZero, decimal.TiesTowardZero, decimal.TowardZero,
		decimal.AwayFromZero, decimal.TowardPositiveInfinity, decimal.TowardNegativeInfinity,
	}
	operand := func() (*big.Int, int64) {
		digits := 1 + r.Intn(12)
		coefficient := new(big.Int)
		switch r.Intn(3) {
		case 0: // runs of nines provoke carries through the retained digits
			coefficient.Sub(pow10Big(int64(digits)), big.NewInt(int64(r.Intn(3))))
		default:
			coefficient.Rand(r, pow10Big(int64(digits)))
		}
		if r.Intn(2) == 0 {
			coefficient.Neg(coefficient)
		}
		return coefficient, int64(r.Intn(21) - 14)
	}
	checked := 0
	for range 60_000 {
		p := int64(1 + r.Intn(8))
		mode := modes[r.Intn(len(modes))]
		guarded := r.Intn(4) != 0
		emin := int64(-r.Intn(8))
		emax := emin + 3 + int64(r.Intn(12))
		var guards *decimal.ExponentGuards
		if guarded {
			guards = &decimal.ExponentGuards{Emin: int32(emin), Emax: int32(emax)}
		}
		ctx, err := decimal.NewContext(uint32(p), mode, guards, 0)
		if err != nil {
			t.Fatal(err)
		}
		ac, ae := operand()
		bc, be := operand()
		a, b := decimal.MustParse(ac.String()+"E"+strconv.FormatInt(ae, 10)), decimal.MustParse(bc.String()+"E"+strconv.FormatInt(be, 10))
		var exact *big.Int
		var exponent int64
		var got decimal.Decimal
		var conditions decimal.Conditions
		switch op := r.Intn(3); op {
		case 0, 1:
			exponent = min(ae, be)
			x := new(big.Int).Mul(ac, pow10Big(ae-exponent))
			y := new(big.Int).Mul(bc, pow10Big(be-exponent))
			if op == 0 {
				exact = x.Add(x, y)
				got, conditions, err = a.AddWithContext(b, ctx)
			} else {
				exact = x.Sub(x, y)
				got, conditions, err = a.SubWithContext(b, ctx)
			}
		default:
			exponent = ae + be
			exact = new(big.Int).Mul(ac, bc)
			got, conditions, err = a.MulWithContext(b, ctx)
		}
		want, wantConditions, ok := oracleContextRound(exact, exponent, p, guarded, emin, emax, mode)
		if !ok {
			continue
		}
		checked++
		text, _ := got.Text(0)
		if err != nil || text != want || conditions != wantConditions {
			t.Fatalf("p=%d mode=%d guards=%v [%d,%d]: %s op %s = %q, %b, %v; oracle %q, %b",
				p, mode, guarded, emin, emax, a, b, text, conditions, err, want, wantConditions)
		}
	}
	if checked < 30_000 {
		t.Fatalf("oracle checked only %d cases", checked)
	}
}

func pow10Big(n int64) *big.Int { return new(big.Int).Exp(big.NewInt(10), big.NewInt(n), nil) }

func oracleContextRound(exact *big.Int, exponent, p int64, guarded bool, emin, emax int64, mode decimal.RoundingMode) (string, decimal.Conditions, bool) {
	negative := exact.Sign() < 0
	magnitude := new(big.Int).Abs(exact)
	if magnitude.Sign() == 0 {
		return decimal.MustParse("0E" + strconv.FormatInt(exponent, 10)).String(), 0, true
	}
	length := int64(len(magnitude.String()))
	adjusted := exponent + length - 1
	if guarded && adjusted > emax {
		return "", 0, false
	}
	cut := max(0, length-p)
	tiny := guarded && adjusted < emin
	if tiny {
		cut = max(cut, emin-(p-1)-exponent)
	}
	var conditions decimal.Conditions
	if cut > 0 {
		source, sourceExponent := new(big.Int).Set(magnitude), exponent
		quotient, remainder := new(big.Int).QuoRem(magnitude, pow10Big(cut), new(big.Int))
		half := new(big.Int).Mul(remainder, big.NewInt(2))
		tie := half.Cmp(pow10Big(cut))
		inexact := remainder.Sign() != 0
		odd := quotient.Bit(0) == 1
		var up bool
		switch mode {
		case decimal.TiesToEven:
			up = tie > 0 || tie == 0 && odd
		case decimal.TiesAwayFromZero:
			up = tie >= 0
		case decimal.TiesTowardZero:
			up = tie > 0
		case decimal.AwayFromZero:
			up = inexact
		case decimal.TowardPositiveInfinity:
			up = inexact && !negative
		case decimal.TowardNegativeInfinity:
			up = inexact && negative
		}
		if up {
			quotient.Add(quotient, big.NewInt(1))
		}
		magnitude, exponent = quotient, exponent+cut
		if int64(len(magnitude.String())) > p {
			magnitude.Quo(magnitude, big.NewInt(10))
			exponent++
		}
		conditions |= decimal.Rounded
		if inexact {
			conditions |= decimal.Inexact
		}
		if tiny && inexact {
			conditions |= decimal.Underflow
		}
		if inexact {
			// Scale the rounded magnitude back to the exact exponent; the sign
			// of the value difference is the magnitude difference's sign
			// flipped for negative results.
			rounded := new(big.Int).Mul(magnitude, pow10Big(exponent-sourceExponent))
			difference := rounded.Cmp(source)
			if negative {
				difference = -difference
			}
			if difference > 0 {
				conditions |= decimal.Increased
			} else {
				conditions |= decimal.Decreased
			}
		}
	}
	if tiny {
		conditions |= decimal.Subnormal
	}
	if magnitude.Sign() == 0 {
		return decimal.MustParse("0E" + strconv.FormatInt(exponent, 10)).String(), conditions, true
	}
	if guarded && exponent+int64(len(magnitude.String()))-1 > emax {
		return "", 0, false
	}
	text := magnitude.String() + "E" + strconv.FormatInt(exponent, 10)
	if negative {
		text = "-" + text
	}
	return decimal.MustParse(text).String(), conditions, true
}

// TestContextAddRemoteOperandIsSticky checks that, with a
// finite precision, an operand entirely below the rounding position only
// supplies a sticky digit, so an unbudgeted context Add must not do work
// proportional to the exponent gap, here 4e8.
func TestContextAddRemoteOperandIsSticky(t *testing.T) {
	var err error
	big, tiny := decimal.MustParse("1E+200000000"), decimal.MustParse("1E-200000000")
	start := time.Now()
	for _, tc := range []struct {
		mode      decimal.RoundingMode
		sub       bool
		want      string
		direction decimal.Conditions // sign of result − (1E+200000000 ± 1E-200000000).
	}{
		{decimal.TiesToEven, false, "1.000000000000000E+200000000", decimal.Decreased},
		{decimal.TowardPositiveInfinity, false, "1.000000000000001E+200000000", decimal.Increased},
		{decimal.TowardZero, true, "9.999999999999999E+199999999", decimal.Decreased},
		{decimal.TiesToEven, true, "1.000000000000000E+200000000", decimal.Increased},
	} {
		c, _ := decimal.NewContext(16, tc.mode, nil, 0)
		var got decimal.Decimal
		var conditions decimal.Conditions
		if tc.sub {
			got, conditions, err = big.SubWithContext(tiny, c)
		} else {
			got, conditions, err = big.AddWithContext(tiny, c)
		}
		if err != nil || got.String() != tc.want || conditions != decimal.Inexact|decimal.Rounded|tc.direction {
			t.Errorf("mode %v sub %v: %s, %v, %v; want %s", tc.mode, tc.sub, got, conditions, err, tc.want)
		}
	}
	if elapsed := time.Since(start); elapsed > 200*time.Millisecond {
		t.Fatalf("four remote-operand context additions took %v", elapsed)
	}
}

// TestContextBudgetCountsCarriedEtinyDigit pins the budget consequence of
// the subnormal carry: the correct subnormal carry keeps Etiny with one more coefficient
// digit, so a digit cap one below that length refuses.
func TestContextBudgetCountsCarriedEtinyDigit(t *testing.T) {
	ctx, err := decimal.NewContext(34, decimal.TiesAwayFromZero, &decimal.ExponentGuards{Emin: -17, Emax: 66}, 0)
	if err != nil {
		t.Fatal(err)
	}
	a, b := decimal.MustParse("999E-56"), decimal.MustParse("-99999999999999999999E-54")
	got, _, err := a.AddWithContext(b, ctx)
	if err != nil || got.String() != "-1.0000000000000000E-34" || got.Exponent() != -50 {
		t.Fatalf("unbudgeted = %s (exponent %d), %v", got, got.Exponent(), err)
	}
	if _, _, err := a.AddWithContext(b, ctx.WithBudget(decimal.Budget{MaxDigits: 16})); !errors.Is(err, decimal.ErrInsufficientStorage) {
		t.Fatalf("16-digit cap: %v, want ErrInsufficientStorage", err)
	}
	if _, _, err := a.AddWithContext(b, ctx.WithBudget(decimal.Budget{MaxDigits: 17})); err != nil {
		t.Fatalf("17-digit cap: %v", err)
	}
}

type outboundFixture struct {
	name, input, coefficient, want string
	exponent                       int32
	negative                       bool
	newMinInt64                    bool
}

func outboundFixtures(t *testing.T) []outboundFixture {
	t.Helper()
	return []outboundFixture{
		{name: "scale-2", input: "1.10", coefficient: "110", exponent: -2, want: "1.10"},
		{name: "zero-scale-2", input: "0.00", coefficient: "0", exponent: -2, want: "0.00"},
		{name: "zero-positive-exponent", input: "0E+2", coefficient: "0", exponent: 2, want: "0E+2"},
		{name: "negative-cohort", input: "-12.300", coefficient: "12300", exponent: -3, negative: true, want: "-12.300"},
		{name: "scientific", input: "1E-7", coefficient: "1", exponent: -7, want: "1E-7"},
		{name: "negative-zero", input: "-0.00", coefficient: "0", exponent: -2, want: "0.00"},
		{name: "min-int64", coefficient: "9223372036854775808", exponent: -2, negative: true, want: "-92233720368547758.08", newMinInt64: true},
		{name: "slow-integer", input: "1234567890123456789012345678901234567890", coefficient: "1234567890123456789012345678901234567890", exponent: 0, want: "1234567890123456789012345678901234567890"},
		{name: "slow-equal-different-cohort", input: "1.1" + strings.Repeat("0", 38), coefficient: "11" + strings.Repeat("0", 38), exponent: -39, want: "1.1" + strings.Repeat("0", 38)},
	}
}

func outboundValue(t *testing.T, f outboundFixture) decimal.Decimal {
	t.Helper()
	if f.newMinInt64 {
		return decimal.New(-1<<63, f.exponent)
	}
	d, err := decimal.Parse(f.input)
	if err != nil {
		t.Fatalf("Parse(%q): %v", f.input, err)
	}
	return d
}

// The expected rational comes from fixture coefficient/exponent fields, not
// Decimal.Parse, Text, String, or the methods under test.
func outboundRat(t *testing.T, f outboundFixture) *big.Rat {
	t.Helper()
	coefficient, ok := new(big.Int).SetString(f.coefficient, 10)
	if !ok {
		t.Fatalf("invalid fixture coefficient %q", f.coefficient)
	}
	if f.negative {
		coefficient.Neg(coefficient)
	}
	ten := big.NewInt(10)
	if f.exponent >= 0 {
		coefficient.Mul(coefficient, new(big.Int).Exp(ten, big.NewInt(int64(f.exponent)), nil))
		return new(big.Rat).SetInt(coefficient)
	}
	denominator := new(big.Int).Exp(ten, big.NewInt(-int64(f.exponent)), nil)
	return new(big.Rat).SetFrac(coefficient, denominator)
}

func TestInteropValuerCanonicalScaleAndKind(t *testing.T) {
	for _, f := range outboundFixtures(t) {
		d := outboundValue(t, f)
		t.Run(f.name+"/kind", func(t *testing.T) {
			got, err := d.Value()
			if err != nil {
				t.Fatal(err)
			}
			if _, ok := got.(string); !ok {
				t.Fatalf("Value payload kind = %T, want string", got)
			}
		})
		t.Run(f.name+"/bytes", func(t *testing.T) {
			got, err := d.Value()
			if err != nil {
				t.Fatal(err)
			}
			if got != f.want {
				t.Fatalf("Value payload = %q, want %q", got, f.want)
			}
		})
		t.Run(f.name+"/numeric", func(t *testing.T) {
			got, err := d.Value()
			if err != nil {
				t.Fatal(err)
			}
			value, ok := got.(string)
			if !ok {
				t.Fatalf("Value payload kind = %T, want string", got)
			}
			actual, ok := new(big.Rat).SetString(value)
			if !ok || actual.Cmp(outboundRat(t, f)) != 0 {
				t.Fatalf("Value numeric = %q, want coefficient %s exponent %d", value, f.coefficient, f.exponent)
			}
		})
	}
}

func TestInteropTextMarshalerCanonicalBytes(t *testing.T) {
	for _, f := range outboundFixtures(t) {
		d := outboundValue(t, f)
		t.Run(f.name+"/bytes", func(t *testing.T) {
			got, err := d.MarshalText()
			if err != nil {
				t.Fatal(err)
			}
			if string(got) != f.want {
				t.Fatalf("MarshalText bytes = %q, want %q", got, f.want)
			}
		})
		t.Run(f.name+"/numeric", func(t *testing.T) {
			got, err := d.MarshalText()
			if err != nil {
				t.Fatal(err)
			}
			actual, ok := new(big.Rat).SetString(string(got))
			if !ok || actual.Cmp(outboundRat(t, f)) != 0 {
				t.Fatalf("MarshalText numeric = %q, want coefficient %s exponent %d", got, f.coefficient, f.exponent)
			}
		})
		t.Run(f.name+"/owned-bytes", func(t *testing.T) {
			got, err := d.MarshalText()
			if err != nil {
				t.Fatal(err)
			}
			if len(got) == 0 {
				t.Fatal("MarshalText returned no bytes")
			}
			got[0] = '!'
			again, err := d.MarshalText()
			if err != nil || string(again) != f.want {
				t.Fatalf("MarshalText result aliases Decimal: %q, %v", again, err)
			}
		})
	}
}

func TestInteropReadInterfaceSets(t *testing.T) {
	var _ driver.Valuer = decimal.Decimal{}
	var _ encoding.TextMarshaler = decimal.Decimal{}
	value := decimal.New(110, -2)
	var valuer driver.Valuer = value
	var marshaler encoding.TextMarshaler = value
	if got, err := valuer.Value(); err != nil || got != "1.10" {
		t.Fatalf("value receiver Valuer = %q, %v", got, err)
	}
	if got, err := marshaler.MarshalText(); err != nil || string(got) != "1.10" {
		t.Fatalf("value receiver TextMarshaler = %q, %v", got, err)
	}
}

// TestAppendTextMatchesMarshalText requires AppendText to append exactly the
// MarshalText bytes after an existing prefix, for inline, slow-band, zero
// and exponent-form values, without touching the prefix.
func TestAppendTextMatchesMarshalText(t *testing.T) {
	for _, text := range []string{
		"0", "0E+5", "-1.10", "1E-12", "123456789012345678901234567890123456789",
		"340282366920938463463374607431768211456", "-" + strings.Repeat("9", 120) + "E-60",
		strings.Repeat("7", 90) + "E+7",
	} {
		d := decimal.MustParse(text)
		want, err := d.MarshalText()
		if err != nil {
			t.Fatal(err)
		}
		prefix := []byte("value=")
		got, err := d.AppendText(prefix)
		if err != nil || string(got) != "value="+string(want) || string(prefix) != "value=" {
			t.Fatalf("AppendText(%s) = %q, %v; want value=%s", text, got, err, want)
		}
	}
}

// TestConditionAndModeNames checks that conditions, rounding
// modes and trapped-condition errors name what happened.
func TestConditionAndModeNames(t *testing.T) {
	for _, tc := range []struct {
		got  fmt.Stringer
		want string
	}{
		{decimal.Conditions(0), "0"},
		{decimal.Inexact, "Inexact"},
		{decimal.Inexact | decimal.Rounded | decimal.Subnormal, "Inexact|Rounded|Subnormal"},
		{decimal.Clamped | decimal.Underflow, "Clamped|Underflow"},
		{decimal.Conditions(1 << 15), "Conditions(0x8000)"},
		{decimal.Rounded | decimal.Conditions(1<<15), "Rounded|Conditions(0x8000)"},
		{decimal.TiesToEven, "TiesToEven"},
		{decimal.TowardNegativeInfinity, "TowardNegativeInfinity"},
		{decimal.Exact, "Exact"},
		{decimal.RoundingMode(99), "RoundingMode(99)"},
	} {
		if s := tc.got.String(); s != tc.want {
			t.Errorf("String() = %q, want %q", s, tc.want)
		}
	}
}

// TestConditionErrorNamesTrapped requires a trapped-condition error to name
// its conditions instead of a generic "decimal condition" message.
func TestConditionErrorNamesTrapped(t *testing.T) {
	ctx, err := decimal.NewContext(2, decimal.TiesToEven, nil, decimal.Inexact|decimal.Rounded)
	if err != nil {
		t.Fatal(err)
	}
	_, _, err = decimal.MustParse("1.25").AddWithContext(decimal.Zero(), ctx)
	if err == nil || err.Error() != "decimal: AddWithContext: condition Inexact|Rounded" {
		t.Fatalf("trapped error = %v", err)
	}
	_, _, err = decimal.MustParse("1.25").Quantize(-1, decimal.Exact)
	if err == nil || err.Error() != "decimal: Quantize: condition Inexact" {
		t.Fatalf("Exact refusal error = %v", err)
	}
}

func TestZeroValueEqualityHashCohort(t *testing.T) {
	var zero decimal.Decimal
	seed := maphash.MakeSeed()
	digest := func(value decimal.Decimal) uint64 {
		var h maphash.Hash
		h.SetSeed(seed)
		(decimal.Hasher{}).Hash(&h, value)
		return h.Sum64()
	}
	wantHash := digest(zero)
	for _, tc := range []struct{ input, text string }{
		{"0", "0"}, {"0.0", "0.0"}, {"0.00", "0.00"}, {"0E+9", "0E+9"}, {"-0", "0"},
	} {
		value := decimal.MustParse(tc.input)
		if !zero.Equal(value) || zero.Compare(value) != 0 || !(decimal.Hasher{}).Equal(zero, value) || digest(value) != wantHash {
			t.Fatalf("zero value disagrees with cohort %q", tc.input)
		}
		text, err := value.Text(0)
		if err != nil || text != tc.text || value.Reduce().String() != "0" {
			t.Fatalf("zero cohort %q emitted %q, error %v", tc.input, text, err)
		}
	}
	if zero.String() != "0" || zero.Reduce().String() != "0" {
		t.Fatal("zero value public methods are unusable")
	}
}

var (
	updatePortableDigest = flag.Bool("update-portable-digest", false, "rewrite testdata/portable-results.sha256 from this run")
	dumpPortableResults  = flag.String("dump-portable-results", "", "write every portable result line to this file for diffing")
)

const portableDigestFile = "testdata/portable-results.sha256"

// TestPortableResultDigest checks that results are bit-identical across
// build profiles and architectures. A seeded corpus drives every shipped public operation family and
// hashes each result, condition set and error text; the digest must equal
// the committed golden on the default SIMD profile, the scalar profile,
// GOARCH=386, arm64 and js/wasm. Semantic changes rewrite the golden with
// -update-portable-digest in the same commit; on a mismatch, compare
// two -dump-portable-results files to find the first divergent line.
func TestPortableResultDigest(t *testing.T) {
	lines := portableResultLines(t)
	sum := sha256.New()
	for _, line := range lines {
		io.WriteString(sum, line)
		sum.Write([]byte{'\n'})
	}
	got := fmt.Sprintf("%s %d\n", hex.EncodeToString(sum.Sum(nil)), len(lines))
	if *dumpPortableResults != "" {
		if err := os.WriteFile(*dumpPortableResults, []byte(strings.Join(lines, "\n")+"\n"), 0o600); err != nil {
			t.Fatal(err)
		}
	}
	if *updatePortableDigest {
		if err := os.WriteFile(portableDigestFile, []byte(got), 0o600); err != nil {
			t.Fatal(err)
		}
		return
	}
	want, err := os.ReadFile(portableDigestFile)
	if err != nil {
		t.Fatal(err)
	}
	if got != string(want) {
		t.Fatalf("portable result digest %q, want %q; rerun with -dump-portable-results on a reference target and diff", strings.TrimSpace(got), strings.TrimSpace(string(want)))
	}
}

// TestIdenticalCallsGiveIdenticalResults checks that identical calls give
// identical results: the full portable corpus replayed after unrelated
// library use in the same process (huge parses, refusals, every context
// preset and all display paths) yields the identical result sequence.
func TestIdenticalCallsGiveIdenticalResults(t *testing.T) {
	first := portableResultLines(t)
	huge := "1" + strings.Repeat("0", 5000) + "E-4000"
	for range 3 {
		d := decimal.MustParse(huge)
		_, _ = d.Mul(d)
		_, _, _ = decimal.ParseWithContext(huge, decimal.Context{}.WithBudget(decimal.Budget{MaxDigits: 3}))
		for _, ctx := range []decimal.Context{decimal.Decimal32Context(), decimal.Decimal64Context(), decimal.Decimal128Context()} {
			_, _, _ = d.AddWithContext(decimal.One(), ctx)
		}
		_, _ = d.Scientific(40)
		_, _ = d.BigInt(nil)
	}
	second := portableResultLines(t)
	if len(first) != len(second) {
		t.Fatalf("result count changed: %d then %d", len(first), len(second))
	}
	for i := range first {
		if first[i] != second[i] {
			t.Fatalf("line %d changed after unrelated use: %q then %q", i, first[i], second[i])
		}
	}
}

func portableResultLines(t *testing.T) []string {
	t.Helper()
	rng := randv2.New(randv2.NewPCG(20260925, 42))
	operand := func() string {
		var b strings.Builder
		if rng.IntN(3) == 0 {
			b.WriteByte('-')
		}
		digits := 1 + rng.IntN(60)
		if rng.IntN(4) == 0 {
			digits = 1 + rng.IntN(4)
		}
		for i := range digits {
			d := byte('0' + rng.IntN(10))
			if i == 0 && rng.IntN(5) == 0 {
				d = '9'
			}
			b.WriteByte(d)
		}
		if rng.IntN(10) == 0 { // long zero runs and zero coefficients
			b.WriteString(strings.Repeat("0", rng.IntN(40)))
		}
		fmt.Fprintf(&b, "E%d", rng.IntN(81)-40)
		return b.String()
	}
	var lines []string
	emit := func(format string, args ...any) { lines = append(lines, fmt.Sprintf(format, args...)) }
	result := func(d decimal.Decimal, err error) string {
		if err != nil {
			return "err:" + err.Error()
		}
		return d.String() + "@" + strconv.Itoa(int(d.Exponent()))
	}
	for _, src := range []any{*big.NewInt(-123), big.NewInt(256), *big.NewRat(11, 10), big.NewRat(1, 8)} {
		var d decimal.Decimal
		err := d.Scan(src)
		emit("scan %T %s", src, result(d, err))
	}
	contexts := []decimal.Context{decimal.Decimal32Context(), decimal.Decimal64Context(), decimal.Decimal128Context()}
	for mode := decimal.RoundingMode(0); mode <= decimal.Exact; mode++ {
		ctx, err := decimal.NewContext(7, mode, &decimal.ExponentGuards{Emin: -20, Emax: 20}, 0)
		if err != nil {
			t.Fatal(err)
		}
		contexts = append(contexts, ctx)
	}
	values := make([]decimal.Decimal, 0, 400)
	for range 400 {
		text := operand()
		d, err := decimal.Parse(text)
		emit("parse %s %s", text, result(d, err))
		for _, mode := range []decimal.RoundingMode{decimal.TiesToEven, decimal.TowardNegativeInfinity} {
			q, c, qerr := decimal.ParseToExponent(text, -2, mode)
			emit("parsetoexp %v %s %v", mode, result(q, qerr), c)
		}
		pc, c, perr := decimal.ParseWithContext([]byte(text), decimal.Decimal64Context())
		emit("parsectx %s %v", result(pc, perr), c)
		var scanned decimal.Decimal
		serr := scanned.Scan([]byte(text))
		emit("scan %s", result(scanned, serr))
		if err != nil {
			continue
		}
		values = append(values, d)
		// []byte carriers reach the portable SIMD span kernel for long digit
		// runs; the string path uses SWAR, so both kernels feed the digest.
		var fromText, fromJSON decimal.Decimal
		long := text
		if rng.IntN(2) == 0 {
			long = strings.Repeat(strings.TrimPrefix(strings.SplitN(text, "E", 2)[0], "-"), 1+rng.IntN(24)) + "." + strings.Repeat("7", rng.IntN(600))
		}
		err = fromText.UnmarshalText([]byte(long))
		emit("unmarshaltext %s %s", long, result(fromText, err))
		err = fromJSON.UnmarshalJSON([]byte(long))
		emit("unmarshaljson %s", result(fromJSON, err))
		canonical, err := d.Text(0)
		emit("text %s %v digits=%d sign=%d reduce=%s", canonical, err, d.CoefficientDigits(), d.Sign(), d.Reduce())
		fixed, err := d.Fixed(3)
		emit("fixed %s %v", fixed, err)
		sci, err := d.Scientific(6)
		emit("sci %s %v", sci, err)
		eng, err := d.Engineering()
		emit("eng %s %v", eng, err)
		js, err := json.Marshal(d)
		emit("json %s %v", js, err)
		i64, err := d.Int64()
		emit("int64 %d %v", i64, err)
		hi, lo, fits := d.CoefficientInt128()
		lane, err := d.AppendTwosComplement(nil, 32, binary.LittleEndian)
		emit("lanes %d %d %t %x %v", hi, lo, fits, lane, err)
		form, negative, magnitude, exponent := decimal.SQLDecimal{Decimal: d}.Decompose(nil)
		var composed decimal.Decimal
		err = composed.Compose(form, negative, magnitude, exponent)
		emit("decompose %d %t %x %d %s %v", form, negative, magnitude, exponent, composed, err)
		u64, err := d.Uint64()
		emit("uint64 %d %v", u64, err)
		bi, err := d.BigInt(nil)
		emit("bigint %v %v", bi, err)
		if bi != nil {
			back, err := decimal.FromBigInt(bi)
			emit("frombigint %s", result(back, err))
		}
		for mode := decimal.RoundingMode(0); mode <= decimal.Exact; mode++ {
			for _, e := range []int32{-5, 0, 3} {
				q, c, err := d.Quantize(e, mode)
				emit("quantize %v %d %s %v", mode, e, result(q, err), c)
			}
			r, c, err := d.RoundToIntegral(mode)
			emit("integral %v %s %v", mode, result(r, err), c)
		}
	}
	// Exponents at the int32 limits run only through operations whose output
	// is bounded (canonical text, comparison, finite-precision contexts and
	// budgeted arithmetic); exact unbudgeted operations on them legitimately
	// produce coefficients of about 2^31 digits.
	budget := decimal.Budget{MaxDigits: 80, MaxWork: 1 << 16}
	for range 120 {
		exponent := 2147483647 - rng.IntN(80)
		if rng.IntN(2) == 0 {
			exponent = -2147483648 + rng.IntN(80)
		}
		text := strings.SplitN(operand(), "E", 2)[0] + "E" + strconv.Itoa(exponent)
		d, err := decimal.Parse(text)
		emit("extreme parse %s %s", text, result(d, err))
		if err != nil {
			continue
		}
		canonical, err := d.Text(0)
		emit("extreme text %s %v digits=%d", canonical, err, d.CoefficientDigits())
		sci, err := d.Scientific(4)
		emit("extreme sci %s %v", sci, err)
		js, err := json.Marshal(d)
		emit("extreme json %s %v", js, err)
		i64, err := d.Int64()
		emit("extreme int64 %d %v", i64, err)
		other := values[rng.IntN(len(values))]
		emit("extreme cmp %d %t", d.Compare(other), d.Equal(other))
		for _, pair := range [][2]decimal.Decimal{{d, other}, {d, d}} {
			sum, _, err := pair[0].AddWithContext(pair[1], decimal.Context{}.WithBudget(budget))
			emit("extreme addbudget %s", result(sum, err))
			prod, _, err := pair[0].MulWithContext(pair[1], decimal.Context{}.WithBudget(budget))
			emit("extreme mulbudget %s", result(prod, err))
			for _, ctx := range contexts {
				s, c, err := pair[0].AddWithContext(pair[1], ctx.WithBudget(budget))
				emit("extreme ctxadd %s %v", result(s, err), c)
				p, c, err := pair[0].MulWithContext(pair[1], ctx.WithBudget(budget))
				emit("extreme ctxmul %s %v", result(p, err), c)
				r, c, err := pair[0].RoundToIntegralWithContext(ctx.WithBudget(budget))
				emit("extreme ctxintegral %s %v", result(r, err), c)
			}
		}
	}
	for i := 0; i+1 < len(values); i++ {
		a, b := values[i], values[i+1]
		emit("cmp %d eq=%t min=%s max=%s", a.Compare(b), a.Equal(b), a.Min(b), a.Max(b))
		sum, err := a.Add(b)
		emit("add %s", result(sum, err))
		diff, err := a.Sub(b)
		emit("sub %s", result(diff, err))
		prod, err := a.Mul(b)
		emit("mul %s", result(prod, err))
		capped, _, err := a.MulWithContext(b, decimal.Context{}.WithBudget(decimal.Budget{MaxDigits: 40}))
		emit("mulbudget %s", result(capped, err))
		quotient, err := a.Div(b)
		emit("div %s", result(quotient, err))
		for _, mode := range []decimal.RoundingMode{decimal.TiesToEven, decimal.TowardNegativeInfinity, decimal.Exact} {
			q, c, err := a.DivToExponent(b, b.Exponent()-3, mode)
			emit("divtoexp %v %s %v", mode, result(q, err), c)
		}
		for _, ctx := range contexts {
			q, c, err := a.DivWithContext(b, ctx)
			emit("ctxdiv %s %v", result(q, err), c)
			s, c, err := a.AddWithContext(b, ctx)
			emit("ctxadd %s %v", result(s, err), c)
			p, c, err := a.MulWithContext(b, ctx)
			emit("ctxmul %s %v", result(p, err), c)
			qz, c, err := a.QuantizeWithContext(b.Exponent(), ctx)
			emit("ctxquantize %s %v", result(qz, err), c)
		}
		f, c := a.Float64()
		lo, lc, _ := a.Float64Rounded(decimal.TowardNegativeInfinity)
		hi, hc, _ := a.Float64Rounded(decimal.TowardPositiveInfinity)
		cmp, _ := a.CompareFloat64(f)
		emit("float64 %x %v %x %v %x %v cmp=%d", math.Float64bits(f), c, math.Float64bits(lo), lc, math.Float64bits(hi), hc, cmp)
		ra, err := a.Rat(nil)
		if err != nil {
			t.Fatal(err)
		}
		emit("rat %s", ra.RatString())
		if rb, err := b.Rat(nil); err == nil && rb.Sign() != 0 {
			r := new(big.Rat).Quo(ra, rb)
			fr, err := decimal.FromRat(r)
			emit("fromrat %s", result(fr, err))
			fr, c, err := decimal.FromRatToExponent(r, b.Exponent()-3, decimal.TiesToEven)
			emit("fromrattoexp %s %v", result(fr, err), c)
			for _, ctx := range contexts {
				fr, c, err := decimal.FromRatWithContext(r, ctx)
				emit("ctxfromrat %s %v", result(fr, err), c)
			}
		}
	}
	for _, bitsIn := range []uint64{0x3FB999999999999A, 1, 0x000FFFFFFFFFFFFF, 0x7FEFFFFFFFFFFFFF, 0xC005666666666666, 0x4340000000000001, 0x8000000000000000} {
		v := math.Float64frombits(bitsIn)
		s, err := decimal.FromFloat64(v)
		emit("fromfloat64 %x %s", bitsIn, result(s, err))
		e, err := decimal.FromFloat64Exact(v)
		emit("fromfloat64exact %x %s", bitsIn, result(e, err))
		for _, mode := range []decimal.RoundingMode{decimal.TiesToEven, decimal.TowardNegativeInfinity, decimal.AwayFromZero} {
			q, c, err := decimal.FromFloat64ToExponent(v, -2, mode)
			emit("fromfloat64toexp %x %v %s %v", bitsIn, mode, result(q, err), c)
		}
		for _, ctx := range contexts {
			q, c, err := decimal.FromFloat64WithContext(v, ctx)
			emit("ctxfromfloat64 %x %s %v", bitsIn, result(q, err), c)
		}
	}
	for _, text := range []string{"1e-99999999999", "-1e-99999999999", "1e+99999999999", "0.125" + strings.Repeat("0", 1000) + "1", "0e-99999999999"} {
		for _, mode := range []decimal.RoundingMode{decimal.TiesToEven, decimal.TowardPositiveInfinity, decimal.TowardNegativeInfinity} {
			q, c, err := decimal.ParseToExponent(text, -2, mode)
			emit("parsetoexp-magnitude %.20s %v %s %v", text, mode, result(q, err), c)
		}
		q, c, err := decimal.ParseWithContext(text, decimal.Decimal64Context())
		emit("parsectx-magnitude %.20s %s %v", text, result(q, err), c)
	}
	for _, src := range []any{int64(-9223372036854775808), 0.1, -2.5e-320, decimal.SQLDecimal{Decimal: decimal.MustParse("-1.10")}, "NaN", true} {
		var scanned decimal.Decimal
		err := scanned.Scan(src)
		emit("scan-kind %T %s", src, result(scanned, err))
		var null decimal.NullDecimal
		err = null.Scan(src)
		emit("scan-null %T %t %s", src, null.Valid, result(null.Decimal, err))
	}
	return lines
}

// TestOutOfScopeOperationsAreNotExported checks the operation catalogue:
// no exported identifier —
// function, method, type, variable or constant, parsed from the library's
// non-test sources — starts with an excluded operation's stem followed by
// the end of the name, a digit or an uppercase letter (so NextUp, Exp10,
// Log1p, CompareTotalMagnitude and the type Money are caught, while
// Exponent is not). The catalogue admits exactly the four forms of Exp,
// Ln, Log10, PowDecimal and the thirteen trigonometric and hyperbolic
// functions; every other stem stays excluded, and Pow and
// its forms still take an int32 exponent. MustParse is the only function that panics.
// A bare FMA is absent, with the context form present as a vacuity guard.
func TestOutOfScopeOperationsAreNotExported(t *testing.T) {
	excluded := regexp.MustCompile(`^(?i:` +
		`exp|expm1|ln|log|sin|cos|tan|sqrtreal|powreal|powdecimal|ulp|` +
		`next|maxmag|minmag|` +
		`comparesignal|comparetotal|copysign|copyabs|copynegate|nan|inf|isnan|isinf|payload|signaling|quiet|` +
		`and|or|xor|invert|logical|shift|rotate|scaleb|samequantum|class|` +
		`allocate|prorate|distribute|split|placement|roundcash|roundper|perline|perinvoice|` +
		`currency|money|locale|grouping|exchange|convertcurrency` +
		`)([0-9A-Z]|$)`)
	admitted := regexp.MustCompile(`^(Exp|Ln|Log10|PowDecimal|Sin|Cos|Tan|Asin|Acos|Atan|Atan2|Sinh|Cosh|Tanh|Asinh|Acosh|Atanh)(WithBudget|WithContext)?$`)
	outOfScope := func(name string) bool { return excluded.MatchString(name) && !admitted.MatchString(name) }
	for name, want := range map[string]bool{
		"Exp10": true, "Expm1": true, "Ulp": true, "Log1p": true, "Log2": true, "LogB": true, "LnGamma": true, "SinPi": true, "Tan2": true, "CosPi": true,
		"PowReal": true, "PowDecimalToExponent": true, "NextUp": true, "NextToward": true,
		"CompareTotalMagnitude": true, "CopySign": true, "ScaleB": true, "Allocate": true, "RoundPerLineItems": true,
		"Money": true, "NaN": true, "Exponent": false, "Sqrt": false, "Shape": false, "Sum": false, "Compare": false,
		"Exp": false, "ExpWithContext": false, "LnWithContext": false, "Log10WithContext": false, "PowDecimal": false,
		"Sin": false, "Atan2WithContext": false, "AcoshWithContext": false,
	} {
		if outOfScope(name) != want {
			t.Fatalf("exclusion predicate on %s = %v, want %v", name, !want, want)
		}
	}
	fset := token.NewFileSet()
	files, err := filepath.Glob("*.go")
	if err != nil {
		t.Fatal(err)
	}
	var names, musts []string
	for _, file := range files {
		if strings.HasSuffix(file, "_test.go") {
			continue
		}
		f, err := parser.ParseFile(fset, file, nil, parser.SkipObjectResolution)
		if err != nil {
			t.Fatal(err)
		}
		for _, decl := range f.Decls {
			switch decl := decl.(type) {
			case *ast.FuncDecl:
				if !decl.Name.IsExported() {
					continue
				}
				names = append(names, decl.Name.Name)
				if strings.HasPrefix(decl.Name.Name, "Must") {
					musts = append(musts, decl.Name.Name)
				}
				if regexp.MustCompile(`^Pow(With|$)`).MatchString(decl.Name.Name) && decl.Type.Params.NumFields() > 0 {
					if ident, ok := decl.Type.Params.List[0].Type.(*ast.Ident); !ok || ident.Name != "int32" {
						t.Errorf("%s takes a non-int32 exponent", decl.Name.Name)
					}
				}
			case *ast.GenDecl:
				for _, spec := range decl.Specs {
					switch spec := spec.(type) {
					case *ast.TypeSpec:
						names = append(names, spec.Name.Name)
					case *ast.ValueSpec:
						for _, n := range spec.Names {
							if n.IsExported() {
								names = append(names, n.Name)
							}
						}
					}
				}
			}
		}
	}
	if len(names) < 150 {
		t.Fatalf("parsed only %d exported identifiers", len(names))
	}
	for _, name := range names {
		if ast.IsExported(name) && outOfScope(name) {
			t.Errorf("%s is an out-of-scope operation", name)
		}
	}
	if len(musts) != 1 || musts[0] != "MustParse" {
		t.Errorf("Must functions %v, want only MustParse", musts)
	}
	// There is no bare FMA: Mul then Add is as fast. Only the context form
	// and its estimator (EstimateFMA takes the Context) exist.
	found := map[string]bool{}
	for _, name := range names {
		found[name] = true
	}
	for _, name := range []string{"FMA"} {
		if found[name] {
			t.Errorf("%s must not exist: FMA has only a context form", name)
		}
	}
	for _, name := range []string{"FMAWithContext", "EstimateFMA"} {
		if !found[name] {
			t.Errorf("%s is missing: the exclusion check is vacuous", name)
		}
	}
}

// roundingVocabularyViolations reports the rounding vocabulary breaks in
// one line of documentation or source: "half up" or "half down" (any
// spacing, hyphen, underscore or case, so identifiers such as HalfUp match)
// unless qualified in place as "(= ties ...)" (the gloss itself may cite
// GDA's round-half-up), and "commercial rounding" or
// "banker's rounding" unless glossed to TiesAwayFromZero or TiesToEven.
func roundingVocabularyViolations(line string) []string {
	var bad []string
	lower := strings.ToLower(line)
	for _, m := range roundingHalfRE.FindAllStringIndex(lower, -1) {
		before := lower[:m[0]]
		inGloss := strings.LastIndex(before, "(= ties") > strings.LastIndex(before, ")")
		if !inGloss && !strings.HasPrefix(strings.TrimLeft(lower[m[1]:], " "), "(= ties") {
			bad = append(bad, "unqualified "+line[m[0]:m[1]])
		}
	}
	for alias, gloss := range map[string]string{"commercial rounding": "TiesAwayFromZero", "banker's rounding": "TiesToEven", "bankers rounding": "TiesToEven", "bankers' rounding": "TiesToEven"} {
		if strings.Contains(lower, alias) && !strings.Contains(line, gloss) {
			bad = append(bad, "unglossed "+alias)
		}
	}
	return bad
}

var roundingHalfRE = regexp.MustCompile(`half[\s_-]*(up|down)`)

// TestRoundingVocabularyScan checks the rounding vocabulary: no exported identifier,
// comment or user document of the library contains "half up" or "half
// down" unqualified, and the commercial/banker's aliases appear only glossed
// to their mode. The matcher is checked on hand-written
// lines first so the scan cannot pass vacuously.
func TestRoundingVocabularyScan(t *testing.T) {
	for line, want := range map[string]int{
		"RoundHalfUp":              1,
		"rounds half-down on ties": 1,
		"ROUND_HALF_UP":            1,
		"half up (= ties away from zero, GDA round-half-up)": 0,
		"commercial rounding":                                1,
		"commercial rounding (TiesAwayFromZero)":             0,
		"banker's rounding is TiesToEven":                    0,
		"banker's rounding":                                  1,
		"TiesAwayFromZero rounds a half away from zero":      0,
	} {
		if got := len(roundingVocabularyViolations(line)); got != want {
			t.Fatalf("matcher on %q found %d violations, want %d", line, got, want)
		}
	}
	files, err := filepath.Glob("*.go")
	if err != nil {
		t.Fatal(err)
	}
	var docs []string
	for _, file := range files {
		if !strings.HasSuffix(file, "_test.go") || file == "example_test.go" {
			docs = append(docs, file)
		}
	}
	docs = append(docs, "README.md", "ARCHITECTURE.md")
	for _, pattern := range []string{"docs/*.md", "docs/*/*.md"} {
		guides, err := filepath.Glob(pattern)
		if err != nil {
			t.Fatal(err)
		}
		docs = append(docs, guides...)
	}
	scannedLines := 0
	for _, file := range docs {
		data, err := os.ReadFile(file)
		if err != nil {
			t.Fatal(err)
		}
		for i, line := range strings.Split(string(data), "\n") {
			scannedLines++
			for _, v := range roundingVocabularyViolations(line) {
				t.Errorf("%s:%d: %s", file, i+1, v)
			}
		}
	}
	if len(docs) < 30 || scannedLines < 10000 {
		t.Fatalf("scanned %d files, %d lines: the library sources are missing", len(docs), scannedLines)
	}
}

// TestZeroValueBehavesAsZero checks that the zero value is usable: an
// uninitialized Decimal, used without any initialization step in every
// operation and conversion family, gives the hand-derived results of the
// finite value 0 and exactly what decimal.Zero() and MustParse("0") give.
func TestZeroValueBehavesAsZero(t *testing.T) {
	show := func(v any, err error) string {
		if d, ok := v.(decimal.Decimal); ok {
			v = d.String()
		}
		return fmt.Sprintf("%v|%v", v, err)
	}
	ops := []struct {
		name string
		run  func(decimal.Decimal) string
		want string
	}{
		{"String", func(z decimal.Decimal) string { return z.String() }, "0"},
		{"IsZero/Sign/Exponent/Digits", func(z decimal.Decimal) string {
			return fmt.Sprint(z.IsZero(), z.Sign(), z.Exponent(), z.CoefficientDigits())
		}, "true 0 0 1"},
		{"Add", func(z decimal.Decimal) string { return show(z.Add(decimal.MustParse("1.5"))) }, "1.5|<nil>"},
		{"Sub", func(z decimal.Decimal) string { return show(z.Sub(decimal.MustParse("1.5"))) }, "-1.5|<nil>"},
		{"Mul", func(z decimal.Decimal) string { return show(z.Mul(decimal.MustParse("1.5"))) }, "0.0|<nil>"},
		{"Div", func(z decimal.Decimal) string { return show(z.Div(decimal.MustParse("4"))) }, "0|<nil>"},
		{"Quantize", func(z decimal.Decimal) string {
			q, c, err := z.Quantize(-2, decimal.TiesToEven)
			return fmt.Sprintf("%s %d %v", q, c, err)
		}, "0.00 0 <nil>"},
		{"Neg/Abs/Reduce", func(z decimal.Decimal) string { return z.Neg().String() + z.Abs().String() + z.Reduce().String() }, "000"},
		{"Sqrt", func(z decimal.Decimal) string { return show(z.Sqrt()) }, "0|<nil>"},
		{"Pow0", func(z decimal.Decimal) string { return show(z.Pow(0)) }, "1|<nil>"},
		{"Int64", func(z decimal.Decimal) string { return show(z.Int64()) }, "0|<nil>"},
		{"Uint64", func(z decimal.Decimal) string { return show(z.Uint64()) }, "0|<nil>"},
		{"BigInt", func(z decimal.Decimal) string { return show(z.BigInt(nil)) }, "0|<nil>"},
		{"Rat", func(z decimal.Decimal) string { return show(z.Rat(nil)) }, "0/1|<nil>"},
		{"Float64", func(z decimal.Decimal) string { f, c := z.Float64(); return fmt.Sprint(f, c) }, "0 0"},
		{"Text", func(z decimal.Decimal) string { return show(z.Text(0)) }, "0|<nil>"},
		{"Fixed", func(z decimal.Decimal) string { return show(z.Fixed(2)) }, "0.00|<nil>"},
		{"Engineering", func(z decimal.Decimal) string { return show(z.Engineering()) }, "0E+0|<nil>"},
		{"MarshalJSON", func(z decimal.Decimal) string { b, err := z.MarshalJSON(); return show(string(b), err) }, "0|<nil>"},
		{"Value", func(z decimal.Decimal) string { return show(z.Value()) }, "0|<nil>"},
		{"Compare/Equal", func(z decimal.Decimal) string {
			return fmt.Sprint(z.Compare(decimal.MustParse("0.00")), z.Equal(decimal.MustParse("0E+9")), z.Compare(decimal.One()))
		}, "0 true -1"},
	}
	var zero decimal.Decimal
	for _, op := range ops {
		for _, z := range []decimal.Decimal{zero, decimal.Zero(), decimal.MustParse("0")} {
			if got := op.run(z); got != op.want {
				t.Errorf("%s on zero = %q, want %q", op.name, got, op.want)
			}
		}
	}
	if _, err := zero.Pow(-1); !errors.Is(err, decimal.ErrDivisionByZero) {
		t.Errorf("zero value Pow(-1) error = %v, want ErrDivisionByZero", err)
	}
}

// TestConstructorsNeverPanic checks that constructors never panic on input
// values: every exported constructor except MustParse,
// including each budgeted and context form, fed non-finite
// floats, nil sources, an invalid mode, a nil byte order, empty and hostile
// bytes and 4,000 seeded random byte strings, returns a value or an error
// and never panics. Hand-derived identities pin the defined refusals, and a
// failed constructor returns the zero Decimal.
func TestConstructorsNeverPanic(t *testing.T) {
	call := func(name string, run func() (decimal.Decimal, error), want error) {
		t.Helper()
		var d decimal.Decimal
		var err error
		func() {
			defer func() {
				if r := recover(); r != nil {
					t.Errorf("%s panicked: %v", name, r)
				}
			}()
			d, err = run()
		}()
		if want != nil && !errors.Is(err, want) {
			t.Errorf("%s error = %v, want %v", name, err, want)
		}
		if err != nil && !d.Equal(decimal.Decimal{}) || err != nil && d.Exponent() != 0 {
			t.Errorf("%s failed with a nonzero value %s", name, d)
		}
	}
	drop := func(d decimal.Decimal, _ decimal.Conditions, err error) (decimal.Decimal, error) { return d, err }
	badMode := decimal.RoundingMode(200)
	ctx := decimal.Decimal128Context()
	for _, f := range []float64{math.NaN(), math.Inf(1), math.Inf(-1)} {
		call("FromFloat64", func() (decimal.Decimal, error) { return decimal.FromFloat64(f) }, decimal.ErrConversionSyntax)
		call("FromFloat64Exact", func() (decimal.Decimal, error) { return decimal.FromFloat64Exact(f) }, decimal.ErrConversionSyntax)
		call("FromFloat64ToExponent", func() (decimal.Decimal, error) { return drop(decimal.FromFloat64ToExponent(f, 0, decimal.TiesToEven)) }, decimal.ErrConversionSyntax)
		call("FromFloat64ToExponentWithBudget", func() (decimal.Decimal, error) {
			return drop(decimal.FromFloat64ToExponentWithBudget(f, 0, decimal.TiesToEven, decimal.Budget{}))
		}, decimal.ErrConversionSyntax)
		call("FromFloat64WithContext", func() (decimal.Decimal, error) { return drop(decimal.FromFloat64WithContext(f, ctx)) }, decimal.ErrConversionSyntax)
	}
	call("FromFloat64ToExponent bad mode", func() (decimal.Decimal, error) { return drop(decimal.FromFloat64ToExponent(0.1, -2, badMode)) }, decimal.ErrInvalidContext)
	call("FromBigInt nil", func() (decimal.Decimal, error) { return decimal.FromBigInt(nil) }, decimal.ErrConversionSyntax)
	call("FromBigIntWithBudget nil", func() (decimal.Decimal, error) {
		return decimal.FromBigIntWithBudget(nil, decimal.Budget{})
	}, decimal.ErrConversionSyntax)
	call("FromRat nil", func() (decimal.Decimal, error) { return decimal.FromRat(nil) }, decimal.ErrConversionSyntax)
	call("FromRatWithContext at Context{} with a budget, nil", func() (decimal.Decimal, error) {
		res, _, resErr := decimal.FromRatWithContext(nil, decimal.Context{}.WithBudget(decimal.Budget{}))
		return res, resErr
	}, decimal.ErrConversionSyntax)
	call("FromRatWithContext nil", func() (decimal.Decimal, error) { return drop(decimal.FromRatWithContext(nil, ctx)) }, decimal.ErrConversionSyntax)
	call("FromRatToExponent nil", func() (decimal.Decimal, error) { return drop(decimal.FromRatToExponent(nil, 0, decimal.TiesToEven)) }, decimal.ErrConversionSyntax)
	call("FromRatToExponent bad mode", func() (decimal.Decimal, error) {
		return drop(decimal.FromRatToExponent(big.NewRat(1, 3), 0, badMode))
	}, decimal.ErrInvalidContext)
	call("FromRatWithContext with a budget, nil", func() (decimal.Decimal, error) {
		return drop(decimal.FromRatWithContext(nil, ctx.WithBudget(decimal.Budget{})))
	}, decimal.ErrConversionSyntax)
	call("FromRatToExponentWithBudget nil", func() (decimal.Decimal, error) {
		return drop(decimal.FromRatToExponentWithBudget(nil, 0, decimal.TiesToEven, decimal.Budget{}))
	}, decimal.ErrConversionSyntax)
	call("FromRatToExponentWithBudget bad mode", func() (decimal.Decimal, error) {
		return drop(decimal.FromRatToExponentWithBudget(big.NewRat(1, 3), 0, badMode, decimal.Budget{}))
	}, decimal.ErrInvalidContext)
	call("NewTwosComplementWithBudget nil order", func() (decimal.Decimal, error) {
		return decimal.NewTwosComplementWithBudget([]byte{1}, nil, 0, decimal.Budget{})
	}, decimal.ErrInvalidOperation)
	call("ParseToExponentWithBudget bad mode", func() (decimal.Decimal, error) {
		return drop(decimal.ParseToExponentWithBudget("1.25", -1, badMode, decimal.Budget{}))
	}, decimal.ErrInvalidContext)
	call("NewTwosComplement nil bytes", func() (decimal.Decimal, error) { return decimal.NewTwosComplement(nil, binary.BigEndian, 0) }, decimal.ErrConversionSyntax)
	call("NewTwosComplement nil order", func() (decimal.Decimal, error) { return decimal.NewTwosComplement([]byte{1}, nil, 0) }, decimal.ErrInvalidOperation)
	call("ParseJSONWithBudget nil", func() (decimal.Decimal, error) { return decimal.ParseJSONWithBudget(nil, decimal.Budget{}) }, decimal.ErrConversionSyntax)
	call("ParseToExponent bad mode", func() (decimal.Decimal, error) { return drop(decimal.ParseToExponent("1.25", -1, badMode)) }, decimal.ErrInvalidContext)
	for _, n := range []struct {
		hi  int64
		lo  uint64
		exp int32
	}{{math.MinInt64, 0, math.MinInt32}, {-1, math.MaxUint64, math.MaxInt32}, {math.MaxInt64, math.MaxUint64, 0}} {
		call("NewInt128", func() (decimal.Decimal, error) { return decimal.NewInt128(n.hi, n.lo, n.exp), nil }, nil)
	}
	call("New extremes", func() (decimal.Decimal, error) { return decimal.New(math.MinInt64, math.MinInt32), nil }, nil)
	call("FromUint64 max", func() (decimal.Decimal, error) { return decimal.FromUint64(math.MaxUint64), nil }, nil)
	call("FromInt64 min", func() (decimal.Decimal, error) { return decimal.FromInt64(math.MinInt64), nil }, nil)
	call("Zero/One", func() (decimal.Decimal, error) { return decimal.Zero().Add(decimal.One()) }, nil)
	rng := rand.New(rand.NewSource(20260928))
	const alphabet = "0123456789+-.eE_ \"\\nNaIiFf\x00\xff\u00e9"
	for i := range 4000 {
		b := make([]byte, rng.Intn(64))
		for j := range b {
			if i%2 == 0 {
				b[j] = alphabet[rng.Intn(len(alphabet))]
			} else {
				b[j] = byte(rng.Intn(256))
			}
		}
		call("Parse", func() (decimal.Decimal, error) { return decimal.Parse(b) }, nil)
		call("ParseJSONWithBudget", func() (decimal.Decimal, error) { return decimal.ParseJSONWithBudget(b, decimal.Budget{}) }, nil)
		call("ParseWithContext", func() (decimal.Decimal, error) { return drop(decimal.ParseWithContext(b, ctx)) }, nil)
		call("ParseToExponent", func() (decimal.Decimal, error) { return drop(decimal.ParseToExponent(b, -2, decimal.TiesToEven)) }, nil)
		call("NewTwosComplement", func() (decimal.Decimal, error) {
			return decimal.NewTwosComplement(b, binary.LittleEndian, int32(rng.Uint32()))
		}, nil)
		call("NewTwosComplementWithBudget", func() (decimal.Decimal, error) {
			return decimal.NewTwosComplementWithBudget(b, binary.BigEndian, int32(rng.Uint32()), decimal.Budget{MaxInputDigits: 40})
		}, nil)
		call("ParseWithContext", func() (decimal.Decimal, error) {
			res, _, resErr := decimal.ParseWithContext(b, decimal.Context{}.WithBudget(decimal.Budget{MaxInputBytes: 32}))
			return res, resErr
		}, nil)
		call("ParseWithContext", func() (decimal.Decimal, error) {
			return drop(decimal.ParseWithContext(b, ctx.WithBudget(decimal.Budget{MaxInputBytes: 32})))
		}, nil)
		call("ParseToExponentWithBudget", func() (decimal.Decimal, error) {
			return drop(decimal.ParseToExponentWithBudget(b, int32(rng.Uint32()), decimal.TowardZero, decimal.Budget{MaxInputBytes: 32, MaxDigits: 64}))
		}, nil)
	}
}

// exportedSurface is the parsed exported API of the library package: every
// exported top-level function and method with its receiver type name
// (pointer receivers prefixed with "*"), every exported type with its
// declared type expression, and the package's imports.
type exportedSurface struct {
	funcs   map[string]*ast.FuncDecl // "Name" or "Recv.Name" / "*Recv.Name"
	types   map[string]ast.Expr
	imports []string
}

func parseExportedSurface(t *testing.T) exportedSurface {
	t.Helper()
	s := exportedSurface{funcs: map[string]*ast.FuncDecl{}, types: map[string]ast.Expr{}}
	files, err := filepath.Glob("*.go")
	if err != nil {
		t.Fatal(err)
	}
	fset := token.NewFileSet()
	for _, file := range files {
		if strings.HasSuffix(file, "_test.go") {
			continue
		}
		f, err := parser.ParseFile(fset, file, nil, parser.SkipObjectResolution)
		if err != nil {
			t.Fatal(err)
		}
		for _, imp := range f.Imports {
			path, _ := strconv.Unquote(imp.Path.Value)
			s.imports = append(s.imports, path)
		}
		for _, decl := range f.Decls {
			switch decl := decl.(type) {
			case *ast.FuncDecl:
				if !decl.Name.IsExported() {
					continue
				}
				key := decl.Name.Name
				if decl.Recv != nil {
					recv := decl.Recv.List[0].Type
					prefix := ""
					if star, ok := recv.(*ast.StarExpr); ok {
						recv, prefix = star.X, "*"
					}
					if ident, ok := recv.(*ast.Ident); ok {
						if !ident.IsExported() {
							continue
						}
						key = prefix + ident.Name + "." + key
					}
				}
				s.funcs[key] = decl
			case *ast.GenDecl:
				for _, spec := range decl.Specs {
					if ts, ok := spec.(*ast.TypeSpec); ok && ts.Name.IsExported() {
						s.types[ts.Name.Name] = ts.Type
					}
				}
			}
		}
	}
	if len(s.funcs) < 150 || len(s.types) < 15 {
		t.Fatalf("parsed %d exported functions and %d types: the library sources are missing", len(s.funcs), len(s.types))
	}
	return s
}

// carrierViolations walks a type expression at any depth (slices, arrays,
// maps, channels, exported struct fields, function signatures) and reports a
// *Decimal or *NullDecimal (a mutable carrier), a function type (a
// callback or iterator) or an iter package type (an iterator).
func carrierViolations(expr ast.Expr) []string {
	var bad []string
	ast.Inspect(expr, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.StructType: // only exported fields are public surface
			for _, field := range n.Fields.List {
				exported := len(field.Names) == 0 // embedded
				for _, name := range field.Names {
					exported = exported || name.IsExported()
				}
				if exported {
					bad = append(bad, carrierViolations(field.Type)...)
				}
			}
			return false
		case *ast.StarExpr:
			if ident, ok := n.X.(*ast.Ident); ok && (ident.Name == "Decimal" || ident.Name == "NullDecimal") {
				bad = append(bad, "passes *"+ident.Name+" (mutable carrier)")
			}
		case *ast.FuncType:
			bad = append(bad, "has a function type (callback or iterator)")
		case *ast.SelectorExpr:
			if x, ok := n.X.(*ast.Ident); ok && x.Name == "iter" {
				bad = append(bad, "uses iter."+n.Sel.Name+" (iterator)")
			}
		}
		return true
	})
	return bad
}

// TestPublicSurfaceHasNoCarriersIteratorsOrContainers scans the exported API
// for surfaces the design excludes, each checked against a
// hand-written allowlist or ban:
//   - no destination-style mutable carrier. The only exported
//     pointer-receiver methods on library values are the stdlib inbound
//     contracts (Scan, UnmarshalText/JSON, Compose) and the error types'
//     methods; no exported function signature or type mentions *Decimal
//     or *NullDecimal at any nesting depth ([]*Decimal, struct fields).
//   - no iterator surface (no import of iter, no function type at
//     any depth of an exported signature or type).
//   - no unseeded public hash; the only hash surface is the seeded
//     Hasher pair.
//   - no decimal-keyed map or set container type.
//   - traps live on the context: only NewContext and
//     Context.WithTraps accept Conditions, and Decimal has no Conditions
//     field.
//   - no CSV, FIX, ISO or other envelope type.
func TestPublicSurfaceHasNoCarriersIteratorsOrContainers(t *testing.T) {
	s := parseExportedSurface(t)
	wantPointer := map[string]bool{
		"*Decimal.Compose": true, "*Decimal.ComposeWithBudget": true, "*Decimal.Scan": true,
		"*Decimal.ScanWithBudget": true, "*Decimal.UnmarshalJSON": true, "*Decimal.UnmarshalText": true,
		"*NullDecimal.Scan": true, "*NullDecimal.ScanWithBudget": true, "*NullDecimal.UnmarshalJSON": true,
	}
	for key, decl := range s.funcs {
		if strings.HasPrefix(key, "*") && !wantPointer[key] && !strings.HasSuffix(strings.SplitN(key, ".", 2)[0], "Error") {
			t.Errorf("unexpected pointer-receiver method %s (mutable carrier)", key)
		}
		for _, list := range []*ast.FieldList{decl.Type.Params, decl.Type.Results} {
			if list == nil {
				continue
			}
			for _, field := range list.List {
				for _, v := range carrierViolations(field.Type) {
					t.Errorf("%s: %s", key, v)
				}
				if ident, ok := field.Type.(*ast.Ident); ok && ident.Name == "Conditions" && decl.Type.Params == list &&
					key != "NewContext" && key != "Context.WithTraps" {
					t.Errorf("%s accepts Conditions: trap configuration outside the context", key)
				}
			}
		}
		name := key[strings.LastIndex(key, ".")+1:]
		if regexp.MustCompile(`(?i)hash|digest|fingerprint|sum64`).MatchString(name) && key != "Hasher.Hash" {
			t.Errorf("%s is a hash surface other than the seeded Hasher pair", key)
		}
	}
	for _, key := range []string{"Hasher.Hash", "Hasher.Equal", "NewContext", "Context.WithTraps"} {
		if s.funcs[key] == nil {
			t.Errorf("%s missing: the scan lost its anchors", key)
		}
	}
	if slices.Contains(s.imports, "iter") {
		t.Error("library imports iter")
	}
	container := regexp.MustCompile(`(?i)map|set$|table|cache|container|accumulator|builder`)
	envelope := regexp.MustCompile(`^(?i:csv|iso|envelope|swift|iban|record|field)|^FIX`)
	for name, expr := range s.types {
		for _, v := range carrierViolations(expr) {
			t.Errorf("type %s: %s", name, v)
		}
		switch expr.(type) {
		case *ast.MapType, *ast.ArrayType, *ast.ChanType:
			t.Errorf("exported type %s is a container", name)
		}
		if container.MatchString(name) {
			t.Errorf("exported type %s is named as a container or accumulator", name)
		}
		if envelope.MatchString(name) {
			t.Errorf("exported type %s is an envelope type", name)
		}
		if regexp.MustCompile(`(?i)hash|digest`).MatchString(name) && name != "Hasher" {
			t.Errorf("exported type %s is a hash surface", name)
		}
	}
	for src, want := range map[string]int{
		"[]*Decimal": 1, "map[string][]*Decimal": 1, "struct{ D *Decimal }": 1, "struct{ _ [0]func(); d *Decimal }": 0, "struct{ OnChange func(Decimal) }": 1, "func(yield func(Decimal) bool)": 2,
		"iter.Seq[Decimal]": 1, "[]Decimal": 0, "*maphash.Hash": 0, "chan *NullDecimal": 1,
	} {
		expr, err := parser.ParseExpr(src)
		if err != nil {
			t.Fatal(err)
		}
		if got := len(carrierViolations(expr)); got != want {
			t.Fatalf("carrier walk on %s found %d violations, want %d", src, got, want)
		}
	}
	for name, want := range map[string]bool{"CSVField": true, "FIXMessage": true, "ISO20022": true, "Fixed": false, "Decimal": false} {
		if envelope.MatchString(name) != want {
			t.Fatalf("envelope pattern on %s = %v, want %v", name, !want, want)
		}
	}
	for name, want := range map[string]bool{"DecimalMap": true, "DecimalSet": true, "Accumulator": true, "Shape": false, "SumShape": false, "Context": false} {
		if container.MatchString(name) != want {
			t.Fatalf("container pattern on %s = %v, want %v", name, !want, want)
		}
	}
	decimalType := reflect.TypeFor[decimal.Decimal]()
	for field := range decimalType.Fields() {
		if field.Type == reflect.TypeFor[decimal.Conditions]() {
			t.Errorf("Decimal carries a Conditions field %s", field.Name)
		}
	}
}

// TestPackageDocumentationStatesDefaultsAndKeyRecipes checks the reference
// documentation contracts on the package doc and
// its executable examples (whose outputs go test verifies):
//   - documented recipes and behavior: the
//     package doc states that == and map[Decimal]V do not compile and
//     presents the Reduce().Text(0) text-key and Hasher recipes, and both
//     recipes exist as examples with their checked outputs;
//   - explicit monetary rounding: the package doc names TiesToEven as
//     the default and the package example rounds tax to cents by selecting
//     TiesAwayFromZero explicitly.
func TestPackageDocumentationStatesDefaultsAndKeyRecipes(t *testing.T) {
	fset := token.NewFileSet()
	pkgFile, err := parser.ParseFile(fset, "doc.go", nil, parser.ParseComments|parser.SkipObjectResolution)
	if err != nil {
		t.Fatal(err)
	}
	pkgDoc := strings.Join(strings.Fields(pkgFile.Doc.Text()), " ")
	for _, want := range []string{
		"== and map[Decimal]V do not compile",
		"a text key from d.Reduce().Text(0)",
		"[Hasher] with a caller-owned [maphash.Hash]",
		"The zero RoundingMode is [TiesToEven]",
	} {
		if !strings.Contains(pkgDoc, want) {
			t.Errorf("package documentation lacks %q", want)
		}
	}
	examplesFile, err := parser.ParseFile(fset, "example_test.go", nil, parser.ParseComments|parser.SkipObjectResolution)
	if err != nil {
		t.Fatal(err)
	}
	examples := map[string]*doc.Example{}
	for _, ex := range doc.Examples(examplesFile) {
		examples[ex.Name] = ex
	}
	for name, output := range map[string]string{
		"":                "59.97 4.95 64.92\n",
		"Decimal_mapKeys": "1 1\n",
		"Hasher_mapKeys":  "true true\n",
	} {
		ex := examples[name]
		if ex == nil || ex.Output != output {
			t.Fatalf("Example%s missing or its checked output changed: %+v", name, ex)
		}
	}
	var monetary bool
	ast.Inspect(examples[""].Code, func(n ast.Node) bool {
		if call, ok := n.(*ast.CallExpr); ok {
			if sel, ok := call.Fun.(*ast.SelectorExpr); ok && sel.Sel.Name == "Quantize" && len(call.Args) == 2 {
				if mode, ok := call.Args[1].(*ast.SelectorExpr); ok && mode.Sel.Name == "TiesAwayFromZero" {
					monetary = true
				}
			}
		}
		return true
	})
	if !monetary {
		t.Error("the package example does not select TiesAwayFromZero explicitly for its monetary rounding")
	}
	for name, calls := range map[string][]string{"Decimal_mapKeys": {"Reduce", "Text"}, "Hasher_mapKeys": {"Hash", "Equal"}} {
		seen := map[string]bool{}
		ast.Inspect(examples[name].Code, func(n ast.Node) bool {
			if sel, ok := n.(*ast.SelectorExpr); ok {
				seen[sel.Sel.Name] = true
			}
			return true
		})
		for _, call := range calls {
			if !seen[call] {
				t.Errorf("Example%s no longer calls %s", name, call)
			}
		}
	}
}

// TestChainingSelectionIsErrorFreeGrowthIsChecked checks that chaining
// respects resource errors: the selection and no-growth methods
// return a bare Decimal, so a chain of them needs no per-step handling and
// yields the hand-derived value, while growth-capable aggregation returns
// (Decimal, error) and a checked resource refusal stays observable as
// Decimal{} with an ErrInsufficientStorage.
func TestChainingSelectionIsErrorFreeGrowthIsChecked(t *testing.T) {
	var (
		_ func(decimal.Decimal) decimal.Decimal                           = decimal.Decimal.Neg
		_ func(decimal.Decimal) decimal.Decimal                           = decimal.Decimal.Abs
		_ func(decimal.Decimal) decimal.Decimal                           = decimal.Decimal.Reduce
		_ func(decimal.Decimal, decimal.Decimal) decimal.Decimal          = decimal.Decimal.Min
		_ func(decimal.Decimal, decimal.Decimal) decimal.Decimal          = decimal.Decimal.Max
		_ func(decimal.Decimal, decimal.Decimal) (decimal.Decimal, error) = decimal.Decimal.Add
		_ func(...decimal.Decimal) (decimal.Decimal, error)               = decimal.Sum
	)
	got := decimal.MustParse("-12.30").Neg().Abs().Max(decimal.MustParse("4.5")).Min(decimal.MustParse("100")).Reduce()
	if got.String() != "12.3" || got.Exponent() != -1 {
		t.Fatalf("selection chain = %s at exponent %d, want 12.3 at -1", got, got.Exponent())
	}
	nines, one := decimal.MustParse("999"), decimal.One()
	tight := decimal.Budget{MaxDigits: 3}
	for name, run := range map[string]func() (decimal.Decimal, error){
		"SumWithBudget": func() (decimal.Decimal, error) { return decimal.SumWithBudget([]decimal.Decimal{nines, one}, tight) },
		"AddWithContext": func() (decimal.Decimal, error) {
			res, _, resErr := nines.AddWithContext(one, decimal.Context{}.WithBudget(tight))
			return res, resErr
		},
	} {
		d, err := run()
		var opErr *decimal.Error
		if !errors.Is(err, decimal.ErrInsufficientStorage) || !errors.As(err, &opErr) || opErr.Op != name ||
			!d.Equal(decimal.Decimal{}) || d.Exponent() != 0 {
			t.Errorf("%s(999, 1) at 3 digits = %s, %v; want Decimal{} and %s ErrInsufficientStorage", name, d, err, name)
		}
	}
	if sum, err := decimal.SumWithBudget([]decimal.Decimal{nines, one}, decimal.Budget{MaxDigits: 4}); err != nil || sum.String() != "1000" {
		t.Errorf("SumWithBudget(999, 1) at 4 digits = %s, %v; want 1000", sum, err)
	}
}

// TestNonFiniteTextRefusedAtEveryCarrier checks that non-finite text is
// refused with a typed error at every boundary: NaN, Infinity, -Infinity, .nan and .inf (plus sign and case
// variants) through Parse (string and []byte), UnmarshalText (the raw-scalar
// contract a YAML decoder calls), database/sql Scan (string and []byte),
// quoted JSON (UnmarshalJSON and ParseJSONWithBudget) and bare JSON tokens
// return a Conversion-syntax error assertable through errors.Is; no value is
// constructed, and a receiver holding 7.5 keeps it.
func TestNonFiniteTextRefusedAtEveryCarrier(t *testing.T) {
	specials := []string{"NaN", "Infinity", "-Infinity", ".nan", ".inf", "+Inf", "-inf", "nan", "sNaN", "-.inf"}
	for _, text := range specials {
		check := func(carrier string, got decimal.Decimal, err error) {
			t.Helper()
			var parseErr *decimal.Error
			if !errors.Is(err, decimal.ErrConversionSyntax) {
				t.Errorf("%s(%q) error = %v, want ErrConversionSyntax", carrier, text, err)
			}
			if errors.As(err, &parseErr) && parseErr.Condition != decimal.ConversionSyntax {
				t.Errorf("%s(%q) condition = %v, want ConversionSyntax", carrier, text, parseErr.Condition)
			}
			if got.String() != "7.5" && got.String() != "0" {
				t.Errorf("%s(%q) constructed %s", carrier, text, got)
			}
		}
		d, err := decimal.Parse(text)
		check("Parse string", d, err)
		d, err = decimal.Parse([]byte(text))
		check("Parse []byte", d, err)
		d, err = decimal.ParseJSONWithBudget([]byte(strconv.Quote(text)), decimal.Budget{})
		check("ParseJSONWithBudget quoted", d, err)
		d, err = decimal.ParseJSONWithBudget([]byte(text), decimal.Budget{})
		check("ParseJSONWithBudget bare", d, err)
		receivers := map[string]func(*decimal.Decimal) error{
			"UnmarshalText": func(r *decimal.Decimal) error { return r.UnmarshalText([]byte(text)) },
			"UnmarshalJSON": func(r *decimal.Decimal) error { return r.UnmarshalJSON([]byte(strconv.Quote(text))) },
			"Scan string":   func(r *decimal.Decimal) error { return r.Scan(text) },
			"Scan []byte":   func(r *decimal.Decimal) error { return r.Scan([]byte(text)) },
		}
		for carrier, run := range receivers {
			r := decimal.MustParse("7.5")
			err := run(&r)
			check(carrier, r, err)
			if r.String() != "7.5" || r.Exponent() != -1 {
				t.Errorf("%s(%q) changed the receiver to %s", carrier, text, r)
			}
		}
	}
}

// TestLibraryImportsOnlyStandardPackages checks that the library has no
// format-specific or third-party dependency: every import of the library
// package's non-test files is a standard-library path (no dot in its first
// element, so no YAML, CBOR, MessagePack or sibling module), none is an
// in-module subpackage, and the library go.mod carries no require or
// replace directive.
func TestLibraryImportsOnlyStandardPackages(t *testing.T) {
	s := parseExportedSurface(t)
	if len(s.imports) < 30 {
		t.Fatalf("parsed only %d imports", len(s.imports))
	}
	for _, path := range s.imports {
		first, _, _ := strings.Cut(path, "/")
		if strings.Contains(first, ".") || strings.HasPrefix(path, "github.com/0xCarbon/decimal") {
			t.Errorf("library imports non-standard package %q", path)
		}
		if regexp.MustCompile(`(?i)yaml|cbor|msgpack|messagepack`).MatchString(path) {
			t.Errorf("library imports a format-specific package %q", path)
		}
	}
	mod, err := os.ReadFile("go.mod")
	if err != nil {
		t.Fatal(err)
	}
	for line := range strings.SplitSeq(string(mod), "\n") {
		if field := strings.Fields(line); len(field) > 0 && (field[0] == "require" || field[0] == "replace") {
			t.Errorf("library go.mod has a %s directive: %q", field[0], line)
		}
	}
	if !strings.HasPrefix(string(mod), "module github.com/0xCarbon/decimal\n") {
		t.Fatalf("go.mod does not declare the library module: %.60q", mod)
	}
}

// TestModuleHasOnePublicPackage checks that the module has a single public
// package: walking the module (nested modules excluded), the root is package
// decimal with the whole exported surface, no internal/ package exists, and
// every other Go package is either a command (package main, the tools) or
// exports nothing (the benchmarks package holds only tests and doc).
func TestModuleHasOnePublicPackage(t *testing.T) {
	skip := map[string]bool{"testdata": true, "dist": true, "node_modules": true}
	fset := token.NewFileSet()
	packages := map[string]string{}
	err := filepath.WalkDir(".", func(path string, d os.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if d.IsDir() {
			if path != "." && (skip[d.Name()] || strings.HasPrefix(d.Name(), ".")) {
				return filepath.SkipDir
			}
			if _, err := os.Stat(filepath.Join(path, "go.mod")); path != "." && err == nil {
				return filepath.SkipDir // a nested module is not part of this module
			}
			if d.Name() == "internal" {
				t.Errorf("module has an internal package at %s", path)
			}
			return nil
		}
		if !strings.HasSuffix(path, ".go") || strings.HasSuffix(path, "_test.go") {
			return nil
		}
		f, err := parser.ParseFile(fset, path, nil, parser.SkipObjectResolution)
		if err != nil {
			return err
		}
		dir := filepath.Dir(path)
		packages[dir] = f.Name.Name
		if dir == "." || f.Name.Name == "main" {
			return nil
		}
		for _, decl := range f.Decls {
			switch decl := decl.(type) {
			case *ast.FuncDecl:
				if decl.Name.IsExported() {
					t.Errorf("%s exports %s outside the root package", path, decl.Name.Name)
				}
			case *ast.GenDecl:
				for _, spec := range decl.Specs {
					switch spec := spec.(type) {
					case *ast.TypeSpec:
						if spec.Name.IsExported() {
							t.Errorf("%s exports type %s outside the root package", path, spec.Name.Name)
						}
					case *ast.ValueSpec:
						for _, n := range spec.Names {
							if n.IsExported() {
								t.Errorf("%s exports %s outside the root package", path, n.Name)
							}
						}
					}
				}
			}
		}
		return nil
	})
	if err != nil {
		t.Fatal(err)
	}
	if packages["."] != "decimal" || len(packages) < 5 {
		t.Fatalf("module packages %v: want the root package decimal plus the tool and benchmark packages", packages)
	}
	if packages["benchmarks"] == "" || packages[filepath.Join("tools", "benchcmp")] != "main" {
		t.Fatalf("walk missed known packages: %v", packages)
	}
}

// TestAdaptiveEvaluationIsDocumented checks the documentation of the
// adaptive elementary functions: the package doc presents Exp, Ln, Log10
// and PowDecimal as correctly rounded, and no package doc, exported declaration's
// doc comment or README line uses tolerance language (a tolerance, an
// approximate or faithfully rounded result, a result within some ulps).
// The pattern is checked on hand-written lines first.
func TestAdaptiveEvaluationIsDocumented(t *testing.T) {
	tolerance := regexp.MustCompile(`(?i)toleran|\bapproximat|faithful|within (one|two|a few|\d+) ulps?`)
	for line, want := range map[string]bool{
		"results are within 1 ulp": true, "an approximate logarithm": true, "GDA tolerance": true,
		"faithfully rounded": true, "rounds once, correctly in every mode": false, "the half-ulp cell": false,
	} {
		if tolerance.MatchString(line) != want {
			t.Fatalf("tolerance pattern on %q = %v, want %v", line, !want, want)
		}
	}
	fset := token.NewFileSet()
	files, err := filepath.Glob("*.go")
	if err != nil {
		t.Fatal(err)
	}
	var docs []string
	for _, file := range files {
		if strings.HasSuffix(file, "_test.go") {
			continue
		}
		f, err := parser.ParseFile(fset, file, nil, parser.ParseComments|parser.SkipObjectResolution)
		if err != nil {
			t.Fatal(err)
		}
		if f.Doc != nil {
			docs = append(docs, file+" package doc: "+f.Doc.Text())
		}
		for _, decl := range f.Decls {
			switch decl := decl.(type) {
			case *ast.FuncDecl:
				if decl.Name.IsExported() && decl.Doc != nil {
					docs = append(docs, file+" "+decl.Name.Name+": "+decl.Doc.Text())
				}
			case *ast.GenDecl:
				if decl.Doc != nil {
					docs = append(docs, file+" declaration: "+decl.Doc.Text())
				}
				for _, spec := range decl.Specs {
					if ts, ok := spec.(*ast.TypeSpec); ok && ts.Name.IsExported() && ts.Doc != nil {
						docs = append(docs, file+" "+ts.Name.Name+": "+ts.Doc.Text())
					}
				}
			}
		}
	}
	readme, err := os.ReadFile("README.md")
	if err != nil {
		t.Fatal(err)
	}
	docs = append(docs, "README.md: "+string(readme))
	if len(docs) < 150 {
		t.Fatalf("collected only %d doc comments", len(docs))
	}
	for _, doc := range docs {
		if m := tolerance.FindString(doc); m != "" {
			t.Errorf("tolerance language %q in %.80s", m, doc)
		}
	}
	pkgDoc := ""
	for _, doc := range docs {
		if strings.HasPrefix(doc, "doc.go package doc: ") {
			pkgDoc = strings.Join(strings.Fields(doc), " ")
		}
	}
	for _, want := range []string{"[Decimal.Exp], [Decimal.Ln], [Decimal.Log10] and [Decimal.PowDecimal] (a Decimal exponent) are correctly rounded", "correctly in every mode", "[BoundEvaluation]"} {
		if !strings.Contains(pkgDoc, want) {
			t.Errorf("package doc lacks %q", want)
		}
	}
}

// TestScanDriverStandInRefused checks that a foreign driver's
// coefficient/scale value needs an explicit wrapper and is not a text hook.
func TestScanDriverStandInRefused(t *testing.T) {
	var d decimal.Decimal
	var e *decimal.Error
	if err := d.Scan(driverDecimal{Width: 3, Scale: 2, Value: big.NewInt(110)}); !errors.As(err, &e) || !strings.HasPrefix(e.Remedy, "unsupported source ") || strings.Contains(e.Remedy, ": ") {
		t.Fatalf("stand-in refusal: %v", err)
	}
	var wrapper driverDecimalScanner
	if err := wrapper.Scan(driverDecimal{Width: 3, Scale: 2, Value: big.NewInt(110)}); err != nil || wrapper.Decimal.String() != "1.10" {
		t.Fatalf("wrapper: %s %v", wrapper.Decimal, err)
	}
	if err := wrapper.Scan(driverDecimal{}); err == nil || wrapper.Decimal.String() != "1.10" {
		t.Fatal("nil coefficient must refuse atomically")
	}
	if err := wrapper.Scan(nil); err != nil || wrapper.Valid {
		t.Fatal("NULL wrapper", err)
	}
}

// ratOfText is the math/big reading of a decimal's canonical text: the
// independent oracle side of the exactness checks below.
func ratOfText(t *testing.T, d decimal.Decimal) *big.Rat {
	t.Helper()
	r, ok := new(big.Rat).SetString(d.String())
	if !ok {
		t.Fatalf("math/big cannot read %q", d.String())
	}
	return r
}

// terminates reports whether a reduced rational has a finite decimal
// expansion: its denominator has no prime factor other than 2 and 5.
func terminates(r *big.Rat) bool {
	den := new(big.Int).Set(r.Denom())
	for _, p := range []int64{2, 5} {
		q, m, bp := new(big.Int), new(big.Int), big.NewInt(p)
		for {
			q.QuoRem(den, bp, m)
			if m.Sign() != 0 {
				break
			}
			den.Set(q)
		}
	}
	return den.Cmp(big.NewInt(1)) == 0
}

// requireInexactRefusal checks the bare-form refusal: Decimal{} and a
// *Error for op trapping exactly Inexact, visible as ErrInexact.
func requireInexactRefusal(t *testing.T, op string, got decimal.Decimal, err error) {
	t.Helper()
	var ce *decimal.Error
	if !reflect.DeepEqual(got, decimal.Decimal{}) || !errors.Is(err, decimal.ErrInexact) || !errors.As(err, &ce) || ce.Code != 0 || ce.Op != op || ce.Condition != decimal.Inexact {
		t.Errorf("%s = %s, %v; want Decimal{} and a %s Error trapping Inexact", op, got, err, op)
	}
}

// TestBareFormsNeverRoundSilently checks that bare forms never round
// silently, over every bare public form whose
// exact result can fail to be a finite decimal: Div, Sqrt, Pow with a
// negative exponent, FromRat, Exp, Ln, Log10, PowDecimal, the twelve
// trigonometric and hyperbolic functions and Atan2 refuse an inexact result
// with Decimal{} and an Inexact Error, and return the exact value
// when it exists (hand-derived twins, so the refusal is not vacuous); the
// integer egress forms Int64, Uint64 and BigInt refuse a fraction with
// ErrNonIntegral instead of truncating. A seeded sweep checks Div, Pow(-n),
// FromRat and Sqrt against math/big: the bare form succeeds exactly when
// the rational result terminates (or, for Sqrt, is a rational square) and
// then equals it, and refuses otherwise, with both outcomes observed.
// Forms that take a rounding mode, precision, exponent or context carry
// their instruction; FromFloat64 is the named shortest-round-trip regime
// and FromFloat64Exact is always exact, so neither belongs to the set.
func TestBareFormsNeverRoundSilently(t *testing.T) {
	d := decimal.MustParse[string]
	half, two, three := d("0.5"), d("2"), d("3")
	type unary = func(decimal.Decimal) (decimal.Decimal, error)
	for _, tc := range []struct {
		op             string
		f              unary
		inexact, exact decimal.Decimal
		want           string
	}{
		{"Div", func(x decimal.Decimal) (decimal.Decimal, error) { return decimal.One().Div(x) }, three, d("8"), "0.125"},
		{"Sqrt", decimal.Decimal.Sqrt, two, d("2.25"), "1.5"},
		{"Pow", func(x decimal.Decimal) (decimal.Decimal, error) { return x.Pow(-3) }, three, two, "0.125"},
		{"Exp", decimal.Decimal.Exp, half, decimal.Zero(), "1"},
		{"Ln", decimal.Decimal.Ln, two, decimal.One(), "0"},
		{"Log10", decimal.Decimal.Log10, two, d("0.001"), "-3"},
		{"PowDecimal", func(x decimal.Decimal) (decimal.Decimal, error) { return x.PowDecimal(half) }, two, d("4"), "2"},
		{"Sin", decimal.Decimal.Sin, half, decimal.Zero(), "0"},
		{"Cos", decimal.Decimal.Cos, half, decimal.Zero(), "1"},
		{"Tan", decimal.Decimal.Tan, half, decimal.Zero(), "0"},
		{"Asin", decimal.Decimal.Asin, half, decimal.Zero(), "0"},
		{"Acos", decimal.Decimal.Acos, half, decimal.One(), "0"},
		{"Atan", decimal.Decimal.Atan, half, decimal.Zero(), "0"},
		{"Sinh", decimal.Decimal.Sinh, half, decimal.Zero(), "0"},
		{"Cosh", decimal.Decimal.Cosh, half, decimal.Zero(), "1"},
		{"Tanh", decimal.Decimal.Tanh, half, decimal.Zero(), "0"},
		{"Asinh", decimal.Decimal.Asinh, half, decimal.Zero(), "0"},
		{"Acosh", decimal.Decimal.Acosh, d("1.5"), decimal.One(), "0"},
		{"Atanh", decimal.Decimal.Atanh, half, decimal.Zero(), "0"},
		{"Atan2", func(y decimal.Decimal) (decimal.Decimal, error) { return y.Atan2(decimal.One()) }, half, decimal.Zero(), "0"},
	} {
		got, err := tc.f(tc.inexact)
		requireInexactRefusal(t, tc.op, got, err)
		if got, err := tc.f(tc.exact); err != nil || got.String() != tc.want {
			t.Errorf("%s(%s) = %s, %v; want the exact %s", tc.op, tc.exact, got, err, tc.want)
		}
	}
	got, err := decimal.FromRat(big.NewRat(1, 3))
	requireInexactRefusal(t, "FromRat", got, err)
	for _, tc := range []struct {
		op   string
		call func() error
	}{
		{"Int64", func() error { _, err := half.Int64(); return err }},
		{"Uint64", func() error { _, err := half.Uint64(); return err }},
		{"BigInt", func() error { _, err := d("-7.5").BigInt(nil); return err }},
	} {
		var oe *decimal.Error
		if err := tc.call(); !errors.Is(err, decimal.ErrNonIntegral) || !errors.As(err, &oe) || oe.Op != tc.op {
			t.Errorf("%s of a fraction: %v; want a %s ErrNonIntegral refusal, not a truncation", tc.op, err, tc.op)
		}
	}

	rng := rand.New(rand.NewSource(20260929))
	factors := []int64{1, 2, 3, 4, 5, 7, 8, 10, 11, 16, 25, 40, 49, 125, 3 * 5, 9}
	pick := func() *big.Int {
		v := big.NewInt(1 + rng.Int63n(9))
		for range rng.Intn(4) {
			v.Mul(v, big.NewInt(factors[rng.Intn(len(factors))]))
		}
		return v
	}
	cohorts := map[string][2]int{}
	check := func(op string, got decimal.Decimal, err error, want *big.Rat, representable bool) {
		t.Helper()
		c := cohorts[op]
		if representable {
			c[0]++
		} else {
			c[1]++
		}
		cohorts[op] = c
		if !representable {
			requireInexactRefusal(t, op, got, err)
			return
		}
		if err != nil || ratOfText(t, got).Cmp(want) != 0 {
			t.Errorf("%s = %s, %v; want the exact %s", op, got, err, want.RatString())
		}
	}
	for range 400 {
		num, den := pick(), pick()
		if rng.Intn(2) == 0 {
			num.Neg(num)
		}
		q := new(big.Rat).SetFrac(num, den)
		x, y := decimal.MustParse(num.String()), decimal.MustParse(den.String())
		got, err := x.Div(y)
		check("Div", got, err, q, terminates(q))
		got, err = decimal.FromRat(q)
		check("FromRat", got, err, q, terminates(q))

		base := decimal.MustParse(new(big.Rat).SetFrac(num, big.NewInt(int64(1+rng.Intn(3))*10)).FloatString(3))
		n := int32(1 + rng.Intn(4))
		br := ratOfText(t, base)
		want := new(big.Rat).SetInt64(1)
		for range n {
			want.Mul(want, br)
		}
		if want.Sign() != 0 {
			want.Inv(want)
		}
		got, err = base.Pow(-n)
		check("Pow", got, err, want, base.IsZero() || terminates(want))

		sq := new(big.Rat).Abs(q)
		if rng.Intn(2) == 0 {
			sq.Mul(sq, sq)
		}
		if !terminates(sq) {
			continue
		}
		root := decimal.MustParse(sq.FloatString(40)).Reduce()
		if ratOfText(t, root).Cmp(sq) != 0 {
			t.Fatalf("radicand %s lost digits in its 40-place text", sq.RatString())
		}
		rn, rd := new(big.Int).Sqrt(sq.Num()), new(big.Int).Sqrt(sq.Denom())
		isSquare := new(big.Int).Mul(rn, rn).Cmp(sq.Num()) == 0 && new(big.Int).Mul(rd, rd).Cmp(sq.Denom()) == 0
		got, err = root.Sqrt()
		check("Sqrt", got, err, new(big.Rat).SetFrac(rn, rd), isSquare)
	}
	for _, op := range []string{"Div", "FromRat", "Pow", "Sqrt"} {
		if c := cohorts[op]; c[0] < 20 || c[1] < 20 {
			t.Errorf("%s sweep saw %d exact and %d refused results; want both cohorts populated", op, c[0], c[1])
		}
	}
	t.Logf("cohorts (exact, refused): %v", cohorts)
}

// TestMathBigBoundaryConversionsAreExact checks boundary conversions:
// every crossing of the
// math/big boundary is exact or refuses, and shares no storage. Seeded
// big.Int values up to 4000 bits enter through FromBigInt and Scan with
// math/big's own decimal text and leave through BigInt equal to the source;
// terminating big.Rat values enter through FromRat and Scan equal to the
// source and leave through Rat equal to math/big's reading of the decimal
// text, while a non-terminating one refuses with Inexact; finite big.Float
// values cross only through their exact big.Rat (always terminating) and
// equal it, and Scan refuses a *big.Float as an unsupported source
// instead of rounding it. Mutating a source after entry or a result after
// exit never changes the Decimal (no carrier coupling).
func TestMathBigBoundaryConversionsAreExact(t *testing.T) {
	rng := rand.New(rand.NewSource(4))
	for i := range 300 {
		x := new(big.Int).Rand(rng, new(big.Int).Lsh(big.NewInt(1), uint(1+rng.Intn(4000))))
		if i%2 == 1 {
			x.Neg(x)
		}
		want := x.String()
		got, err := decimal.FromBigInt(x)
		if err != nil || got.String() != want || got.Exponent() != 0 {
			t.Fatalf("FromBigInt(%s) = %s, %v", want, got, err)
		}
		var scanned decimal.Decimal
		if err := scanned.Scan(x); err != nil || !scanned.Equal(got) {
			t.Fatalf("Scan(*big.Int %s) = %s, %v", want, scanned, err)
		}
		x.Add(x, big.NewInt(1))
		back, err := got.BigInt(nil)
		if err != nil || back.String() != want || got.String() != want {
			t.Fatalf("BigInt round trip of %s = %v, %v; decimal now %s", want, back, err, got)
		}
		back.SetInt64(7)
		if got.String() != want {
			t.Fatalf("mutating the BigInt result changed the Decimal to %s", got)
		}
	}
	if b, err := decimal.MustParse("-12E+3").BigInt(nil); err != nil || b.Cmp(big.NewInt(-12000)) != 0 {
		t.Errorf("BigInt(-12E+3) = %v, %v; want -12000", b, err)
	}

	for i := range 300 {
		num := new(big.Int).Rand(rng, new(big.Int).Lsh(big.NewInt(1), uint(1+rng.Intn(300))))
		if i%3 == 0 {
			num.Neg(num)
		}
		den := new(big.Int).Exp(big.NewInt(2), big.NewInt(int64(rng.Intn(80))), nil)
		den.Mul(den, new(big.Int).Exp(big.NewInt(5), big.NewInt(int64(rng.Intn(80))), nil))
		r := new(big.Rat).SetFrac(num, den)
		src := new(big.Rat).Set(r)
		got, err := decimal.FromRat(src)
		if err != nil || ratOfText(t, got).Cmp(r) != 0 {
			t.Fatalf("FromRat(%s) = %s, %v", r.RatString(), got, err)
		}
		var scanned decimal.Decimal
		if err := scanned.Scan(src); err != nil || !scanned.Equal(got) {
			t.Fatalf("Scan(*big.Rat %s) = %s, %v", r.RatString(), scanned, err)
		}
		text := got.String()
		src.SetInt64(3)
		out, err := got.Rat(nil)
		if err != nil || out.Cmp(r) != 0 || got.String() != text {
			t.Fatalf("Rat of %s = %v, %v; decimal now %s", text, out, err, got)
		}
		out.SetInt64(9)
		if got.String() != text {
			t.Fatalf("mutating the Rat result changed the Decimal to %s", got)
		}
	}
	var scanned decimal.Decimal
	requireInexactRefusal(t, "Scan", scanned, scanned.Scan(big.NewRat(2, 7)))

	for range 300 {
		f := new(big.Float).SetPrec(uint(1 + rng.Intn(500)))
		f.SetMantExp(big.NewFloat(rng.NormFloat64()), rng.Intn(400)-200)
		r, acc := f.Rat(nil)
		if acc != big.Exact {
			t.Fatalf("math/big.Float.Rat of %s was not exact", f.Text('g', -1))
		}
		got, err := decimal.FromRat(r)
		if err != nil || ratOfText(t, got).Cmp(r) != 0 {
			t.Fatalf("FromRat(Float %s) = %s, %v", f.Text('g', -1), got, err)
		}
		var target decimal.Decimal
		var unsupported *decimal.Error
		if err := target.Scan(f); !errors.As(err, &unsupported) || !strings.HasPrefix(unsupported.Remedy, "unsupported source *big.Float") || !target.IsZero() {
			t.Fatalf("Scan(*big.Float %s) = %s, %v; want an unsupported-source refusal", f.Text('g', -1), target, err)
		}
	}
}

// TestValueTypeHasNoMathBigCoupling checks that the value type has no
// math/big coupling: the stored representation reachable from Decimal
// (reflect walk through its fields, pointers, slices and arrays, including
// slowCoefficient's limbs) holds no type from math/big, and among the
// library's non-test files only the boundary files import math/big:
// integer.go (big.Int conversion), rational.go (big.Rat conversion),
// sql.go (Scan's big.Int, big.Rat and big.Float sources) and cost.go
// (their estimates). The walk counts the uint32 limb slice so a changed
// layout cannot pass vacuously.
func TestValueTypeHasNoMathBigCoupling(t *testing.T) {
	seen := map[reflect.Type]bool{}
	var walk func(reflect.Type, string)
	walk = func(ty reflect.Type, path string) {
		if seen[ty] {
			return
		}
		seen[ty] = true
		if ty.PkgPath() == "math/big" {
			t.Errorf("Decimal stores math/big type %s at %s", ty, path)
		}
		switch ty.Kind() {
		case reflect.Pointer, reflect.Slice, reflect.Array, reflect.Chan:
			walk(ty.Elem(), path+"[]")
		case reflect.Map:
			walk(ty.Key(), path+"[key]")
			walk(ty.Elem(), path+"[value]")
		case reflect.Struct:
			for field := range ty.Fields() {
				walk(field.Type, path+"."+field.Name)
			}
		}
	}
	walk(reflect.TypeFor[decimal.Decimal](), "Decimal")
	if !seen[reflect.TypeFor[[]uint32]()] || !seen[reflect.TypeFor[uint64]()] {
		t.Fatalf("the walk did not reach the inline words and the limb slice: %v", seen)
	}

	files, err := filepath.Glob("*.go")
	if err != nil {
		t.Fatal(err)
	}
	var importers []string
	fset := token.NewFileSet()
	for _, file := range files {
		if strings.HasSuffix(file, "_test.go") {
			continue
		}
		f, err := parser.ParseFile(fset, file, nil, parser.ImportsOnly)
		if err != nil {
			t.Fatal(err)
		}
		for _, imp := range f.Imports {
			if imp.Path.Value == `"math/big"` {
				importers = append(importers, file)
			}
		}
	}
	if want := []string{"cost.go", "integer.go", "rational.go", "sql.go"}; !slices.Equal(importers, want) {
		t.Errorf("math/big importers = %v; want only the boundary files %v", importers, want)
	}
}

// TestMonetaryRoundingIsDocumented checks that the documentation makes
// monetary rounding explicit: the API reference (package doc and the
// RoundingMode doc) and the cookbook state that the zero RoundingMode is
// TiesToEven and point monetary rounding at TiesAwayFromZero; the
// ExampleRoundingMode_monetary example selects TiesAwayFromZero, has a
// checked Output (so go test compiles and executes it), and the cookbook's
// code block is its body verbatim, so the cookbook cannot drift from code
// that runs.
func TestMonetaryRoundingIsDocumented(t *testing.T) {
	fset := token.NewFileSet()
	src, err := os.ReadFile("example_test.go")
	if err != nil {
		t.Fatal(err)
	}
	f, err := parser.ParseFile(fset, "example_test.go", src, parser.ParseComments)
	if err != nil {
		t.Fatal(err)
	}
	var example *doc.Example
	for _, ex := range doc.Examples(f) {
		if ex.Name == "RoundingMode_monetary" {
			example = ex
		}
	}
	if example == nil || example.EmptyOutput || !strings.Contains(example.Output, "2.15 Inexact|Rounded|Increased") {
		t.Fatalf("ExampleRoundingMode_monetary missing or without a checked Output: %+v", example)
	}
	var body string
	for _, decl := range f.Decls {
		if fn, ok := decl.(*ast.FuncDecl); ok && fn.Name.Name == "ExampleRoundingMode_monetary" {
			inner := string(src[fset.Position(fn.Body.Lbrace).Offset+2 : fset.Position(fn.Body.Rbrace).Offset-1])
			var lines []string
			for line := range strings.SplitSeq(inner, "\n") {
				lines = append(lines, strings.TrimPrefix(line, "\t"))
			}
			body = strings.Join(lines, "\n")
		}
	}
	if !strings.Contains(body, "decimal.TiesAwayFromZero") || !strings.Contains(body, "var unset decimal.RoundingMode") {
		t.Fatalf("example does not select TiesAwayFromZero against the default mode:\n%s", body)
	}
	cookbook, err := os.ReadFile("docs/cookbook.md")
	if err != nil {
		t.Fatal(err)
	}
	_, section, ok := strings.Cut(string(cookbook), "\n## Rounding money\n")
	if !ok {
		t.Fatal("cookbook has no Rounding money section")
	}
	_, block, ok := strings.Cut(section, "```go\n")
	block, _, closed := strings.Cut(block, "\n```\n")
	if !ok || !closed || block != body {
		t.Fatalf("cookbook code block differs from ExampleRoundingMode_monetary:\n%s\n--- example ---\n%s", block, body)
	}
	flat := func(s string) string { return strings.Join(strings.Fields(s), " ") }
	for _, want := range []string{"the zero `RoundingMode` is `TiesToEven`", "`TiesAwayFromZero`", "ExampleRoundingMode_monetary"} {
		if !strings.Contains(flat(section), want) {
			t.Errorf("cookbook lacks %q", want)
		}
	}
	docs := map[string]string{}
	for _, file := range []string{"doc.go", "context.go"} {
		pf, err := parser.ParseFile(token.NewFileSet(), file, nil, parser.ParseComments|parser.SkipObjectResolution)
		if err != nil {
			t.Fatal(err)
		}
		if pf.Doc != nil {
			docs["package"] = flat(pf.Doc.Text())
		}
		for _, decl := range pf.Decls {
			if gd, ok := decl.(*ast.GenDecl); ok && gd.Doc != nil && gd.Tok == token.TYPE && gd.Specs[0].(*ast.TypeSpec).Name.Name == "RoundingMode" {
				docs["RoundingMode"] = flat(gd.Doc.Text())
			}
		}
	}
	for where, wants := range map[string][]string{
		"package":      {"The zero RoundingMode is [TiesToEven]", "Monetary code should name its mode, usually [TiesAwayFromZero]", "docs/cookbook.md"},
		"RoundingMode": {"The zero value is TiesToEven", "Monetary rounding should name its mode explicitly, usually TiesAwayFromZero"},
	} {
		for _, want := range wants {
			if !strings.Contains(docs[where], want) {
				t.Errorf("%s documentation lacks %q", where, want)
			}
		}
	}
}

// exampleBodies returns the body of every example in example_test.go whose
// output go test checks, as documentation shows it: the text between the
// braces with one leading tab removed from each line.
func exampleBodies(t *testing.T) map[string]string {
	t.Helper()
	src, err := os.ReadFile("example_test.go")
	if err != nil {
		t.Fatal(err)
	}
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, "example_test.go", src, parser.ParseComments)
	if err != nil {
		t.Fatal(err)
	}
	checked := map[string]bool{}
	for _, ex := range doc.Examples(f) {
		checked["Example"+strings.TrimPrefix("_"+ex.Name, "_")] = !ex.EmptyOutput && ex.Output != ""
	}
	bodies := map[string]string{}
	for _, decl := range f.Decls {
		fn, ok := decl.(*ast.FuncDecl)
		if !ok || !checked[fn.Name.Name] {
			continue
		}
		inner := string(src[fset.Position(fn.Body.Lbrace).Offset+2 : fset.Position(fn.Body.Rbrace).Offset-1])
		var lines []string
		for line := range strings.SplitSeq(inner, "\n") {
			lines = append(lines, strings.TrimPrefix(line, "\t"))
		}
		bodies[fn.Name.Name] = strings.Join(lines, "\n")
	}
	return bodies
}

// docExampleMarker precedes every Go block of the documentation set and
// names the example whose body the block is.
var docExampleMarker = regexp.MustCompile(`^<!-- example: (Example\w*) -->$`)

// goFence matches any fence opening a Go block, in any spelling Markdown
// renderers accept; only the exact "```go" form can be pinned.
var goFence = regexp.MustCompile("(?i)^\\s*(```|~~~)\\s*(go|golang)\\s*$")

// checkDocBlocks returns, per document, the examples its Go blocks pin, and
// every block that is not pinned: a Go block without a marker on the line
// before it, a marker without a Go block after it, a marker naming no
// example with checked output, an unterminated block, or a block that
// differs from its example's body.
func checkDocBlocks(docs, bodies map[string]string) (map[string][]string, []string) {
	pinned := map[string][]string{}
	var problems []string
	for _, name := range slices.Sorted(maps.Keys(docs)) {
		lines := strings.Split(docs[name], "\n")
		for i := 0; i < len(lines); i++ {
			m := docExampleMarker.FindStringSubmatch(lines[i])
			if m == nil {
				if goFence.MatchString(lines[i]) {
					problems = append(problems, fmt.Sprintf("%s:%d: Go block without an example marker", name, i+1))
				}
				continue
			}
			if i+1 >= len(lines) || lines[i+1] != "```go" {
				problems = append(problems, fmt.Sprintf("%s:%d: marker for %s not followed by a Go block", name, i+1, m[1]))
				continue
			}
			end := slices.Index(lines[i+2:], "```")
			if end < 0 {
				problems = append(problems, fmt.Sprintf("%s:%d: unterminated Go block", name, i+2))
				break
			}
			block := strings.Join(lines[i+2:i+2+end], "\n")
			switch body, ok := bodies[m[1]]; {
			case !ok:
				problems = append(problems, fmt.Sprintf("%s:%d: %s is not an example with checked output", name, i+1, m[1]))
			case block != body:
				problems = append(problems, fmt.Sprintf("%s:%d: block differs from %s:\n%s\n--- example ---\n%s", name, i+1, m[1], block, body))
			default:
				pinned[name] = append(pinned[name], m[1])
			}
			i += 2 + end
		}
	}
	return pinned, problems
}

// TestDocumentationCodeBlocksAreExamples checks the documentation set:
// every Go block in
// docs/ is the verbatim body of an example in example_test.go whose output
// go test checks, named by the marker line before it, so no page shows code
// that does not compile or prints something else. The pages pin the SQL
// DECIMAL(p,s) recipe, the cross-domain numeric key recipe, the map-key
// recipes and the minor-units round trip; doc.go and README.md link every
// page, including the correct-rounding reference and the design rationale.
// Controls: a changed character, a
// missing marker, an unknown example and a marker without a block are each
// caught, as is a Go block fenced in another spelling (~~~, golang, any
// case), and an empty documentation set pins nothing, which the required
// list rejects.
func TestDocumentationCodeBlocksAreExamples(t *testing.T) {
	docs := map[string]string{}
	err := filepath.WalkDir("docs", func(path string, d fs.DirEntry, err error) error {
		if err != nil || d.IsDir() || !strings.HasSuffix(path, ".md") {
			return err
		}
		text, err := os.ReadFile(path)
		docs[filepath.ToSlash(path)] = string(text)
		return err
	})
	if err != nil {
		t.Fatal(err)
	}
	bodies := exampleBodies(t)
	pinned, problems := checkDocBlocks(docs, bodies)
	for _, p := range problems {
		t.Error(p)
	}
	required := map[string][]string{
		"docs/api-guide.md": {"Example", "ExampleNew_minorUnits"},
		"docs/cookbook.md":  {"ExampleRoundingMode_monetary", "ExampleDecimal_mapKeys", "ExampleHasher_mapKeys", "ExampleDecimal_numericKey"},
		"docs/interop.md":   {"ExampleNullDecimal", "ExampleContext_sqlDecimal", "ExampleDecimal_MarshalJSON", "ExampleNewTwosComplement", "ExampleDecimal_Float64Rounded"},
	}
	for page, names := range required {
		for _, name := range names {
			if !slices.Contains(pinned[page], name) {
				t.Errorf("%s does not pin %s (pinned: %v)", page, name, pinned[page])
			}
		}
	}
	for _, file := range []string{"doc.go", "README.md"} {
		text, err := os.ReadFile(file)
		if err != nil {
			t.Fatal(err)
		}
		for _, page := range []string{"docs/reference/semantics.md", "docs/api-guide.md", "docs/cookbook.md", "docs/interop.md", "docs/reference/correct-rounding.md", "docs/rationale.md"} {
			if !strings.Contains(string(text), page) {
				t.Errorf("%s does not link %s", file, page)
			}
		}
	}

	// Controls: each defect class is caught on a copy of a real page.
	page := docs["docs/cookbook.md"]
	for name, mutate := range map[string]func(string) string{
		"changed character": func(s string) string { return strings.Replace(s, "entries[key] = i", "entries[key] = i+1", 1) },
		"missing marker":    func(s string) string { return strings.Replace(s, "<!-- example: ExampleHasher_mapKeys -->\n", "", 1) },
		"unknown example": func(s string) string {
			return strings.Replace(s, "example: ExampleHasher_mapKeys", "example: ExampleHasher_absent", 1)
		},
		"orphan marker": func(s string) string { return s + "\n<!-- example: Example -->\ntext\n" },
		"tilde fence":   func(s string) string { return s + "\n~~~Golang\nfmt.Println()\n~~~\n" },
	} {
		mutated := mutate(page)
		if mutated == page {
			t.Fatalf("control %s did not change the page", name)
		}
		if _, got := checkDocBlocks(map[string]string{"docs/cookbook.md": mutated}, bodies); len(got) == 0 {
			t.Errorf("control %s: defect not caught", name)
		}
	}
	if got, _ := checkDocBlocks(map[string]string{}, bodies); len(got) != 0 {
		t.Errorf("empty documentation set pinned %v", got)
	}
}

// correctlyRoundedClaim matches documentation that claims correct rounding.
var correctlyRoundedClaim = regexp.MustCompile(`(?i)\bcorrectly\b`)

// toleranceLanguage matches accuracy stated as a tolerance, which no
// correct-rounding claim or its register may use.
var toleranceLanguage = regexp.MustCompile(`(?i)toleran|\bapproximat|faithful|within (one|two|a few|\d+) ulps?`)

// claimDocument is one claiming-document candidate: the godoc of the
// package (package comments and exported declaration comments) or one
// Markdown file, split into paragraphs. implied maps a paragraph index to
// the operation whose own doc comment it belongs to.
type claimDocument struct {
	name       string
	paragraphs []string
	implied    map[int]string
}

// markdownParagraphs splits Markdown into blank-line-separated blocks, and
// list items and table rows into their own paragraphs.
func markdownParagraphs(text string) []string {
	var out []string
	item := regexp.MustCompile(`^\s*([-*+]|\d+\.|\|)\s`)
	for block := range strings.SplitSeq(text, "\n\n") {
		var cur []string
		for line := range strings.SplitSeq(block, "\n") {
			if item.MatchString(line) && len(cur) > 0 {
				out = append(out, strings.Join(cur, "\n"))
				cur = nil
			}
			cur = append(cur, line)
		}
		if len(cur) > 0 {
			out = append(out, strings.Join(cur, "\n"))
		}
	}
	return out
}

// claimDocuments gathers the claiming-document candidates of fsys: the
// package godoc of its non-test Go files, README.md, ARCHITECTURE.md and
// docs/**/*.md. It also returns the exported methods of Decimal.
func claimDocuments(fsys fs.FS) ([]claimDocument, map[string]bool, error) {
	godoc := claimDocument{name: "package godoc", implied: map[int]string{}}
	methods := map[string]bool{}
	add := func(text, op string) {
		for paragraph := range strings.SplitSeq(text, "\n\n") {
			if op != "" {
				godoc.implied[len(godoc.paragraphs)] = op
			}
			godoc.paragraphs = append(godoc.paragraphs, paragraph)
		}
	}
	files, err := fs.Glob(fsys, "*.go")
	if err != nil {
		return nil, nil, err
	}
	fset := token.NewFileSet()
	for _, file := range files {
		if strings.HasSuffix(file, "_test.go") {
			continue
		}
		src, err := fs.ReadFile(fsys, file)
		if err != nil {
			return nil, nil, err
		}
		f, err := parser.ParseFile(fset, file, src, parser.ParseComments|parser.SkipObjectResolution)
		if err != nil {
			return nil, nil, err
		}
		if f.Doc != nil {
			add(f.Doc.Text(), "")
		}
		for _, decl := range f.Decls {
			switch d := decl.(type) {
			case *ast.FuncDecl:
				if !d.Name.IsExported() {
					continue
				}
				op := ""
				if d.Recv != nil && len(d.Recv.List) == 1 {
					if id, ok := d.Recv.List[0].Type.(*ast.Ident); ok && id.Name == "Decimal" {
						methods[d.Name.Name], op = true, d.Name.Name
					}
				}
				if d.Doc != nil {
					add(d.Doc.Text(), op)
				}
			case *ast.GenDecl:
				exported := false
				for _, spec := range d.Specs {
					switch s := spec.(type) {
					case *ast.TypeSpec:
						exported = exported || s.Name.IsExported()
						if s.Doc != nil && s.Name.IsExported() {
							add(s.Doc.Text(), "")
						}
					case *ast.ValueSpec:
						for _, n := range s.Names {
							exported = exported || n.IsExported()
						}
						if s.Doc != nil && slices.ContainsFunc(s.Names, (*ast.Ident).IsExported) {
							add(s.Doc.Text(), "")
						}
					}
				}
				if exported && d.Doc != nil {
					add(d.Doc.Text(), "")
				}
			}
		}
	}
	docs := []claimDocument{godoc}
	markdown := []string{"README.md", "ARCHITECTURE.md"}
	err = fs.WalkDir(fsys, "docs", func(name string, d fs.DirEntry, err error) error {
		if errors.Is(err, fs.ErrNotExist) && name == "docs" {
			return fs.SkipDir
		}
		if err == nil && !d.IsDir() && strings.HasSuffix(name, ".md") {
			markdown = append(markdown, name)
		}
		return err
	})
	if err != nil {
		return nil, nil, err
	}
	for _, file := range markdown {
		data, err := fs.ReadFile(fsys, file)
		if errors.Is(err, fs.ErrNotExist) {
			continue
		}
		if err != nil {
			return nil, nil, err
		}
		docs = append(docs, claimDocument{name: file, paragraphs: markdownParagraphs(string(data))})
	}
	return docs, methods, nil
}

// markdownLinkTarget matches the target of an inline Markdown link.
var markdownLinkTarget = regexp.MustCompile(`\]\(([^)\s#]*)(?:#[^)\s]*)?\)`)

// citesReference reports whether a claiming paragraph of the named document
// cites the register: by its repository path in text (Go doc comments) or
// by a Markdown link whose target, resolved against the document's
// directory, is the register.
func citesReference(name, paragraph, register string) bool {
	if strings.Contains(paragraph, register) {
		return true
	}
	for _, m := range markdownLinkTarget.FindAllStringSubmatch(paragraph, -1) {
		if m[1] != "" && !strings.Contains(m[1], "://") && path.Join(path.Dir(name), m[1]) == register {
			return true
		}
	}
	return false
}

// checkRoundingClaims returns the operations claimed correctly rounded
// (with where each claim is made) and the problems of the claiming
// documents: every claiming paragraph outside the register must cite the
// register, and no claiming document, nor the register, may use tolerance
// language anywhere.
func checkRoundingClaims(docs []claimDocument, methods map[string]bool, register string) (map[string]string, []string) {
	claimed := map[string]string{}
	var problems []string
	decimalLink := regexp.MustCompile(`\[?\x60?Decimal\.([A-Za-z0-9]+)\x60?\]?`)
	backticked := regexp.MustCompile("`([A-Z][A-Za-z0-9]*)`")
	flat := func(s string) string { return strings.Join(strings.Fields(s), " ") }
	for _, doc := range docs {
		isReference := doc.name == register
		claims := isReference
		for i, paragraph := range doc.paragraphs {
			if !correctlyRoundedClaim.MatchString(paragraph) {
				continue
			}
			claims = true
			if isReference {
				continue
			}
			if !citesReference(doc.name, flat(paragraph), register) {
				problems = append(problems, fmt.Sprintf("%s: claiming paragraph does not cite %s: %.80q", doc.name, register, flat(paragraph)))
			}
			if op := doc.implied[i]; op != "" {
				claimed[op] = doc.name + " " + op + " doc"
			}
			for _, m := range decimalLink.FindAllStringSubmatch(paragraph, -1) {
				claimed[m[1]] = doc.name
			}
			for _, m := range backticked.FindAllStringSubmatch(paragraph, -1) {
				if methods[m[1]] {
					claimed[m[1]] = doc.name
				}
			}
		}
		if !claims {
			continue
		}
		for _, paragraph := range doc.paragraphs {
			if m := toleranceLanguage.FindString(paragraph); m != "" {
				problems = append(problems, fmt.Sprintf("%s: claiming document uses tolerance language %q: %.80q", doc.name, m, flat(paragraph)))
			}
		}
	}
	return claimed, problems
}

// TestCorrectRoundingClaimsCiteReference checks that every claim of correct
// rounding cites the correct-rounding register. Claims are extracted per paragraph
// from the package godoc (package and exported declaration comments),
// README.md, ARCHITECTURE.md and docs/**/*.md. Every claiming paragraph
// cites docs/reference/correct-rounding.md itself, and no claiming document
// or the register uses tolerance language anywhere. Every operation so
// claimed has a register row naming its reduction or enclosure argument, a
// checker test that exists in the package, and validating named cases that
// are tests of the root package; the register names only
// real methods. Mutated fixtures (an uncited second paragraph beside a
// citing one, uncited claims in README, ARCHITECTURE and docs/, a method
// doc claim, tolerance language away from the claim) must each be caught,
// and the extraction is guarded against vacuity: the current documentation
// claims correct rounding for at least the 21 adaptive, root and power
// operations.
func TestCorrectRoundingClaimsCiteReference(t *testing.T) {
	const register = "docs/reference/correct-rounding.md"
	cite := " (" + register + ")"
	fixture := fstest.MapFS{
		"doc.go":    {Data: []byte("// Package p.\n//\n// [Decimal.Sqrt] rounds correctly" + cite + ".\npackage p\n")},
		"exp.go":    {Data: []byte("package p\n\ntype Decimal struct{}\n\n// Exp returns e^x.\nfunc (Decimal) Exp() {}\n\n// Sqrt returns a root.\nfunc (Decimal) Sqrt() {}\n")},
		"README.md": {Data: []byte("# P\n\n- **Roots.** `Sqrt` is correctly rounded;\n  see " + register + ".\n- Other.\n")},
		register:    {Data: []byte("# Register\n\nAn operation documented as correctly rounded.\n")},
	}
	fixtureDocs := func(changes map[string]string) ([]claimDocument, map[string]bool) {
		t.Helper()
		fsys := fstest.MapFS{}
		maps.Copy(fsys, fixture)
		for name, text := range changes {
			fsys[name] = &fstest.MapFile{Data: []byte(text)}
		}
		docs, methods, err := claimDocuments(fsys)
		if err != nil {
			t.Fatal(err)
		}
		return docs, methods
	}
	docs, methods := fixtureDocs(nil)
	if claimed, problems := checkRoundingClaims(docs, methods, register); len(problems) > 0 || claimed["Sqrt"] == "" {
		t.Fatalf("clean fixture: claimed %v, problems %q", claimed, problems)
	}
	for name, m := range map[string]struct {
		changes map[string]string
		want    string
	}{
		"uncited second package paragraph": {map[string]string{"doc.go": "// Package p.\n//\n// [Decimal.Sqrt] rounds correctly" + cite + ".\n//\n// [Decimal.Exp] also rounds correctly.\npackage p\n"},
			"package godoc: claiming paragraph does not cite"},
		"uncited method doc claim": {map[string]string{"exp.go": strings.Replace(string(fixture["exp.go"].Data), "e^x.", "e^x, correctly rounded.", 1)},
			"package godoc: claiming paragraph does not cite"},
		"uncited README claim": {map[string]string{"README.md": "# P\n\n- `Exp` is correctly rounded.\n- `Sqrt` is correctly rounded" + cite + ".\n"},
			"README.md: claiming paragraph does not cite"},
		"uncited ARCHITECTURE claim": {map[string]string{"ARCHITECTURE.md": "# A\n\nExp rounds correctly.\n"},
			"ARCHITECTURE.md: claiming paragraph does not cite"},
		"uncited docs claim": {map[string]string{"docs/guide.md": "# Guide\n\n| `Exp` | correctly rounded |\n"},
			"docs/guide.md: claiming paragraph does not cite"},
		"tolerance away from the claim": {map[string]string{"docs/guide.md": "# Guide\n\n`Exp` is correctly rounded" + cite + ".\n\nLn is accurate within one ulp.\n"},
			"docs/guide.md: claiming document uses tolerance language"},
		"tolerance in the register": {map[string]string{register: "# Register\n\nResults are faithful.\n"},
			register + ": claiming document uses tolerance language"},
	} {
		docs, methods := fixtureDocs(m.changes)
		_, problems := checkRoundingClaims(docs, methods, register)
		if !slices.ContainsFunc(problems, func(p string) bool { return strings.Contains(p, m.want) }) {
			t.Errorf("%s: mutated fixture accepted (problems %q, want %q)", name, problems, m.want)
		}
	}
	docs, methods = fixtureDocs(map[string]string{"docs/guide.md": "# Guide\n\n`Exp` is correctly rounded.\n"})
	if claimed, _ := checkRoundingClaims(docs, methods, register); claimed["Exp"] != "docs/guide.md" {
		t.Errorf("docs/ claim not extracted: %v", claimed)
	}
	// A relative link resolves against its document's directory: from
	// docs/reference/ it cites the register, from docs/ it does not.
	docs, methods = fixtureDocs(map[string]string{"docs/reference/guide.md": "# Guide\n\n`Exp` is correctly rounded ([register](correct-rounding.md#exp)).\n"})
	if _, problems := checkRoundingClaims(docs, methods, register); len(problems) != 0 {
		t.Errorf("relative register link from docs/reference rejected: %q", problems)
	}
	docs, methods = fixtureDocs(map[string]string{"docs/guide.md": "# Guide\n\n`Exp` is correctly rounded ([register](correct-rounding.md)).\n"})
	if _, problems := checkRoundingClaims(docs, methods, register); !slices.ContainsFunc(problems, func(p string) bool { return strings.Contains(p, "docs/guide.md: claiming paragraph does not cite") }) {
		t.Errorf("misresolved relative link accepted: %q", problems)
	}
	docs, methods = fixtureDocs(map[string]string{"docs/a/b/deep.md": "# Deep\n\n`Exp` is correctly rounded.\n"})
	if claimed, problems := checkRoundingClaims(docs, methods, register); claimed["Exp"] != "docs/a/b/deep.md" || len(problems) == 0 {
		t.Errorf("nested docs/ claim not extracted: %v, %q", claimed, problems)
	}

	docs, methods, err := claimDocuments(os.DirFS("."))
	if err != nil {
		t.Fatal(err)
	}
	claimed, problems := checkRoundingClaims(docs, methods, register)
	for _, p := range problems {
		t.Error(p)
	}
	fset := token.NewFileSet()
	files, err := filepath.Glob("*_test.go")
	if err != nil {
		t.Fatal(err)
	}
	tests := map[string]bool{}
	for _, file := range files {
		f, err := parser.ParseFile(fset, file, nil, parser.SkipObjectResolution)
		if err != nil {
			t.Fatal(err)
		}
		for _, decl := range f.Decls {
			if fn, ok := decl.(*ast.FuncDecl); ok && strings.HasPrefix(fn.Name.Name, "Test") {
				tests[fn.Name.Name] = true
			}
		}
	}
	if len(claimed) < 21 || len(methods) < 90 || len(tests) < 300 {
		t.Fatalf("extracted %d claims, %d methods, %d tests: the scan is vacuous", len(claimed), len(methods), len(tests))
	}

	table, err := os.ReadFile(register)
	if err != nil {
		t.Fatal(err)
	}
	covered := map[string]bool{}
	testName := regexp.MustCompile("`(Test[A-Za-z0-9]+)`")
	operation := regexp.MustCompile("`Decimal\\.([A-Za-z0-9]+)`")
	rows := 0
	for line := range strings.SplitSeq(string(table), "\n") {
		cells := strings.Split(line, " | ")
		if !strings.HasPrefix(line, "| `Decimal.") || len(cells) != 4 {
			continue
		}
		rows++
		ops, argument, checker, cases := cells[0], cells[1], cells[2], cells[3]
		for _, m := range operation.FindAllStringSubmatch(ops, -1) {
			if !methods[m[1]] {
				t.Errorf("register row names Decimal.%s, which is not an exported method", m[1])
			}
			covered[m[1]] = true
		}
		if !strings.HasPrefix(argument, "Reduction") && !strings.HasPrefix(argument, "Enclosure") {
			t.Errorf("register row %.60q states no reduction or enclosure argument", ops)
		}
		checkers, named := testName.FindAllStringSubmatch(checker, -1), testName.FindAllStringSubmatch(cases, -1)
		if len(checkers) == 0 || len(named) == 0 {
			t.Errorf("register row %.60q lacks a checker or named cases", ops)
		}
		for _, m := range checkers {
			if !tests[m[1]] {
				t.Errorf("checker %s is not a test of the package", m[1])
			}
		}
		for _, m := range named {
			if !tests[m[1]] {
				t.Errorf("named case %s is not a test of the package", m[1])
			}
		}
	}
	if rows == 0 {
		t.Fatal("register has no claim rows")
	}
	for op, where := range claimed {
		if !covered[op] {
			t.Errorf("%s claims Decimal.%s is correctly rounded, but the register has no row for it", where, op)
		}
	}
}
