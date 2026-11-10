// SPDX-License-Identifier: Apache-2.0

// Public parser, round-trip, arithmetic and conversion fuzz targets. Every
// target must neither panic nor do unbounded work.
//
// FuzzParse and FuzzRoundtrip exercise Decimal's public entry points under
// per-call budgets; FuzzArithmetic checks exact and context arithmetic
// against the rational oracle. Crasher promotion is mandatory: see
// testdata/fuzz/README.md; TestFuzzCorpusPromotion enforces it.

package decimal_test

import (
	"bytes"
	"encoding/binary"
	"encoding/json"
	"errors"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"math"
	"math/big"
	"os"
	"path/filepath"
	"regexp"
	"slices"
	"strconv"
	"strings"
	"testing"

	decimal "github.com/0xCarbon/decimal"
)

// requireFuzzRepresentation checks the representation invariant on every
// produced Decimal,
// including refused-result zeros and receivers after failed mutations. Numeric,
// cohort, condition and resource oracles remain independent checks below it.
func requireFuzzRepresentation(t *testing.T, values ...decimal.Decimal) {
	t.Helper()
	for _, value := range values {
		if !decimal.ValidRepresentationForTest(value) {
			t.Fatalf("invalid Decimal representation: %#v", value)
		}
	}
}

// maxShapeExponent bounds the exponents the oracle checks touch, keeping
// every property bounded-work: no panic and bounded work.
const maxShapeExponent = 10000

// scanDecimalShape recognizes an independent strict subset of the public
// decimal grammar: optional sign; digits with at most one dot and at least
// one digit on each side of a present dot; optional bounded exponent. Its
// narrower acceptance keeps rational-oracle work bounded.
func scanDecimalShape(s string) bool {
	if s == "" {
		return false
	}
	if s[0] == '+' || s[0] == '-' {
		s = s[1:]
	}
	mant := s
	if i := strings.IndexAny(s, "eE"); i >= 0 {
		if !boundedExp(s[i+1:]) {
			return false
		}
		mant = s[:i]
	}
	intPart := mant
	if i := strings.IndexByte(mant, '.'); i >= 0 {
		intPart = mant[:i]
		frac := mant[i+1:]
		if frac == "" || intPart == "" {
			return false
		}
		if !allDigits(frac) {
			return false
		}
	}
	return intPart != "" && allDigits(intPart)
}

func allDigits(s string) bool {
	if s == "" {
		return false
	}
	for i := range len(s) {
		if s[i] < '0' || s[i] > '9' {
			return false
		}
	}
	return true
}

func boundedExp(exp string) bool {
	if exp == "" {
		return false
	}
	if exp[0] == '+' || exp[0] == '-' {
		exp = exp[1:]
	}
	if !allDigits(exp) || len(exp) > 5 {
		return false
	}
	v := 0
	for i := range len(exp) {
		v = v*10 + int(exp[i]-'0')
	}
	return v <= maxShapeExponent
}

// splitShape splits a shape-accepted string into sign, integer digits,
// fraction digits and exponent ("" when absent); exponents are normalized
// to a signed integer value.
func splitShape(s string) (neg bool, intPart, frac, exp string, expVal int, ok bool) {
	if s == "" {
		return false, "", "", "", 0, false
	}
	if s[0] == '+' {
		s = s[1:]
	} else if s[0] == '-' {
		neg = true
		s = s[1:]
	}
	if i := strings.IndexAny(s, "eE"); i >= 0 {
		exp = s[i+1:]
		s = s[:i]
		sign := 1
		if exp != "" && (exp[0] == '+' || exp[0] == '-') {
			if exp[0] == '-' {
				sign = -1
			}
			exp = exp[1:]
		}
		for j := range len(exp) {
			expVal = expVal*10 + int(exp[j]-'0')
		}
		expVal *= sign
	}
	if i := strings.IndexByte(s, '.'); i >= 0 {
		intPart, frac = s[:i], s[i+1:]
	} else {
		intPart = s
	}
	return neg, intPart, frac, exp, expVal, intPart != ""
}

// shapeRat parses a shape-accepted string exactly with the rational oracle.
func shapeRat(s string) (*big.Rat, bool) {
	if _, _, _, _, expVal, ok := splitShape(s); !ok || expVal > maxShapeExponent || expVal < -maxShapeExponent {
		return nil, false
	}
	r, ok := new(big.Rat).SetString(s)
	return r, ok
}

// FuzzParse checks public parsing against an independently accepted grammar
// subset and an exact rational oracle. Its per-call limits bound fuzz work.
func FuzzParse(f *testing.F) {
	for _, seed := range []string{
		"1.25", "-0.001", "1234567890123456789", "0.0000001", "9E+9", "-7.5E-2",
		"0", "100", ".5", "5.", "-0.00", "1.2E+2147483648",
	} {
		f.Add([]byte(seed))
	}
	f.Fuzz(func(t *testing.T, data []byte) {
		if len(data) > 4096 {
			return
		}
		s := string(data)
		value, _, err := decimal.ParseWithContext(s, decimal.Context{}.WithBudget(decimal.Budget{
			MaxInputBytes: 4096, MaxDigits: 4096,
		}))
		requireFuzzRepresentation(t, value)
		if scanDecimalShape(s) {
			oracle, ok := shapeRat(s)
			if !ok {
				t.Fatalf("independent grammar accepted %q but rational oracle refused it", s)
			}
			if err != nil {
				t.Fatalf("public parser rejected independent grammar subset %q: %v", s, err)
			}
			canonical, err := value.Text(8192)
			if err != nil {
				t.Fatalf("Text(Parse(%q)): %v", s, err)
			}
			got, ok := new(big.Rat).SetString(canonical)
			if !ok || got.Cmp(oracle) != 0 {
				t.Fatalf("numeric disagreement for %q: canonical %q, want %s", s, canonical, oracle.RatString())
			}
		}
		if err == nil {
			canonical, err := value.Text(8192)
			if err != nil || !json.Valid([]byte(canonical)) {
				t.Fatalf("public parser accepted %q but canonical text is %q, %v", s, canonical, err)
			}
		}
	})
}

// FuzzRoundtrip checks the public canonical-text bijection on successful
// bounded parses, including cohort-preserving trailing zeros and zero scale.
func FuzzRoundtrip(f *testing.F) {
	for _, seed := range []string{
		"001.2500", "+3", "-0.500", "12E+004", "0.000", "-000", "7.5E-2",
		"1000", ".5", "5.", "1.2300", "0E+9", "1.2E+2147483648",
	} {
		f.Add(seed)
	}
	f.Fuzz(func(t *testing.T, s string) {
		if len(s) > 4096 {
			return
		}
		value, _, err := decimal.ParseWithContext(s, decimal.Context{}.WithBudget(decimal.Budget{
			MaxInputBytes: 4096, MaxDigits: 4096,
		}))
		requireFuzzRepresentation(t, value)
		if err != nil {
			if scanDecimalShape(s) {
				t.Fatalf("public parser rejected independent grammar subset %q: %v", s, err)
			}
			return
		}
		canonical, err := value.Text(8192)
		if err != nil {
			t.Fatalf("Text(Parse(%q)): %v", s, err)
		}
		again, err := decimal.Parse(canonical)
		requireFuzzRepresentation(t, again)
		if err != nil {
			t.Fatalf("canonical text %q does not parse: %v", canonical, err)
		}
		second, err := again.Text(8192)
		if err != nil || second != canonical || !again.Equal(value) {
			t.Fatalf("roundtrip changed %q -> %q -> %q, %v", s, canonical, second, err)
		}
		if !json.Valid([]byte(canonical)) || strings.HasPrefix(canonical, "+") {
			t.Fatalf("canonical text %q is not a JSON number", canonical)
		}
	})
}

// FuzzArithmetic is the arithmetic-law target: on
// shape-accepted operands (exponents within ±10000, so exact work stays
// bounded), the library's exact Add, Sub and Mul equal the
// rational oracle at the GDA exponents (min(ex, ey), ex+ey), Add and Mul
// commute in cohort, x - y = -(y - x), and a context sum at a precision
// and mode derived from the operands lies within one unit of the exact sum
// (the reversed operations use the budgeted forms, which must agree)
// on the side its direction bit reports, with Inexact exactly when it
// differs.
func FuzzArithmetic(f *testing.F) {
	for _, pair := range [][2]string{
		{"1.25", "2.50"}, {"-0.001", "0.001"}, {"9999999999999999999", "1"},
		{"0", "0"}, {"1E+3", "-1E-3"}, {"-7.5", "-2.5"}, {"99999999999999999999999999999999999999", "1"},
	} {
		f.Add(pair[0], pair[1])
	}
	budget := decimal.Budget{MaxDigits: 1 << 16, MaxWork: 1 << 24}
	f.Fuzz(func(t *testing.T, a, b string) {
		if !scanDecimalShape(a) || !scanDecimalShape(b) || len(a) > 200 || len(b) > 200 {
			return
		}
		ra, _ := shapeRat(a)
		rb, _ := shapeRat(b)
		x, err1 := decimal.Parse(a)
		requireFuzzRepresentation(t, x)
		y, err2 := decimal.Parse(b)
		requireFuzzRepresentation(t, y)
		if err1 != nil || err2 != nil || ra == nil || rb == nil {
			t.Fatalf("shape-accepted operands %q, %q: %v %v", a, b, err1, err2)
		}
		exact := func(name string, got decimal.Decimal, err error, want *big.Rat, exponent int32) {
			t.Helper()
			if err != nil {
				t.Fatalf("%s(%q, %q): %v", name, a, b, err)
			}
			r, ok := new(big.Rat).SetString(got.String())
			if !ok || r.Cmp(want) != 0 || got.Exponent() != exponent {
				t.Fatalf("%s(%q, %q) = %v, want %s at exponent %d", name, a, b, got, want.RatString(), exponent)
			}
		}
		lo := min(x.Exponent(), y.Exponent())
		sum, err := x.Add(y)
		requireFuzzRepresentation(t, sum)
		exact("Add", sum, err, new(big.Rat).Add(ra, rb), lo)
		diff, err := x.Sub(y)
		requireFuzzRepresentation(t, diff)
		exact("Sub", diff, err, new(big.Rat).Sub(ra, rb), lo)
		prod, err := x.Mul(y)
		requireFuzzRepresentation(t, prod)
		exact("Mul", prod, err, new(big.Rat).Mul(ra, rb), x.Exponent()+y.Exponent())
		{
			rev, _, _ := y.AddWithContext(x, decimal.Context{}.WithBudget(budget))
			requireFuzzRepresentation(t, rev)
			if rev.String() != sum.String() {
				t.Fatalf("Add does not commute: %v + %v = %v, reversed %v", x, y, sum, rev)
			}
		}
		{
			rev, _, _ := y.MulWithContext(x, decimal.Context{}.WithBudget(budget))
			requireFuzzRepresentation(t, rev)
			if rev.String() != prod.String() {
				t.Fatalf("Mul does not commute: %v * %v = %v, reversed %v", x, y, prod, rev)
			}
		}
		{
			rev, _, _ := y.SubWithContext(x, decimal.Context{}.WithBudget(budget))
			requireFuzzRepresentation(t, rev)
			negative := rev.Neg()
			requireFuzzRepresentation(t, negative)
			if !negative.Equal(diff) {
				t.Fatalf("x - y != -(y - x): %v, %v", diff, rev)
			}
		}
		p := uint32(1 + len(a)%40)
		mode := decimal.RoundingMode(len(b) % 7)
		ctx, err := decimal.NewContext(p, mode, nil, 0)
		if err != nil {
			t.Fatal(err)
		}
		r, cond, err := x.AddWithContext(y, ctx.WithBudget(budget))
		requireFuzzRepresentation(t, r)
		if err != nil {
			t.Fatalf("AddWithContext(%q, %q, p=%d, %v): %v", a, b, p, mode, err)
		}
		rv, _ := new(big.Rat).SetString(r.String())
		want := new(big.Rat).Add(ra, rb)
		side := rv.Cmp(want)
		if (side != 0) != (cond&decimal.Inexact != 0) || side != cond.Direction() || r.CoefficientDigits() > uint64(p) {
			t.Fatalf("AddWithContext(%q, %q, p=%d, %v) = %v %v; exact %s", a, b, p, mode, r, cond, want.RatString())
		}
		if side != 0 {
			// Within one unit in the last place of the p-digit result.
			ulp := new(big.Rat).SetFrac(big.NewInt(1), big.NewInt(1))
			e := int(r.Exponent())
			ten := new(big.Rat).SetInt64(10)
			for range max(e, -e) {
				if e > 0 {
					ulp.Mul(ulp, ten)
				} else {
					ulp.Quo(ulp, ten)
				}
			}
			if gap := new(big.Rat).Abs(new(big.Rat).Sub(rv, want)); gap.Cmp(ulp) >= 0 {
				t.Fatalf("AddWithContext(%q, %q, p=%d, %v) = %v is %s from the exact sum, not within one unit", a, b, p, mode, r, gap.RatString())
			}
		}
	})
}

// FuzzDivision checks DivToExponent and Div against a
// self-contained math/big.Rat oracle written over the public API only; the
// internal oracles of division_test.go are a second, independent check.
func FuzzDivision(f *testing.F) {
	for _, seed := range []struct {
		a, b   string
		target int8
		mode   uint8
	}{
		{"1", "8", -2, 0}, {"-1", "3", 0, 6}, {"2.400", "2.0", -2, 0},
		{"100", "1", 1, 7}, {"12345678901234567890123456789012345678", "7", -40, 1},
	} {
		f.Add(seed.a, seed.b, seed.target, seed.mode)
	}
	f.Fuzz(func(t *testing.T, a, b string, target int8, modeByte uint8) {
		x, _, err := decimal.ParseWithContext(a, decimal.Context{}.WithBudget(decimal.Budget{MaxInputBytes: 200}))
		requireFuzzRepresentation(t, x)
		if err != nil {
			return
		}
		y, _, err := decimal.ParseWithContext(b, decimal.Context{}.WithBudget(decimal.Budget{MaxInputBytes: 200}))
		requireFuzzRepresentation(t, y)
		if err != nil || y.IsZero() || x.Exponent() < -60 || x.Exponent() > 60 || y.Exponent() < -60 || y.Exponent() > 60 {
			return
		}
		mode := decimal.RoundingMode(modeByte % 8)
		rx, _ := new(big.Rat).SetString(x.String())
		ry, _ := new(big.Rat).SetString(y.String())
		q := new(big.Rat).Quo(rx, ry)
		got, cond, err := x.DivToExponent(y, int32(target), mode)
		requireFuzzRepresentation(t, got)
		scale := new(big.Rat).SetInt(new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(max(target, -target))), nil))
		v := new(big.Rat).Abs(q)
		if target >= 0 {
			v.Quo(v, scale)
		} else {
			v.Mul(v, scale)
		}
		floor := new(big.Int).Quo(v.Num(), v.Denom())
		frac := new(big.Rat).Sub(v, new(big.Rat).SetInt(floor))
		negative := q.Sign() < 0
		up := false
		if frac.Sign() != 0 {
			half := frac.Cmp(big.NewRat(1, 2))
			switch mode {
			case decimal.AwayFromZero:
				up = true
			case decimal.TowardPositiveInfinity:
				up = !negative
			case decimal.TowardNegativeInfinity:
				up = negative
			case decimal.TiesToEven:
				up = half > 0 || half == 0 && floor.Bit(0) == 1
			case decimal.TiesAwayFromZero:
				up = half >= 0
			case decimal.TiesTowardZero:
				up = half > 0
			}
		}
		if mode == decimal.Exact && frac.Sign() != 0 {
			if !errors.Is(err, decimal.ErrInexact) {
				t.Fatalf("%v/%v t=%d Exact: want refusal, got (%v, %v)", x, y, target, got, err)
			}
			return
		}
		if up {
			floor.Add(floor, big.NewInt(1))
		}
		want := new(big.Rat).SetInt(floor)
		if target >= 0 {
			want.Mul(want, scale)
		} else {
			want.Quo(want, scale)
		}
		if negative {
			want.Neg(want)
		}
		rgot, _ := new(big.Rat).SetString(got.String())
		if err != nil || rgot.Cmp(want) != 0 || got.Exponent() != int32(target) {
			t.Fatalf("%v/%v t=%d %v: got (%v, %v, %v), want %s at exponent %d", x, y, target, mode, got, cond, err, want.RatString(), target)
		}
		if (frac.Sign() != 0) != (cond&decimal.Inexact != 0) {
			t.Fatalf("%v/%v t=%d: Inexact %v disagrees with oracle", x, y, target, cond)
		}
		// Bare Div: exact exactly when the reduced denominator has only 2s and 5s.
		exact, err := x.Div(y)
		requireFuzzRepresentation(t, exact)
		den := new(big.Int).Set(q.Denom())
		for _, factor := range []int64{2, 5} {
			for new(big.Int).Mod(den, big.NewInt(factor)).Sign() == 0 {
				den.Quo(den, big.NewInt(factor))
			}
		}
		if den.Cmp(big.NewInt(1)) != 0 {
			if !errors.Is(err, decimal.ErrInexact) {
				t.Fatalf("Div %v/%v: want remedy refusal, got (%v, %v)", x, y, exact, err)
			}
			return
		}
		rexact, _ := new(big.Rat).SetString(exact.String())
		if err != nil || rexact.Cmp(q) != 0 || exact.Exponent() > x.Exponent()-y.Exponent() {
			t.Fatalf("Div %v/%v: got (%v, %v), want %s", x, y, exact, err, q.RatString())
		}
	})
}

// FuzzFromRat checks the math/big.Rat conversion over the public API: the
// math/big boundary division agrees with the independent Div kernel on the
// same numerator and denominator for exponent, context and exact targets,
// and Rat of every result returns the exact value.
func FuzzFromRat(f *testing.F) {
	for _, seed := range []struct {
		n, d   string
		target int8
		mode   uint8
		prec   uint8
	}{
		{"1", "3", -5, 0, 7}, {"-22", "7", 0, 6, 1}, {"5", "2", 2, 7, 34},
		{"100", "1", 1, 1, 3}, {"123456789012345678901234567890", "-8", -40, 2, 20},
	} {
		f.Add(seed.n, seed.d, seed.target, seed.mode, seed.prec)
	}
	f.Fuzz(func(t *testing.T, ns, ds string, target int8, modeByte, precByte uint8) {
		if len(ns) > 80 || len(ds) > 80 {
			return
		}
		n, ok1 := new(big.Int).SetString(ns, 10)
		d, ok2 := new(big.Int).SetString(ds, 10)
		if !ok1 || !ok2 || d.Sign() == 0 {
			return
		}
		r := new(big.Rat).SetFrac(n, d)
		x, err := decimal.FromBigInt(r.Num())
		requireFuzzRepresentation(t, x)
		if err != nil {
			t.Fatal(err)
		}
		y, err := decimal.FromBigInt(r.Denom())
		requireFuzzRepresentation(t, y)
		if err != nil {
			t.Fatal(err)
		}
		mode := decimal.RoundingMode(modeByte % 8)
		same := func(what string, a decimal.Decimal, ac decimal.Conditions, ae error, b decimal.Decimal, bc decimal.Conditions, be error) {
			if (ae == nil) != (be == nil) || ae == nil && (!a.Equal(b) || a.Exponent() != b.Exponent() || ac != bc) {
				t.Fatalf("%s %s: FromRat (%v, %v, %v) vs Div (%v, %v, %v)", r.RatString(), what, a, ac, ae, b, bc, be)
			}
			if ae != nil {
				return
			}
			back, err := a.Rat(nil)
			if err != nil {
				t.Fatalf("%s %s: Rat of %v: %v", r.RatString(), what, a, err)
			}
			if want, _ := new(big.Rat).SetString(a.String()); back.Cmp(want) != 0 {
				t.Fatalf("%s %s: Rat of %v = %s", r.RatString(), what, a, back.RatString())
			}
		}
		a, ac, ae := decimal.FromRatToExponent(r, int32(target), mode)
		requireFuzzRepresentation(t, a)
		b, bc, be := x.DivToExponent(y, int32(target), mode)
		requireFuzzRepresentation(t, b)
		same("exponent", a, ac, ae, b, bc, be)
		ctx, err := decimal.NewContext(uint32(1+precByte%60), mode, nil, 0)
		if err != nil {
			t.Fatal(err)
		}
		a, ac, ae = decimal.FromRatWithContext(r, ctx)
		requireFuzzRepresentation(t, a)
		b, bc, be = x.DivWithContext(y, ctx)
		requireFuzzRepresentation(t, b)
		same("context", a, ac, ae, b, bc, be)
		a, ae = decimal.FromRat(r)
		requireFuzzRepresentation(t, a)
		b, be = x.Div(y)
		requireFuzzRepresentation(t, b)
		same("exact", a, 0, ae, b, 0, be)
	})
}

// FuzzFloat64Egress checks float64 egress over the public API against
// math/big: TowardNegativeInfinity and TowardPositiveInfinity bracket the
// decimal with adjacent doubles (MaxFloat64 and ±Inf at overflow) without
// the wrong direction bit, and Float64 is the nearer bracket, ties to even,
// with an exactness signal that holds exactly when the double equals it.
func FuzzFloat64Egress(f *testing.F) {
	for _, seed := range []string{"0.1", "-9007199254740993", "1E+400", "2.4703282292062327208828439643411068618252990130716238221279284125033775363510437593264991818081799618989828234772285886546332835517796989819938739800539093906315035659515570226392290858392449105184435931802849936536152500319370457678249219365623669863658480757001585769269903706311928279558551332927834338409351978015531246597263579574622766465272827220056374006485499977096599470454020828166226237857393450736339007967761930577506740176324673600968951340535537458516661134223766678604162159680461914467291840300530057530849048765391711386591646239524912623653881879636239373280423891018672348497668235089863388587925628302755995657524455507255189313690836254779186948667994968324049705821028513185451396213837722826145437693412532098591327667236328125E-324", "0E-9"} {
		f.Add(seed)
	}
	f.Fuzz(func(t *testing.T, text string) {
		d, _, err := decimal.ParseWithContext(text, decimal.Context{}.WithBudget(decimal.Budget{MaxInputBytes: 2000}))
		requireFuzzRepresentation(t, d)
		if err != nil || d.Exponent() < -2000 || d.Exponent() > 2000 {
			return
		}
		exact, _ := new(big.Rat).SetString(d.String())
		asRat := func(v float64) *big.Rat {
			if math.IsInf(v, 0) {
				r := new(big.Rat).SetInt(new(big.Int).Lsh(big.NewInt(1), 1024))
				if v < 0 {
					r.Neg(r)
				}
				return r
			}
			return new(big.Rat).SetFloat64(v)
		}
		lo, lc, err1 := d.Float64Rounded(decimal.TowardNegativeInfinity)
		hi, hc, err2 := d.Float64Rounded(decimal.TowardPositiveInfinity)
		cmpTo := func(v float64) int { // sign(v − exact), ±Inf beyond every decimal
			if math.IsInf(v, 0) {
				if v > 0 {
					return 1
				}
				return -1
			}
			return asRat(v).Cmp(exact)
		}
		if err1 != nil || err2 != nil || cmpTo(lo) > 0 || cmpTo(hi) < 0 ||
			lo != hi && math.Nextafter(lo, math.Inf(1)) != hi || lc&decimal.Increased != 0 || hc&decimal.Decreased != 0 {
			t.Fatalf("%s: enclosure (%v %v %v, %v %v %v)", d, lo, lc, err1, hi, hc, err2)
		}
		near, nc := d.Float64()
		if (lo == hi) != (nc&decimal.Inexact == 0) || near != lo && near != hi {
			t.Fatalf("%s: Float64 (%v, %v) outside [%v, %v]", d, near, nc, lo, hi)
		}
		if lo != hi && !math.IsInf(lo, 0) && !math.IsInf(hi, 0) {
			dl := new(big.Rat).Sub(exact, asRat(lo))
			dh := new(big.Rat).Sub(asRat(hi), exact)
			want := lo
			if c := dl.Cmp(dh); c > 0 || c == 0 && math.Float64bits(math.Abs(lo))&1 == 1 {
				want = hi
			}
			if near != want && !(want == math.MaxFloat64 || want == -math.MaxFloat64) {
				t.Fatalf("%s: Float64 %v, want %v", d, near, want)
			}
		}
		// Every mode picks lo or hi by the mode's rule, with the direction of
		// its choice, Overflow exactly when the unbounded rounding exceeds
		// MaxFloat64, and Subnormal/Underflow by |d| < 2^−1022.
		negative := exact.Sign() < 0
		magnitude := new(big.Rat).Abs(exact)
		huge := magnitude.Cmp(new(big.Rat).SetInt(new(big.Int).Lsh(big.NewInt(1), 1024))) >= 0
		tiny := exact.Sign() != 0 && magnitude.Cmp(new(big.Rat).SetFrac(big.NewInt(1), new(big.Int).Lsh(big.NewInt(1), 1022))) < 0
		for mode := range decimal.Exact {
			got, c, err := d.Float64Rounded(mode)
			if err != nil {
				t.Fatalf("%s %v: %v", d, mode, err)
			}
			if got != lo && got != hi {
				t.Fatalf("%s %v: %v outside [%v, %v]", d, mode, got, lo, hi)
			}
			awayFromZero := got != 0 && (got == hi) != negative
			switch mode {
			case decimal.TowardNegativeInfinity:
				if got != lo {
					t.Fatalf("%s floor: %v", d, got)
				}
			case decimal.TowardPositiveInfinity:
				if got != hi {
					t.Fatalf("%s ceiling: %v", d, got)
				}
			case decimal.TowardZero:
				if lo != hi && awayFromZero {
					t.Fatalf("%s toward zero: %v", d, got)
				}
			case decimal.AwayFromZero:
				if lo != hi && !awayFromZero {
					t.Fatalf("%s away from zero: %v", d, got)
				}
			}
			inexact := lo != hi
			if (c&decimal.Inexact != 0) != inexact || inexact && (c&decimal.Increased != 0) != (cmpTo(got) > 0) {
				t.Fatalf("%s %v: conditions %v for %v", d, mode, c, got)
			}
			overflow := math.IsInf(got, 0) || math.Abs(got) == math.MaxFloat64 && huge
			if (c&decimal.Overflow != 0) != overflow || (c&decimal.Subnormal != 0) != tiny || (c&decimal.Underflow != 0) != (tiny && inexact) {
				t.Fatalf("%s %v: conditions %v for %v (overflow %t, tiny %t)", d, mode, c, got, overflow, tiny)
			}
		}
	})
}

// FuzzCompareFloat64 checks that CompareFloat64 orders a decimal against
// any double exactly as big.Rat does, with ±Inf beyond every decimal and
// NaN refused.
func FuzzCompareFloat64(f *testing.F) {
	for _, seed := range []struct {
		d    string
		bits uint64
	}{{"0.1", 0x3FB999999999999A}, {"9007199254740993", 0x4340000000000000}, {"-0", 0x8000000000000000}, {"1E+400", 0x7FF0000000000000}, {"1", 0x7FF8000000000001}} {
		f.Add(seed.d, seed.bits)
	}
	f.Fuzz(func(t *testing.T, text string, bitsIn uint64) {
		d, _, err := decimal.ParseWithContext(text, decimal.Context{}.WithBudget(decimal.Budget{MaxInputBytes: 2000}))
		requireFuzzRepresentation(t, d)
		if err != nil || d.Exponent() < -2000 || d.Exponent() > 2000 {
			return
		}
		g := math.Float64frombits(bitsIn)
		got, err := d.CompareFloat64(g)
		switch {
		case math.IsNaN(g):
			if !errors.Is(err, decimal.ErrInvalidOperation) {
				t.Fatalf("CompareFloat64(%s, NaN): (%d, %v)", d, got, err)
			}
			return
		case math.IsInf(g, 0):
			if want := -int(math.Copysign(1, g)); err != nil || got != want {
				t.Fatalf("CompareFloat64(%s, %v) = (%d, %v)", d, g, got, err)
			}
			return
		}
		exact, _ := new(big.Rat).SetString(d.String())
		if want := exact.Cmp(new(big.Rat).SetFloat64(g)); err != nil || got != want {
			t.Fatalf("CompareFloat64(%s, %v) = (%d, %v), want %d", d, g, got, err, want)
		}
	})
}

// FuzzFromFloat64 checks float64 ingress over the public API: the
// shortest regime equals strconv's shortest text and round-trips, the
// exact regime equals the double's big.Rat, and rounded ingress equals
// FromRat on that rational for value, Conditions and error.
func FuzzFromFloat64(f *testing.F) {
	for _, seed := range []uint64{0x3FB999999999999A, 1, 0x7FEFFFFFFFFFFFFF, 0x8000000000000000, 0x4005666666666666} {
		f.Add(seed, int16(-2), uint8(0), uint8(7))
	}
	f.Fuzz(func(t *testing.T, bitsIn uint64, target int16, modeByte, precByte uint8) {
		v := math.Float64frombits(bitsIn)
		if math.IsNaN(v) || math.IsInf(v, 0) {
			{
				refused, err := decimal.FromFloat64(v)
				requireFuzzRepresentation(t, refused)
				if !errors.Is(err, decimal.ErrConversionSyntax) {
					t.Fatalf("FromFloat64(%v): %v", v, err)
				}
			}
			return
		}
		r := new(big.Rat).SetFloat64(v)
		s, err := decimal.FromFloat64(v)
		requireFuzzRepresentation(t, s)
		want, _ := new(big.Rat).SetString(strconv.FormatFloat(v, 'e', -1, 64))
		if got, _ := new(big.Rat).SetString(s.String()); err != nil || got.Cmp(want) != 0 || s.Exponent() > 0 {
			t.Fatalf("FromFloat64(%v) = (%v, %v)", v, s, err)
		}
		e, err := decimal.FromFloat64Exact(v)
		requireFuzzRepresentation(t, e)
		if got, _ := new(big.Rat).SetString(e.String()); err != nil || got.Cmp(r) != 0 {
			t.Fatalf("FromFloat64Exact(%v) = (%v, %v)", v, e, err)
		}
		mode := decimal.RoundingMode(modeByte % 8)
		a, ac, ae := decimal.FromFloat64ToExponent(v, int32(target), mode)
		requireFuzzRepresentation(t, a)
		b, bc, be := decimal.FromRatToExponent(r, int32(target), mode)
		requireFuzzRepresentation(t, b)
		if (ae == nil) != (be == nil) || ae == nil && (!a.Equal(b) || a.Exponent() != b.Exponent() || ac != bc) {
			t.Fatalf("%v t=%d %v: (%v, %v, %v) vs FromRat (%v, %v, %v)", v, target, mode, a, ac, ae, b, bc, be)
		}
		var guards *decimal.ExponentGuards
		if precByte&0x80 != 0 { // guarded, around the double's own decades
			emin := int32(target) % 400
			guards = &decimal.ExponentGuards{Emin: emin, Emax: emin + int32(precByte%97)}
		}
		traps := decimal.Conditions(0)
		if precByte&0x40 != 0 {
			traps = decimal.Inexact | decimal.Underflow
		}
		ctx, err := decimal.NewContext(uint32(1+precByte%60), mode, guards, traps)
		if err != nil {
			t.Fatal(err)
		}
		// The budgeted form is the unbudgeted result or a resource refusal.
		limit := decimal.Budget{MaxWork: uint64(precByte) * 40, MaxDigits: uint64(modeByte%50 + 1)}
		q, qc, qe := decimal.FromFloat64ToExponentWithBudget(v, int32(target), mode, limit)
		requireFuzzRepresentation(t, q)
		if qe != nil && !errors.Is(qe, decimal.ErrInsufficientStorage) && (ae == nil) || qe == nil && (ae != nil || !q.Equal(a) || qc != ac) {
			t.Fatalf("%v t=%d %v budget %+v: (%v, %v, %v) vs (%v, %v, %v)", v, target, mode, limit, q, qc, qe, a, ac, ae)
		}
		a, ac, ae = decimal.FromFloat64WithContext(v, ctx)
		requireFuzzRepresentation(t, a)
		b, bc, be = decimal.FromRatWithContext(r, ctx)
		requireFuzzRepresentation(t, b)
		if (ae == nil) != (be == nil) || ae == nil && (!a.Equal(b) || a.Exponent() != b.Exponent() || ac != bc) {
			t.Fatalf("%v %+v %v: (%v, %v, %v) vs FromRat (%v, %v, %v)", v, guards, mode, a, ac, ae, b, bc, be)
		}
	})
}

// FuzzParseToExponent checks rounding parse over the public API: whenever Parse
// succeeds, ParseToExponent equals Parse followed by Quantize in value,
// cohort, Conditions and error sentinel, for string and []byte carriers;
// otherwise it returns a typed error or a magnitude-resolved value, never a
// panic. Seeds live in testdata/fuzz/FuzzParseToExponent.
func FuzzParseToExponent(f *testing.F) {
	f.Add("2.675", int32(-2), uint8(0))
	f.Add("1e-99999999999", int32(-2), uint8(5))
	f.Fuzz(func(t *testing.T, s string, target int32, modeByte uint8) {
		if len(s) > 4096 {
			return
		}
		mode := decimal.RoundingMode(modeByte % 9) // includes one invalid mode
		// Budgeted calls: an unbudgeted pad toward MinInt32 would demand
		// about 2^31 digits per fuzz worker.
		limit := decimal.Budget{MaxDigits: 1 << 20}
		a, ac, ae := decimal.ParseToExponentWithBudget(s, target, mode, limit)
		requireFuzzRepresentation(t, a)
		b, bc, be := decimal.ParseToExponentWithBudget([]byte(s), target, mode, limit)
		requireFuzzRepresentation(t, b)
		if (ae == nil) != (be == nil) || ae == nil && (!a.Equal(b) || a.Exponent() != b.Exponent() || ac != bc) {
			t.Fatalf("%q: string (%v, %v, %v) vs bytes (%v, %v, %v)", s, a, ac, ae, b, bc, be)
		}
		parsed, err := decimal.Parse(s)
		requireFuzzRepresentation(t, parsed)
		if err != nil || mode > decimal.Exact {
			return
		}
		if d := int64(parsed.Exponent()) - int64(target); d > 100000 || d < -100000 {
			return // pads beyond 10^5 digits are exercised by named tests
		}
		want, wc, we := parsed.Quantize(target, mode)
		requireFuzzRepresentation(t, want)
		sentinel := func(err error) string {
			if ce, ok := errors.AsType[*decimal.Error](err); ok {
				return "trapped " + ce.Condition.String()
			}
			for _, code := range []decimal.ErrorCode{decimal.ErrExponentRange, decimal.ErrInsufficientStorage, decimal.ErrInvalidOperation} {
				if errors.Is(err, code) {
					return code.Error()
				}
			}
			if err != nil {
				return err.Error()
			}
			return ""
		}
		if sentinel(ae) != sentinel(we) || we == nil && (!a.Equal(want) || a.Exponent() != want.Exponent() || ac != wc) {
			t.Fatalf("%q t=%d %v: (%v, %v, %v), want (%v, %v, %v)", s, target, mode, a, ac, ae, want, wc, we)
		}
	})
}

// scanSource is a foreign decompose-only value for FuzzScan.
type scanSource struct {
	form        byte
	negative    bool
	coefficient []byte
	exponent    int32
}

func (s scanSource) Decompose([]byte) (byte, bool, []byte, int32) {
	return s.form, s.negative, s.coefficient, s.exponent
}

// FuzzScan checks database/sql scanning over the public API: for every accepted source
// kind, Decimal.Scan and NullDecimal.Scan equal the matching constructor
// (Parse, FromInt64, FromFloat64Exact, Compose) in value, cohort and error
// identity, and a failed scan leaves the receiver unchanged. Seeds live in
// testdata/fuzz/FuzzScan.
func FuzzScan(f *testing.F) {
	f.Add(uint8(0), "1.10", int64(0), uint64(0), int32(0))
	f.Add(uint8(3), "", int64(0), uint64(0x3FB999999999999A), int32(0))
	f.Add(uint8(4), "\x6e", int64(0), uint64(0), int32(-2))
	f.Add(uint8(6), "\x80", int64(-1), uint64(0), int32(0))
	f.Add(uint8(7), "", int64(1), uint64(3), int32(0))
	f.Add(uint8(8), "", int64(1), uint64(127), int32(-2000000000))
	f.Fuzz(func(t *testing.T, kind uint8, text string, integer int64, floatBits uint64, exponent int32) {
		if len(text) > 4096 {
			return
		}
		var src any
		var want decimal.Decimal
		requireFuzzRepresentation(t, want)
		var wantErr error
		switch kind % 9 {
		case 0:
			src = text
			want, wantErr = decimal.Parse(text)
			requireFuzzRepresentation(t, want)
		case 1:
			src = []byte(text)
			want, wantErr = decimal.Parse([]byte(text))
			requireFuzzRepresentation(t, want)
		case 2:
			src, want = integer, decimal.FromInt64(integer)
			requireFuzzRepresentation(t, want)
		case 3:
			v := math.Float64frombits(floatBits)
			src = v
			want, wantErr = decimal.FromFloat64Exact(v)
			requireFuzzRepresentation(t, want)
		case 4:
			source := scanSource{form: byte(integer & 3 % 3), negative: integer < 0, coefficient: []byte(text), exponent: exponent}
			src = source
			wantErr = want.Compose(source.form, source.negative, source.coefficient, source.exponent)
			requireFuzzRepresentation(t, want)
		case 6:
			x := new(big.Int).SetBytes([]byte(text))
			if integer < 0 {
				x.Neg(x)
			}
			src = x
			want, wantErr = decimal.FromBigInt(x)
			requireFuzzRepresentation(t, want)
		case 7:
			r := new(big.Rat).SetFrac(big.NewInt(integer), new(big.Int).SetUint64(floatBits|1))
			src = r
			want, wantErr = decimal.FromRat(r)
			requireFuzzRepresentation(t, want)
		case 8:
			x := new(big.Float).SetPrec(uint(floatBits%256 + 1)).SetInt64(integer)
			x.SetMantExp(x, int(exponent))
			src = x
			wantErr = decimal.ErrConversionSyntax
		default:
			src = struct{ text string }{text}
			wantErr = decimal.ErrConversionSyntax
		}
		sentinel := func(err error) string {
			for _, code := range []decimal.ErrorCode{decimal.ErrConversionSyntax, decimal.ErrExponentRange, decimal.ErrInsufficientStorage, decimal.ErrInvalidOperation, decimal.ErrInexact} {
				if errors.Is(err, code) {
					return code.Error()
				}
			}
			if err != nil {
				return err.Error()
			}
			return ""
		}
		prior := decimal.MustParse("-7.25")
		requireFuzzRepresentation(t, prior)
		got := prior
		requireFuzzRepresentation(t, got)
		err := got.Scan(src)
		requireFuzzRepresentation(t, got)
		if sentinel(err) != sentinel(wantErr) {
			t.Fatalf("Scan(%T): %v, want %v", src, err, wantErr)
		}
		if err != nil {
			if !got.Equal(prior) || got.Exponent() != prior.Exponent() {
				t.Fatalf("failed Scan(%T) changed the receiver to %v", src, got)
			}
			return
		}
		if !got.Equal(want) || got.Exponent() != want.Exponent() {
			t.Fatalf("Scan(%T) = %v, want %v", src, got, want)
		}
		var null decimal.NullDecimal
		{
			err := null.Scan(src)
			requireFuzzRepresentation(t, null.Decimal)
			if err != nil || !null.Valid || !null.Decimal.Equal(want) || null.Decimal.Exponent() != want.Exponent() {
				t.Fatalf("NullDecimal.Scan(%T) = (%+v, %v)", src, null, err)
			}
		}
	})
}

// FuzzTwosComplement checks two's-complement exchange over the public API: any
// nonempty two's-complement input decodes, re-encodes at its own width to
// the identical bytes in both byte orders, and survives SQLDecimal
// Decompose followed by Compose with its exponent.
func FuzzTwosComplement(f *testing.F) {
	for _, seed := range [][]byte{{0x85}, {0xFF, 0xFF, 0x85}, {0x00, 0x80}, {0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}, bytes.Repeat([]byte{0xFF}, 33)} {
		f.Add(seed, int8(-2))
	}
	f.Fuzz(func(t *testing.T, b []byte, exponent int8) {
		if len(b) == 0 || len(b) > 256 {
			return
		}
		for _, order := range []binary.ByteOrder{binary.BigEndian, binary.LittleEndian} {
			d, err := decimal.NewTwosComplement(b, order, int32(exponent))
			requireFuzzRepresentation(t, d)
			if err != nil {
				t.Fatalf("%x: %v", b, err)
			}
			out, err := d.AppendTwosComplement(nil, len(b), order)
			if err != nil || !bytes.Equal(out, b) {
				t.Fatalf("%x %v: re-encoded %x, %v", b, order, out, err)
			}
			form, negative, coefficient, e := decimal.SQLDecimal{Decimal: d}.Decompose(nil)
			var back decimal.Decimal
			requireFuzzRepresentation(t, back)
			{
				err := back.Compose(form, negative, coefficient, e)
				requireFuzzRepresentation(t, back)
				if err != nil || !back.Equal(d) || back.Exponent() != d.Exponent() {
					t.Fatalf("%x: Compose -> (%v, %v), want %v", b, back, err, d)
				}
			}
		}
	})
}

// FuzzQuoRem checks Quo, Rem and RemNear against a
// self-contained math/big oracle over the public API: q = trunc(x/y) at
// exponent 0, x − q·y and x − n·y (nearest-even n) at min(ex, ey), with
// unsigned zeros. The second operand's exponent is shifted by gap so the
// fuzzer reaches the split, stream and modular paths.
func FuzzQuoRem(f *testing.F) {
	for _, seed := range []struct {
		a, b string
		gap  int16
	}{
		{"10.5", "3", 0}, {"-7", "2", 0}, {"12345E-2", "7E+1", 0}, {"1", "7", -1500},
		{"99", "100", 0}, {"9999999999", "3", 20}, {"1001", "1", 3}, {"0.000", "1", 2},
	} {
		f.Add(seed.a, seed.b, seed.gap)
	}
	f.Fuzz(func(t *testing.T, a, b string, gap int16) {
		x, _, err := decimal.ParseWithContext(a, decimal.Context{}.WithBudget(decimal.Budget{MaxInputBytes: 200}))
		requireFuzzRepresentation(t, x)
		if err != nil {
			return
		}
		y0, _, err := decimal.ParseWithContext(b, decimal.Context{}.WithBudget(decimal.Budget{MaxInputBytes: 200}))
		requireFuzzRepresentation(t, y0)
		if err != nil || y0.IsZero() {
			return
		}
		ey := int64(y0.Exponent()) + int64(gap%3000)
		if ey < -3000 || ey > 3000 || x.Exponent() < -3000 || x.Exponent() > 3000 {
			return
		}
		coefficient := func(d decimal.Decimal) *big.Int {
			r, _ := new(big.Rat).SetString(d.String())
			e := int64(d.Exponent())
			p := new(big.Int).Exp(big.NewInt(10), big.NewInt(max(e, -e)), nil)
			if e >= 0 {
				r.Quo(r, new(big.Rat).SetInt(p))
			} else {
				r.Mul(r, new(big.Rat).SetInt(p))
			}
			return new(big.Int).Set(r.Num())
		}
		cy := coefficient(y0)
		y, err := decimal.Parse(cy.String() + "E" + strconv.FormatInt(ey, 10))
		requireFuzzRepresentation(t, y)
		if err != nil {
			t.Fatal(err)
		}
		cx := coefficient(x)
		m := min(int64(x.Exponent()), ey)
		pow := func(n int64) *big.Int { return new(big.Int).Exp(big.NewInt(10), big.NewInt(n), nil) }
		X := new(big.Int).Mul(cx, pow(int64(x.Exponent())-m))
		Y := new(big.Int).Mul(cy, pow(ey-m))
		q, r := new(big.Int).QuoRem(X, Y, new(big.Int))
		n := new(big.Int).Set(q)
		if c := new(big.Int).Lsh(new(big.Int).Abs(r), 1).CmpAbs(Y); c > 0 || c == 0 && q.Bit(0) == 1 {
			n.Add(n, big.NewInt(int64(X.Sign()*Y.Sign())))
		}
		rn := new(big.Int).Sub(X, new(big.Int).Mul(n, Y))
		for _, c := range []struct {
			name string
			got  func() (decimal.Decimal, error)
			want *big.Int
			exp  int64
		}{
			{"Quo", func() (decimal.Decimal, error) { return x.Quo(y) }, q, 0},
			{"Rem", func() (decimal.Decimal, error) { return x.Rem(y) }, r, m},
			{"RemNear", func() (decimal.Decimal, error) { return x.RemNear(y) }, rn, m},
		} {
			got, err := c.got()
			requireFuzzRepresentation(t, got)
			if err != nil {
				t.Fatalf("%v %s %v: %v", x, c.name, y, err)
			}
			if gc := coefficient(got); gc.Cmp(c.want) != 0 || int64(got.Exponent()) != c.exp || c.want.Sign() == 0 && strings.HasPrefix(got.String(), "-") {
				t.Fatalf("%v %s %v = %v, want %v at exponent %d", x, c.name, y, got, c.want, c.exp)
			}
		}
	})
}

// FuzzQuantize is the scale/quantize property target:
// Quantize publishes exactly the target exponent, within one unit of the
// exact value on the side its direction bit reports (Inexact exactly when
// it moved), the directed modes enclose every other mode's result, the
// result is a fixed point under Exact, and RoundToIntegral is Quantize at
// exponent zero.
func FuzzQuantize(f *testing.F) {
	for _, seed := range []struct {
		s    string
		k    int16
		mode uint8
	}{{"2.5", 0, 0}, {"-2.5", 0, 1}, {"1.2345", -2, 2}, {"-0.005", -2, 5}, {"123", 2, 6}, {"9.995", -2, 4}, {"0.000", 3, 0}} {
		f.Add(seed.s, seed.k, seed.mode)
	}
	f.Fuzz(func(t *testing.T, s string, k16 int16, modeByte uint8) {
		if !scanDecimalShape(s) || len(s) > 200 {
			return
		}
		k := int32(k16 % 400)
		x, err := decimal.Parse(s)
		requireFuzzRepresentation(t, x)
		exact, _ := shapeRat(s)
		if err != nil || exact == nil {
			t.Fatalf("shape-accepted %q: %v", s, err)
		}
		if gap := int(x.Exponent()) - int(k); gap > 20000 || gap < -20000 {
			return // padding work would be gap-sized; the budgeted forms own that
		}
		mode := decimal.RoundingMode(modeByte % 7)
		q, cond, err := x.Quantize(k, mode)
		requireFuzzRepresentation(t, q)
		if err != nil || q.Exponent() != k {
			t.Fatalf("Quantize(%q, %d, %v) = %v at exponent %d, %v", s, k, mode, q, q.Exponent(), err)
		}
		qv, _ := new(big.Rat).SetString(q.String())
		side := qv.Cmp(exact)
		unit := new(big.Rat).SetInt64(1)
		for range max(k, -k) {
			if k > 0 {
				unit.Mul(unit, big.NewRat(10, 1))
			} else {
				unit.Quo(unit, big.NewRat(10, 1))
			}
		}
		if mode == decimal.TiesToEven || mode == decimal.TiesAwayFromZero || mode == decimal.TiesTowardZero {
			scaled := new(big.Rat).Quo(new(big.Rat).Abs(exact), unit)
			floor, rem := new(big.Int).QuoRem(scaled.Num(), scaled.Denom(), new(big.Int))
			if new(big.Int).Lsh(rem, 1).Cmp(scaled.Denom()) == 0 {
				if mode == decimal.TiesAwayFromZero || mode == decimal.TiesToEven && floor.Bit(0) == 1 {
					floor.Add(floor, big.NewInt(1))
				}
				if exact.Sign() < 0 {
					floor.Neg(floor)
				}
				want := new(big.Rat).Mul(new(big.Rat).SetInt(floor), unit)
				if qv.Cmp(want) != 0 {
					t.Fatalf("tie Quantize(%q, %d, %v) = %v, want %v", s, k, mode, q, want)
				}
			}
		}
		if (side != 0) != (cond&decimal.Inexact != 0) || side != cond.Direction() ||
			new(big.Rat).Abs(new(big.Rat).Sub(qv, exact)).Cmp(unit) >= 0 {
			t.Fatalf("Quantize(%q, %d, %v) = %v %v; exact %s", s, k, mode, q, cond, exact.RatString())
		}
		lo, _, _ := x.Quantize(k, decimal.TowardNegativeInfinity)
		requireFuzzRepresentation(t, lo)
		hi, _, _ := x.Quantize(k, decimal.TowardPositiveInfinity)
		requireFuzzRepresentation(t, hi)
		if q.Compare(lo) < 0 || q.Compare(hi) > 0 {
			t.Fatalf("Quantize(%q, %d, %v) = %v outside [%v, %v]", s, k, mode, q, lo, hi)
		}
		{
			again, c, err := q.Quantize(k, decimal.Exact)
			requireFuzzRepresentation(t, again)
			if err != nil || c != 0 || again.String() != q.String() {
				t.Fatalf("Quantize(%v, %d, Exact) = %v %v %v, want a fixed point", q, k, again, c, err)
			}
		}
		if k == 0 {
			ri, rc, err := x.RoundToIntegral(mode)
			requireFuzzRepresentation(t, ri)
			if err != nil || ri.String() != q.String() || rc != cond {
				t.Fatalf("RoundToIntegral(%q, %v) = %v %v %v, Quantize gave %v %v", s, mode, ri, rc, err, q, cond)
			}
		}
	})
}

// FuzzJSON is the marshaling target: UnmarshalJSON
// accepts only raw JSON numbers (and quoted numbers) that encoding/json
// accepts as tokens, never panics, and an accepted value marshals to valid
// JSON that unmarshals back to the same cohort.
func FuzzJSON(f *testing.F) {
	for _, seed := range []string{`1.25`, `"1.25"`, `-0.00`, `1e+3`, `null`, `"1E-3"`, `01`, `1.`, `"NaN"`, `[1]`, `1_000`} {
		f.Add([]byte(seed))
	}
	f.Fuzz(func(t *testing.T, raw []byte) {
		if len(raw) > 1024 {
			return
		}
		var d decimal.Decimal
		requireFuzzRepresentation(t, d)
		{
			err := d.UnmarshalJSON(raw)
			requireFuzzRepresentation(t, d)
			if err != nil {
				return
			}
		}
		if trimmed := bytes.TrimSpace(raw); !json.Valid(trimmed) {
			t.Fatalf("UnmarshalJSON accepted %q, which is not valid JSON", raw)
		}
		out, err := d.MarshalJSON()
		if err != nil || !json.Valid(out) {
			t.Fatalf("MarshalJSON(%v) = %q, %v", d, out, err)
		}
		var back decimal.Decimal
		requireFuzzRepresentation(t, back)
		{
			err := back.UnmarshalJSON(out)
			requireFuzzRepresentation(t, back)
			if err != nil || back.String() != d.String() {
				t.Fatalf("JSON round trip of %q: %q -> %v, %v", raw, out, back, err)
			}
		}
	})
}

// fuzzInventory reads the package's fuzz targets and TestRegression tests
// from every _test.go file, with the string literals each regression test
// contains.
func fuzzInventory(t *testing.T) (targets map[string]bool, regressions map[string][]string) {
	t.Helper()
	paths, err := filepath.Glob("*_test.go")
	if err != nil {
		t.Fatal(err)
	}
	targets, regressions = map[string]bool{}, map[string][]string{}
	for _, path := range paths {
		file, err := parser.ParseFile(token.NewFileSet(), path, nil, 0)
		if err != nil {
			t.Fatal(err)
		}
		inventoryDecls(file, targets, regressions)
	}
	return targets, regressions
}

func inventoryDecls(file *ast.File, targets map[string]bool, regressions map[string][]string) {
	for _, decl := range file.Decls {
		fn, ok := decl.(*ast.FuncDecl)
		if !ok || fn.Recv != nil {
			continue
		}
		name := fn.Name.Name
		switch {
		case strings.HasPrefix(name, "Fuzz"):
			targets[name] = true
		case strings.HasPrefix(name, "TestRegression"):
			ast.Inspect(fn, func(n ast.Node) bool {
				if lit, ok := n.(*ast.BasicLit); ok && lit.Kind == token.STRING {
					if s, err := strconv.Unquote(lit.Value); err == nil {
						regressions[name] = append(regressions[name], s)
					}
				}
				return true
			})
		}
	}
}

var engineCrasherName = regexp.MustCompile(`^[0-9a-f]{16}$`)

// TestFuzzCorpusPromotion enforces the crasher-promotion contract
// (testdata/fuzz/README.md): every corpus directory names a fuzz target of
// the package; every file there is a native "go test fuzz v1" entry; a file
// the fuzzing engine wrote (a 16-hex-digit name) is an unpromoted crasher
// and fails until it is renamed crasher-<name> and a TestRegression test
// runs it; every crasher- file has such a test, and every TestRegression
// test names a committed crasher. Every fuzz target of the package is also
// in the Makefile's FUZZ_TARGETS, so make fuzz-smoke fuzzes it.
func TestFuzzCorpusPromotion(t *testing.T) {
	targets, regressions := fuzzInventory(t)
	if len(targets) < 10 {
		t.Fatalf("found only %d fuzz targets", len(targets))
	}
	for _, msg := range fuzzCorpusViolations(t, "testdata/fuzz", targets, regressions) {
		t.Error(msg)
	}
	makefile, err := os.ReadFile("Makefile")
	if err != nil {
		t.Fatal(err)
	}
	var listed []string
	for line := range strings.SplitSeq(string(makefile), "\n") {
		if rest, ok := strings.CutPrefix(line, "FUZZ_TARGETS := "); ok {
			listed = strings.Fields(rest)
		}
	}
	for target := range targets {
		if !slices.Contains(listed, target) {
			t.Errorf("fuzz target %s is not in the Makefile's FUZZ_TARGETS", target)
		}
	}
	for _, target := range listed {
		if !targets[target] {
			t.Errorf("FUZZ_TARGETS lists %s, which the package does not define", target)
		}
	}
}

// fuzzCorpusViolations checks a corpus tree against the promotion contract.
func fuzzCorpusViolations(t *testing.T, root string, targets map[string]bool, regressions map[string][]string) []string {
	t.Helper()
	var msgs []string
	crashers := map[string]bool{}
	dirs, err := os.ReadDir(root)
	if err != nil {
		t.Fatal(err)
	}
	for _, dir := range dirs {
		if !dir.IsDir() {
			continue
		}
		if !targets[dir.Name()] {
			msgs = append(msgs, fmt.Sprintf("corpus directory %s names no fuzz target", dir.Name()))
			continue
		}
		files, err := os.ReadDir(filepath.Join(root, dir.Name()))
		if err != nil {
			t.Fatal(err)
		}
		for _, f := range files {
			path := filepath.Join(root, dir.Name(), f.Name())
			data, err := os.ReadFile(path)
			if err != nil {
				t.Fatal(err)
			}
			switch {
			case !bytes.HasPrefix(data, []byte("go test fuzz v1\n")):
				msgs = append(msgs, fmt.Sprintf("%s is not a native fuzz corpus entry", path))
			case engineCrasherName.MatchString(f.Name()):
				msgs = append(msgs, fmt.Sprintf("%s is an unpromoted crasher: rename it crasher-%s and add a TestRegression test (testdata/fuzz/README.md)", path, f.Name()))
			case strings.HasPrefix(f.Name(), "crasher-"):
				crashers[dir.Name()+"/"+f.Name()] = true
			}
		}
	}
	named := map[string]bool{}
	for test, lits := range regressions {
		found := false
		for _, lit := range lits {
			if crashers[lit] {
				named[lit], found = true, true
			}
		}
		if !found {
			msgs = append(msgs, fmt.Sprintf("%s names no committed crasher (want a \"<Target>/crasher-<id>\" literal)", test))
		}
	}
	for c := range crashers {
		if !named[c] {
			msgs = append(msgs, fmt.Sprintf("crasher %s has no TestRegression test", c))
		}
	}
	slices.Sort(msgs)
	return msgs
}

// TestFuzzCorpusPromotionControl is the contract's failing control: a
// synthetic corpus holding an engine-named crasher, a crasher without a
// regression test, a non-corpus file and a directory for no target is
// refused on each count, and a promoted crasher with its test is accepted.
func TestFuzzCorpusPromotionControl(t *testing.T) {
	root := t.TempDir()
	write := func(path, content string) {
		t.Helper()
		if err := os.MkdirAll(filepath.Dir(filepath.Join(root, path)), 0o755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(filepath.Join(root, path), []byte(content), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	entry := "go test fuzz v1\nstring(\"1\")\n"
	write("FuzzA/seed-01", entry)
	write("FuzzA/crasher-0123456789abcdef", entry)
	targets := map[string]bool{"FuzzA": true}
	good := map[string][]string{"TestRegressionA": {"FuzzA/crasher-0123456789abcdef"}}
	if msgs := fuzzCorpusViolations(t, root, targets, good); len(msgs) != 0 {
		t.Fatalf("promoted corpus refused: %v", msgs)
	}
	write("FuzzA/fedcba9876543210", entry)
	write("FuzzA/crasher-1111111111111111", entry)
	write("FuzzA/notes", "free text\n")
	write("FuzzGone/seed-01", entry)
	stale := map[string][]string{"TestRegressionA": {"FuzzA/crasher-0123456789abcdef"}, "TestRegressionB": {"FuzzA/crasher-2222222222222222"}}
	msgs := strings.Join(fuzzCorpusViolations(t, root, targets, stale), "\n")
	for _, want := range []string{"unpromoted crasher", "crasher FuzzA/crasher-1111111111111111 has no TestRegression", "not a native fuzz corpus entry", "names no fuzz target", "TestRegressionB names no committed crasher"} {
		if !strings.Contains(msgs, want) {
			t.Errorf("violation %q not reported in:\n%s", want, msgs)
		}
	}
}

// TestFuzzShapeAcceptsFractionalSeeds checks that the shape filter accepts
// fractional seeds: independent grammar witnesses include every fractional arithmetic and
// quantize seed, and explicit half-way values must reach the oracle.
func TestFuzzShapeAcceptsFractionalSeeds(t *testing.T) {
	for _, s := range []string{"2.5", "-2.5", "1.2345", "-0.005", "123", "9.995", "0.000", "1.25", "2.50", "-0.001", "0.001", "-7.5", "+1.20e-10000", "1E+10000"} {
		if !scanDecimalShape(s) {
			t.Errorf("valid grammar/seed %q rejected", s)
		}
	}
	for _, s := range []string{"", "+", ".5", "1.", "1..2", "1.2.3", "1e", "1e+", "1e10001", "1e-10001", " 1.2", "1.2 ", "1_0.2", "NaN"} {
		if scanDecimalShape(s) {
			t.Errorf("invalid subset grammar %q accepted", s)
		}
	}
	ties := 0
	for _, s := range []string{"2.5", "-2.5", "7.5", "-7.5"} {
		if !scanDecimalShape(s) {
			continue
		}
		r, ok := new(big.Rat).SetString(s)
		if !ok {
			t.Fatal(s)
		}
		_, rem := new(big.Int).QuoRem(r.Num(), r.Denom(), new(big.Int))
		if new(big.Int).Lsh(new(big.Int).Abs(rem), 1).Cmp(r.Denom()) == 0 {
			ties++
		}
	}
	if ties != 4 {
		t.Fatalf("fractional tie coverage %d, want4", ties)
	}
}
