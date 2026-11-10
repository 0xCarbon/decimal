// SPDX-License-Identifier: Apache-2.0

// Incumbent rows for the F1–F8 families. Every row runs on the portfolio's
// committed-seed corpus and must match the same independent math/big oracle
// as the decimal row before it is timed. Matched accuracy for incumbents:
//
//   - every row: every value equals the oracle's value (math/big.Rat);
//   - F4 display rows: the text equals the oracle's text byte for byte;
//   - F7 JSON and F8 wire rows: the value round-trips exactly; an emitter
//     that differs only in presentation (JSON string quotes, dropped
//     trailing zeros) is timed and labeled "value-matched" in the table.
//
// A row that fails its check is never timed and appears in the accuracy
// table as EXCLUDED with the first mismatch. Each timed loop calls the
// incumbent's methods directly, as the decimal rows do.
//
// Timed-work parity: every row's timed loop does the same class of work as
// the matching decimal row, and every String conversion and accuracy check
// runs before timing.
package incumbents

import (
	"database/sql"
	"errors"
	"fmt"
	"math/big"
	"sort"
	"strconv"
	"strings"
	"testing"

	"github.com/cockroachdb/apd/v3"
	eric "github.com/ericlagergren/decimal"
	gv "github.com/govalues/decimal"
	ss "github.com/shopspring/decimal"
)

type incumbentRow struct {
	family, lib, variant string
	label                string // matched-accuracy note shown in the table
	check                func() error
	bench                func(b *testing.B)
	err                  error // set by the check; non-nil excludes the row
}

var (
	incumbentRows []*incumbentRow
	sinkAny       any
	sinkSS        ss.Decimal
	sinkGV        gv.Decimal
	sinkAPD       apd.Decimal
	sinkEric      *eric.Big
)

func addRow(family, lib, variant, label string, check func() error, bench func(b *testing.B)) {
	incumbentRows = append(incumbentRows, &incumbentRow{family: family, lib: lib, variant: variant, label: label, check: check, bench: bench})
}

// excluded records an incumbent that has no API for a variant.
func excluded(family, lib, variant, reason string) {
	addRow(family, lib, variant, "", func() error { return errors.New(reason) }, nil)
}

var checked = false

func checkRows() {
	if checked {
		return
	}
	checked = true
	for _, r := range incumbentRows {
		func() {
			defer func() {
				if p := recover(); p != nil {
					r.err = fmt.Errorf("panic: %v", p)
				}
			}()
			r.err = r.check()
		}()
	}
}

func runIncumbents(b *testing.B, family string) {
	checkRows()
	for _, r := range incumbentRows {
		if r.family != family || r.err != nil {
			continue
		}
		b.Run(r.lib+"/"+r.variant, func(b *testing.B) {
			b.ReportAllocs()
			r.bench(b)
		})
	}
}

// ratText is the oracle view of any library's decimal text.
func ratText(s string) (*big.Rat, error) {
	r, ok := new(big.Rat).SetString(strings.Trim(s, `"`))
	if !ok {
		return nil, fmt.Errorf("not a number: %q", s)
	}
	return r, nil
}

func sameValue(got string, want *big.Rat) error {
	r, err := ratText(got)
	if err != nil {
		return err
	}
	if r.Cmp(want) != 0 {
		return fmt.Errorf("got %s, oracle %s", got, want.RatString())
	}
	return nil
}

func mustRat(s string) *big.Rat {
	r, err := ratText(s)
	if err != nil {
		panic(err)
	}
	return r
}

func eachIndex(n int, f func(i int) error) error {
	for i := range n {
		if err := f(i); err != nil {
			return fmt.Errorf("entry %d: %w", i, err)
		}
	}
	return nil
}

// Contexts: apd and ericlagergren need a precision; 50 digits keeps every
// exact row exact (the widest exact result is a 38-digit product).
var (
	apdExact    = apd.BaseContext.WithPrecision(50)
	apdHalfUp   = func() *apd.Context { c := apd.BaseContext.WithPrecision(50); c.Rounding = apd.RoundHalfUp; return c }()
	apdHalfEven = func() *apd.Context { c := apd.BaseContext.WithPrecision(50); c.Rounding = apd.RoundHalfEven; return c }()
	apdSci3     = func() *apd.Context { c := apd.BaseContext.WithPrecision(3); c.Rounding = apd.RoundHalfEven; return c }()
	ericExact   = eric.Context{Precision: 50, RoundingMode: eric.ToNearestEven}
	ericHalfUp  = eric.Context{Precision: 50, RoundingMode: eric.ToNearestAway}
)

func newEric(ctx eric.Context) *eric.Big {
	z := new(eric.Big)
	z.Context = ctx
	return z
}

func ssParse(s string) (ss.Decimal, error) { return ss.NewFromString(s) }
func gvParse(s string) (gv.Decimal, error) { return gv.Parse(s) }
func apdParse(s string) (apd.Decimal, error) {
	var d apd.Decimal
	_, _, err := d.SetString(s)
	return d, err
}
func ericParse(ctx eric.Context) func(string) (*eric.Big, error) {
	return func(s string) (*eric.Big, error) {
		z := newEric(ctx)
		if _, ok := z.SetString(s); !ok {
			return nil, fmt.Errorf("SetString(%q) failed", s)
		}
		return z, nil
	}
}

func parseEach[T any](inputs []string, parse func(string) (T, error)) ([]T, error) {
	out := make([]T, len(inputs))
	for i, s := range inputs {
		var err error
		if out[i], err = parse(s); err != nil {
			return nil, fmt.Errorf("parse %q: %w", s, err)
		}
	}
	return out, nil
}

// ---------------------------------------------------------------- F1 Parse

func init() {
	for _, variant := range portfolioFamilyVariants["F1Parse"] {
		corpus := portfolioF1Inputs[variant]
		want := make([]*big.Rat, len(corpus))
		for i, s := range corpus {
			want[i] = mustRat(s)
		}
		n := len(corpus)
		addRow("F1Parse", "shopspring", variant, "", func() error {
			return eachIndex(n, func(i int) error {
				d, err := ss.NewFromString(corpus[i])
				if err != nil {
					return err
				}
				return sameValue(d.String(), want[i])
			})
		}, func(b *testing.B) {
			i := 0
			for b.Loop() {
				var err error
				if sinkSS, err = ss.NewFromString(corpus[i]); err != nil {
					b.Fatal(err)
				}
				if i++; i == n {
					i = 0
				}
			}
		})
		addRow("F1Parse", "apd", variant, "", func() error {
			return eachIndex(n, func(i int) error {
				d, err := apdParse(corpus[i])
				if err != nil {
					return err
				}
				return sameValue(d.String(), want[i])
			})
		}, func(b *testing.B) {
			i := 0
			for b.Loop() {
				if _, _, err := sinkAPD.SetString(corpus[i]); err != nil {
					b.Fatal(err)
				}
				if i++; i == n {
					i = 0
				}
			}
		})
		addRow("F1Parse", "ericlagergren", variant, "", func() error {
			return eachIndex(n, func(i int) error {
				z, err := ericParse(ericExact)(corpus[i])
				if err != nil {
					return err
				}
				return sameValue(z.String(), want[i])
			})
		}, func(b *testing.B) {
			z := newEric(ericExact)
			i := 0
			for b.Loop() {
				if _, ok := z.SetString(corpus[i]); !ok {
					b.Fatal("SetString")
				}
				if i++; i == n {
					i = 0
				}
			}
			sinkEric = z
		})
		addRow("F1Parse", "govalues", variant, "", func() error {
			return eachIndex(n, func(i int) error {
				d, err := gv.Parse(corpus[i])
				if err != nil {
					return err
				}
				return sameValue(d.String(), want[i])
			})
		}, func(b *testing.B) {
			i := 0
			for b.Loop() {
				var err error
				if sinkGV, err = gv.Parse(corpus[i]); err != nil {
					b.Fatal(err)
				}
				if i++; i == n {
					i = 0
				}
			}
		})
	}
}

func BenchmarkF1Parse(b *testing.B) { decimalF1Parse(b); runIncumbents(b, "F1Parse") }

// ------------------------------------------------------------ F2 Aggregate

func init() {
	inputs := portfolioF2Inputs
	prefix := make([]*big.Rat, len(inputs))
	sum := new(big.Rat)
	for i, s := range inputs {
		sum.Add(sum, mustRat(s))
		prefix[i] = new(big.Rat).Set(sum)
	}
	const variant = "mixed1000"
	addRow("F2Aggregate", "shopspring", variant, "", func() error {
		values, err := parseEach(inputs, ssParse)
		if err != nil {
			return err
		}
		acc := ss.Zero
		return eachIndex(len(values), func(i int) error { acc = acc.Add(values[i]); return sameValue(acc.String(), prefix[i]) })
	}, func(b *testing.B) {
		values, _ := parseEach(inputs, ssParse)
		for b.Loop() {
			acc := ss.Zero
			for _, v := range values {
				acc = acc.Add(v)
			}
			sinkSS = acc
		}
	})
	addRow("F2Aggregate", "apd", variant, "in-place accumulation (d = d + x)", func() error {
		values, err := parseEach(inputs, apdParse)
		if err != nil {
			return err
		}
		var acc apd.Decimal
		return eachIndex(len(values), func(i int) error {
			if _, err := apdExact.Add(&acc, &acc, &values[i]); err != nil {
				return err
			}
			return sameValue(acc.String(), prefix[i])
		})
	}, func(b *testing.B) {
		values, _ := parseEach(inputs, apdParse)
		for b.Loop() {
			var acc apd.Decimal
			for i := range values {
				if _, err := apdExact.Add(&acc, &acc, &values[i]); err != nil {
					b.Fatal(err)
				}
			}
			sinkAPD = acc
		}
	})
	addRow("F2Aggregate", "ericlagergren", variant, "in-place accumulation (z = z + x)", func() error {
		values, err := parseEach(inputs, ericParse(ericExact))
		if err != nil {
			return err
		}
		acc := newEric(ericExact)
		return eachIndex(len(values), func(i int) error { acc.Add(acc, values[i]); return sameValue(acc.String(), prefix[i]) })
	}, func(b *testing.B) {
		values, _ := parseEach(inputs, ericParse(ericExact))
		for b.Loop() {
			acc := newEric(ericExact)
			for _, v := range values {
				acc.Add(acc, v)
			}
			sinkEric = acc
		}
	})
	addRow("F2Aggregate", "govalues", variant, "", func() error {
		values, err := parseEach(inputs, gvParse)
		if err != nil {
			return err
		}
		var acc gv.Decimal
		return eachIndex(len(values), func(i int) error {
			if acc, err = acc.Add(values[i]); err != nil {
				return err
			}
			return sameValue(acc.String(), prefix[i])
		})
	}, func(b *testing.B) {
		values, _ := parseEach(inputs, gvParse)
		for b.Loop() {
			var acc gv.Decimal
			for _, v := range values {
				var err error
				if acc, err = acc.Add(v); err != nil {
					b.Fatal(err)
				}
			}
			sinkGV = acc
		}
	})
}

func BenchmarkF2Aggregate(b *testing.B) { decimalF2Aggregate(b); runIncumbents(b, "F2Aggregate") }

// ------------------------------------------------------------ F3 MoneyLoop

// f3Oracle returns the per-line rounded amounts and the subtotal, fee and
// net of the money loop, from math/big alone (f3RoundCents, half away).
func f3Oracle(prices, qtys []string) (lines []*big.Rat, subtotal, fee, net *big.Rat) {
	subtotal = new(big.Rat)
	for i := range prices {
		rounded, _ := f3RoundCents(new(big.Rat).Mul(mustRat(prices[i]), mustRat(qtys[i])), true)
		lines = append(lines, rounded)
		subtotal.Add(subtotal, rounded)
	}
	fee, _ = f3RoundCents(new(big.Rat).Mul(subtotal, mustRat("0.0029")), true)
	return lines, subtotal, fee, new(big.Rat).Sub(subtotal, fee)
}

func init() {
	prices, qtys := f3MoneyLoopInputs()
	lines, subtotal, fee, net := f3Oracle(prices, qtys)
	const variant = "price-qty-round-fee"
	checkTotals := func(gotLines []string, s, f, n string) error {
		for i, l := range gotLines {
			if err := sameValue(l, lines[i]); err != nil {
				return fmt.Errorf("line %d: %w", i, err)
			}
		}
		for _, c := range []struct {
			got  string
			want *big.Rat
		}{{s, subtotal}, {f, fee}, {n, net}} {
			if err := sameValue(c.got, c.want); err != nil {
				return err
			}
		}
		return nil
	}

	ssLoop := func(p, q []ss.Decimal, rate ss.Decimal, observe func(ss.Decimal)) (ss.Decimal, ss.Decimal, ss.Decimal) {
		sub := ss.Zero
		for i := range p {
			rounded := p[i].Mul(q[i]).Round(2)
			if observe != nil {
				observe(rounded)
			}
			sub = sub.Add(rounded)
		}
		f := sub.Mul(rate).Round(2)
		return sub, f, sub.Sub(f)
	}
	addRow("F3MoneyLoop", "shopspring", variant, "Round(2) is half away from zero", func() error {
		p, err := parseEach(prices, ssParse)
		if err != nil {
			return err
		}
		q, _ := parseEach(qtys, ssParse)
		var got []string
		s, f, n := ssLoop(p, q, ss.RequireFromString("0.0029"), func(d ss.Decimal) { got = append(got, d.String()) })
		return checkTotals(got, s.String(), f.String(), n.String())
	}, func(b *testing.B) {
		p, _ := parseEach(prices, ssParse)
		q, _ := parseEach(qtys, ssParse)
		rate := ss.RequireFromString("0.0029")
		for b.Loop() {
			_, _, sinkSS = ssLoop(p, q, rate, nil)
		}
	})

	apdLoop := func(p, q []apd.Decimal, rate *apd.Decimal, observe func(*apd.Decimal)) (sub, f, n apd.Decimal, err error) {
		var product, rounded, feeRaw apd.Decimal
		for i := range p {
			if _, err = apdHalfUp.Mul(&product, &p[i], &q[i]); err != nil {
				return
			}
			if _, err = apdHalfUp.Quantize(&rounded, &product, -2); err != nil {
				return
			}
			if observe != nil {
				observe(&rounded)
			}
			if _, err = apdHalfUp.Add(&sub, &sub, &rounded); err != nil {
				return
			}
		}
		if _, err = apdHalfUp.Mul(&feeRaw, &sub, rate); err != nil {
			return
		}
		if _, err = apdHalfUp.Quantize(&f, &feeRaw, -2); err != nil {
			return
		}
		_, err = apdHalfUp.Sub(&n, &sub, &f)
		return
	}
	addRow("F3MoneyLoop", "apd", variant, "Quantize(-2) under RoundHalfUp (half away from zero)", func() error {
		p, err := parseEach(prices, apdParse)
		if err != nil {
			return err
		}
		q, _ := parseEach(qtys, apdParse)
		rate, _ := apdParse("0.0029")
		var got []string
		s, f, n, err := apdLoop(p, q, &rate, func(d *apd.Decimal) { got = append(got, d.String()) })
		if err != nil {
			return err
		}
		return checkTotals(got, s.String(), f.String(), n.String())
	}, func(b *testing.B) {
		p, _ := parseEach(prices, apdParse)
		q, _ := parseEach(qtys, apdParse)
		rate, _ := apdParse("0.0029")
		for b.Loop() {
			_, _, n, err := apdLoop(p, q, &rate, nil)
			if err != nil {
				b.Fatal(err)
			}
			sinkAPD = n
		}
	})

	ericLoop := func(p, q []*eric.Big, rate *eric.Big, observe func(*eric.Big)) (sub, f, n *eric.Big) {
		sub, f, n = newEric(ericHalfUp), newEric(ericHalfUp), newEric(ericHalfUp)
		rounded := newEric(ericHalfUp)
		for i := range p {
			rounded.Mul(p[i], q[i]).Quantize(2)
			if observe != nil {
				observe(rounded)
			}
			sub.Add(sub, rounded)
		}
		f.Mul(sub, rate).Quantize(2)
		n.Sub(sub, f)
		return sub, f, n
	}
	addRow("F3MoneyLoop", "ericlagergren", variant, "Quantize(2) under ToNearestAway", func() error {
		p, err := parseEach(prices, ericParse(ericHalfUp))
		if err != nil {
			return err
		}
		q, _ := parseEach(qtys, ericParse(ericHalfUp))
		rate, _ := ericParse(ericHalfUp)("0.0029")
		var got []string
		s, f, n := ericLoop(p, q, rate, func(d *eric.Big) { got = append(got, d.String()) })
		return checkTotals(got, s.String(), f.String(), n.String())
	}, func(b *testing.B) {
		p, _ := parseEach(prices, ericParse(ericHalfUp))
		q, _ := parseEach(qtys, ericParse(ericHalfUp))
		rate, _ := ericParse(ericHalfUp)("0.0029")
		for b.Loop() {
			_, _, sinkEric = ericLoop(p, q, rate, nil)
		}
	})
	excluded("F3MoneyLoop", "govalues", variant, "no half-away-from-zero rounding (Round is half to even; the loop's cent rounding is half away)")
}

func BenchmarkF3MoneyLoop(b *testing.B) { decimalF3MoneyLoop(b); runIncumbents(b, "F3MoneyLoop") }

// -------------------------------------------------------------- F4 Format

func init() {
	for _, variant := range portfolioFamilyVariants["F4Format"] {
		corpus := portfolioF4Inputs[variant]
		want := make([]string, len(corpus))
		for i, s := range corpus {
			switch variant {
			case "plain":
				want[i] = s
				if v, ok := new(big.Int).SetString(s, 10); ok {
					want[i] = v.String()
				}
			case "fixed2dp":
				want[i] = f4ExpectedFixed2dp(s)
			case "scientific":
				want[i] = f4ExpectedScientific3(s)
			}
		}
		n := len(corpus)
		textCheck := func(format func(i int) (string, error)) func() error {
			return func() error {
				return eachIndex(n, func(i int) error {
					got, err := format(i)
					if err != nil {
						return err
					}
					if got != want[i] {
						return fmt.Errorf("input %q: got %q, oracle %q", corpus[i], got, want[i])
					}
					return nil
				})
			}
		}
		ssValues, _ := parseEach(corpus, ssParse)
		apdValues, _ := parseEach(corpus, apdParse)
		ericValues, _ := parseEach(corpus, ericParse(ericExact))
		gvValues, gvErr := parseEach(corpus, gvParse)
		var ssFormat func(i int) string
		switch variant {
		case "plain":
			ssFormat = func(i int) string { return ssValues[i].String() }
		case "fixed2dp":
			ssFormat = func(i int) string { return ssValues[i].StringFixedBank(2) }
		}
		if ssFormat != nil {
			addRow("F4Format", "shopspring", variant, "", textCheck(func(i int) (string, error) { return ssFormat(i), nil }), func(b *testing.B) {
				i := 0
				for b.Loop() {
					if variant == "plain" {
						sinkString = ssValues[i].String()
					} else {
						sinkString = ssValues[i].StringFixedBank(2)
					}
					if i++; i == n {
						i = 0
					}
				}
			})
		} else {
			excluded("F4Format", "shopspring", variant, "no scientific display with a significant-digit count")
		}
		apdFormat := func(i int, t *apd.Decimal) (string, error) {
			switch variant {
			case "fixed2dp":
				if _, err := apdHalfEven.Quantize(t, &apdValues[i], -2); err != nil {
					return "", err
				}
				return t.Text('f'), nil
			case "scientific":
				if _, err := apdSci3.Round(t, &apdValues[i]); err != nil {
					return "", err
				}
				return t.Text('E'), nil
			}
			return apdValues[i].Text('f'), nil
		}
		label := ""
		if variant != "plain" {
			label = "round (half even) then Text"
		}
		addRow("F4Format", "apd", variant, label, textCheck(func(i int) (string, error) { var t apd.Decimal; return apdFormat(i, &t) }), func(b *testing.B) {
			var t apd.Decimal
			i := 0
			for b.Loop() {
				var err error
				if sinkString, err = apdFormat(i, &t); err != nil {
					b.Fatal(err)
				}
				if i++; i == n {
					i = 0
				}
			}
		})
		switch variant {
		case "scientific":
			excluded("F4Format", "ericlagergren", variant, `fmt "%.3e" prints "9.12e0", not the oracle's "9.12E+0"`)
		default:
			ericFormat := func(i int, t *eric.Big) string {
				if variant == "fixed2dp" {
					return t.Copy(ericValues[i]).Quantize(2).String()
				}
				return ericValues[i].String()
			}
			label := ""
			if variant == "fixed2dp" {
				label = "Quantize(2) half even then String"
			}
			addRow("F4Format", "ericlagergren", variant, label, textCheck(func(i int) (string, error) { return ericFormat(i, newEric(ericExact)), nil }), func(b *testing.B) {
				t := newEric(ericExact)
				i := 0
				for b.Loop() {
					sinkString = ericFormat(i, t)
					if i++; i == n {
						i = 0
					}
				}
			})
		}
		switch {
		case variant == "scientific":
			excluded("F4Format", "govalues", variant, "no scientific display")
		case gvErr != nil:
			excluded("F4Format", "govalues", variant, gvErr.Error())
		default:
			gvFormat := func(i int) string {
				if variant == "fixed2dp" {
					return gvValues[i].Round(2).String()
				}
				return gvValues[i].String()
			}
			label := ""
			if variant == "fixed2dp" {
				label = "Round(2) half even then String"
			}
			addRow("F4Format", "govalues", variant, label, textCheck(func(i int) (string, error) { return gvFormat(i), nil }), func(b *testing.B) {
				i := 0
				for b.Loop() {
					sinkString = gvFormat(i)
					if i++; i == n {
						i = 0
					}
				}
			})
		}
	}
}

func BenchmarkF4Format(b *testing.B) { decimalF4Format(b); runIncumbents(b, "F4Format") }

// -------------------------------------------------------------- F5 MapKey

// f5Churn runs the in-tree string1024 recipe over any key function: insert
// every base under its key, then look up and delete every cohort member.
func f5Churn(n int, m map[string]int, base, cohort func(i int) string) error {
	for i := range n {
		m[base(i)] = i
	}
	for i := range n {
		key := cohort(i)
		if got, ok := m[key]; !ok || got != i {
			return fmt.Errorf("key %d mismatch: got %d, present %v", i, got, ok)
		}
		delete(m, key)
	}
	if len(m) != 0 {
		return fmt.Errorf("map retained %d entries", len(m))
	}
	return nil
}

func init() {
	pairs := portfolioF5Inputs
	n := len(pairs)
	bases, cohorts := make([]string, n), make([]string, n)
	for i, p := range pairs {
		bases[i], cohorts[i] = p.base, p.cohort
	}
	const variant = "string1024"
	// check: equal values give equal keys, the key's value is the input's,
	// and the churn recipe completes.
	keyCheck := func(base, cohort func(i int) string) func() error {
		return func() error {
			seen := map[string]bool{}
			if err := eachIndex(n, func(i int) error {
				k, c := base(i), cohort(i)
				if k != c {
					return fmt.Errorf("cohort key %q differs from %q", c, k)
				}
				if seen[k] {
					return fmt.Errorf("duplicate key %q", k)
				}
				seen[k] = true
				return sameValue(k, mustRat(bases[i]))
			}); err != nil {
				return err
			}
			return f5Churn(n, make(map[string]int, n), base, cohort)
		}
	}
	churnBench := func(base, cohort func(i int) string) func(b *testing.B) {
		return func(b *testing.B) {
			m := make(map[string]int, n)
			for b.Loop() {
				if err := f5Churn(n, m, base, cohort); err != nil {
					b.Fatal(err)
				}
			}
		}
	}
	{
		bv, _ := parseEach(bases, ssParse)
		cv, _ := parseEach(cohorts, ssParse)
		base := func(i int) string { return bv[i].String() }
		cohort := func(i int) string { return cv[i].String() }
		addRow("F5MapKey", "shopspring", variant, "String() drops trailing zeros", keyCheck(base, cohort), churnBench(base, cohort))
	}
	{
		bv, _ := parseEach(bases, apdParse)
		cv, _ := parseEach(cohorts, apdParse)
		var t apd.Decimal
		key := func(d *apd.Decimal) string { t.Reduce(d); return t.String() }
		base := func(i int) string { return key(&bv[i]) }
		cohort := func(i int) string { return key(&cv[i]) }
		addRow("F5MapKey", "apd", variant, "Reduce then String", keyCheck(base, cohort), churnBench(base, cohort))
	}
	{
		bv, _ := parseEach(bases, ericParse(ericExact))
		cv, _ := parseEach(cohorts, ericParse(ericExact))
		t := newEric(ericExact)
		base := func(i int) string { return t.Copy(bv[i]).Reduce().String() }
		cohort := func(i int) string { return t.Copy(cv[i]).Reduce().String() }
		addRow("F5MapKey", "ericlagergren", variant, "Copy, Reduce then String", keyCheck(base, cohort), churnBench(base, cohort))
	}
	{
		bv, _ := parseEach(bases, gvParse)
		cv, _ := parseEach(cohorts, gvParse)
		base := func(i int) string { return bv[i].Trim(0).String() }
		cohort := func(i int) string { return cv[i].Trim(0).String() }
		addRow("F5MapKey", "govalues", variant, "Trim(0) then String", keyCheck(base, cohort), churnBench(base, cohort))
	}
	for _, lib := range []string{"shopspring", "apd", "ericlagergren", "govalues"} {
		excluded("F5MapKey", lib, "hasher1024", "no hashing recipe (the variant times Decimal's Hasher)")
	}
}

func BenchmarkF5MapKey(b *testing.B) { decimalF5MapKey(b); runIncumbents(b, "F5MapKey") }

// --------------------------------------------------------- F6 TightArith

func init() {
	for _, variant := range portfolioFamilyVariants["F6TightArith"] {
		pair := portfolioF6Inputs[variant]
		x, y := mustRat(pair[0]), mustRat(pair[1])
		var want *big.Rat
		label := ""
		switch variant {
		case "add19":
			want = new(big.Rat).Add(x, y)
		case "mul19", "mulsmall":
			want = new(big.Rat).Mul(x, y)
		case "div2dp":
			want = mustRat(roundRatTiesToEven(new(big.Rat).Quo(x, y), 2))
		case "divby4":
			want = new(big.Rat).Quo(x, y)
		case "cmp19":
			want = big.NewRat(int64(x.Cmp(y)), 1)
		}
		cmpText := func(c int) string { return strconv.Itoa(c) }

		sx, _ := ss.NewFromString(pair[0])
		sy, _ := ss.NewFromString(pair[1])
		ssOp := func() string {
			switch variant {
			case "add19":
				sinkSS = sx.Add(sy)
			case "mul19", "mulsmall":
				sinkSS = sx.Mul(sy)
			case "div2dp":
				sinkSS = sx.DivRound(sy, 2)
			case "divby4":
				sinkSS = sx.Div(sy)
			case "cmp19":
				return cmpText(sx.Cmp(sy))
			}
			return sinkSS.String()
		}
		if variant == "div2dp" {
			label = "DivRound(2) is half away from zero; no tie in this quotient"
		}
		addRow("F6TightArith", "shopspring", variant, label, func() error { return sameValue(ssOp(), want) }, func(b *testing.B) {
			for b.Loop() {
				switch variant {
				case "add19":
					sinkSS = sx.Add(sy)
				case "mul19", "mulsmall":
					sinkSS = sx.Mul(sy)
				case "div2dp":
					sinkSS = sx.DivRound(sy, 2)
				case "divby4":
					sinkSS = sx.Div(sy)
				case "cmp19":
					sinkInt = sx.Cmp(sy)
				}
			}
		})

		ax, _ := apdParse(pair[0])
		ay, _ := apdParse(pair[1])
		apdOp := func(z *apd.Decimal) (string, error) {
			var err error
			switch variant {
			case "add19":
				_, err = apdExact.Add(z, &ax, &ay)
			case "mul19", "mulsmall":
				_, err = apdExact.Mul(z, &ax, &ay)
			case "div2dp":
				if _, err = apdHalfEven.Quo(z, &ax, &ay); err == nil {
					_, err = apdHalfEven.Quantize(z, z, -2)
				}
			case "divby4":
				_, err = apdExact.Quo(z, &ax, &ay)
			case "cmp19":
				return cmpText(ax.Cmp(&ay)), nil
			}
			return z.String(), err
		}
		label = ""
		if variant == "div2dp" {
			label = "Quo at 50 digits then Quantize(-2) half even"
		}
		addRow("F6TightArith", "apd", variant, label, func() error {
			var z apd.Decimal
			got, err := apdOp(&z)
			if err != nil {
				return err
			}
			return sameValue(got, want)
		}, func(b *testing.B) {
			var z apd.Decimal
			for b.Loop() {
				var err error
				switch variant {
				case "add19":
					_, err = apdExact.Add(&z, &ax, &ay)
				case "mul19", "mulsmall":
					_, err = apdExact.Mul(&z, &ax, &ay)
				case "div2dp":
					if _, err = apdHalfEven.Quo(&z, &ax, &ay); err == nil {
						_, err = apdHalfEven.Quantize(&z, &z, -2)
					}
				case "divby4":
					_, err = apdExact.Quo(&z, &ax, &ay)
				case "cmp19":
					sinkInt = ax.Cmp(&ay)
				}
				if err != nil {
					b.Fatal(err)
				}
			}
			sinkAPD = z
		})

		ex, _ := ericParse(ericExact)(pair[0])
		ey, _ := ericParse(ericExact)(pair[1])
		ericOp := func(z *eric.Big) string {
			switch variant {
			case "add19":
				z.Add(ex, ey)
			case "mul19", "mulsmall":
				z.Mul(ex, ey)
			case "div2dp":
				z.Quo(ex, ey).Quantize(2)
			case "divby4":
				z.Quo(ex, ey)
			case "cmp19":
				return cmpText(ex.Cmp(ey))
			}
			return z.String()
		}
		label = ""
		if variant == "div2dp" {
			label = "Quo at 50 digits then Quantize(2) half even"
		}
		addRow("F6TightArith", "ericlagergren", variant, label, func() error { return sameValue(ericOp(newEric(ericExact)), want) }, func(b *testing.B) {
			z := newEric(ericExact)
			for b.Loop() {
				switch variant {
				case "add19":
					z.Add(ex, ey)
				case "mul19", "mulsmall":
					z.Mul(ex, ey)
				case "div2dp":
					z.Quo(ex, ey).Quantize(2)
				case "divby4":
					z.Quo(ex, ey)
				case "cmp19":
					sinkInt = ex.Cmp(ey)
				}
			}
			sinkEric = z
		})

		gx, _ := gv.Parse(pair[0])
		gy, _ := gv.Parse(pair[1])
		gvOp := func() (string, error) {
			var err error
			switch variant {
			case "add19":
				sinkGV, err = gx.Add(gy)
			case "mul19", "mulsmall":
				sinkGV, err = gx.Mul(gy)
			case "div2dp":
				if sinkGV, err = gx.Quo(gy); err == nil {
					sinkGV = sinkGV.Round(2)
				}
			case "divby4":
				sinkGV, err = gx.Quo(gy)
			case "cmp19":
				return cmpText(gx.Cmp(gy)), nil
			}
			return sinkGV.String(), err
		}
		label = ""
		if variant == "div2dp" {
			label = "Quo (19 digits) then Round(2) half even"
		}
		addRow("F6TightArith", "govalues", variant, label, func() error {
			got, err := gvOp()
			if err != nil {
				return err
			}
			return sameValue(got, want)
		}, func(b *testing.B) {
			for b.Loop() {
				var err error
				switch variant {
				case "add19":
					sinkGV, err = gx.Add(gy)
				case "mul19", "mulsmall":
					sinkGV, err = gx.Mul(gy)
				case "div2dp":
					if sinkGV, err = gx.Quo(gy); err == nil {
						sinkGV = sinkGV.Round(2)
					}
				case "divby4":
					sinkGV, err = gx.Quo(gy)
				case "cmp19":
					sinkInt = gx.Cmp(gy)
				}
				if err != nil {
					b.Fatal(err)
				}
			}
		})
	}
}

func BenchmarkF6TightArith(b *testing.B) { decimalF6TightArith(b); runIncumbents(b, "F6TightArith") }

// ----------------------------------------------------------------- F7 JSON

func init() {
	values := f7JSONValues()
	for _, variant := range portfolioFamilyVariants["F7JSON"] {
		corpus := make([][]byte, len(values[variant]))
		want := make([]*big.Rat, len(corpus))
		for i, token := range values[variant] {
			corpus[i] = []byte(token)
			want[i] = mustRat(token)
		}
		n := len(corpus)
		roundTrip := func(unmarshal func([]byte) ([]byte, error)) func() error {
			return func() error {
				return eachIndex(n, func(i int) error {
					blob, err := unmarshal(corpus[i])
					if err != nil {
						return err
					}
					return sameValue(string(blob), want[i])
				})
			}
		}
		addRow("F7JSON", "shopspring", variant, "value-matched: MarshalJSON quotes and drops trailing zeros", roundTrip(func(tok []byte) ([]byte, error) {
			var d ss.Decimal
			if err := d.UnmarshalJSON(tok); err != nil {
				return nil, err
			}
			return d.MarshalJSON()
		}), func(b *testing.B) {
			i := 0
			for b.Loop() {
				var d ss.Decimal
				if err := d.UnmarshalJSON(corpus[i]); err != nil {
					b.Fatal(err)
				}
				blob, err := d.MarshalJSON()
				if err != nil {
					b.Fatal(err)
				}
				sinkInt = len(blob)
				if i++; i == n {
					i = 0
				}
			}
		})
		addRow("F7JSON", "govalues", variant, "value-matched: MarshalJSON emits a JSON string", roundTrip(func(tok []byte) ([]byte, error) {
			var d gv.Decimal
			if err := d.UnmarshalJSON(tok); err != nil {
				return nil, err
			}
			return d.MarshalJSON()
		}), func(b *testing.B) {
			i := 0
			for b.Loop() {
				var d gv.Decimal
				if err := d.UnmarshalJSON(corpus[i]); err != nil {
					b.Fatal(err)
				}
				blob, err := d.MarshalJSON()
				if err != nil {
					b.Fatal(err)
				}
				sinkInt = len(blob)
				if i++; i == n {
					i = 0
				}
			}
		})
		excluded("F7JSON", "apd", variant, "no MarshalJSON/UnmarshalJSON on Decimal (TextMarshaler only)")
		excluded("F7JSON", "ericlagergren", variant, "no MarshalJSON on Big (UnmarshalJSON and TextMarshaler only)")
	}
}

func BenchmarkF7JSON(b *testing.B) { decimalF7JSON(b); runIncumbents(b, "F7JSON") }

// ------------------------------------------------------------- F8 Database

var f8DB *sql.DB

func incumbentSQLConn() *sql.DB {
	if f8DB == nil {
		registerF8()
		var err error
		if f8DB, err = sql.Open("decimal-f8", ""); err != nil {
			panic(err)
		}
		f8DB.SetMaxIdleConns(1)
	}
	return f8DB
}

// f8Row adds one incumbent F8 row with timed-work parity. trip is the
// row's round trip: it binds entry i and scans the result into out, the
// work the decimal row times. The accuracy check runs trip over the corpus
// before timing and renders out through view, so the String conversion
// stays outside the timed closure.
// The timed loop, like the decimal row's, runs trip into a fresh T per
// iteration on a connection fetched before timing and keeps nothing.
func f8Row[T any](lib, variant, label string, n int, valid []bool, want []*big.Rat, trip func(db *sql.DB, i int, out *T) error, view func(out *T) (string, bool)) {
	addRow("F8Database", lib, variant, label, func() error {
		db := incumbentSQLConn()
		return eachIndex(n, func(i int) error {
			var out T
			if err := trip(db, i, &out); err != nil {
				return err
			}
			got, ok := view(&out)
			if variant == "null-roundtrip" && !valid[i] {
				if ok {
					return errors.New("NULL scanned as valid")
				}
				return nil
			}
			if !ok {
				return errors.New("valid value scanned as NULL")
			}
			return sameValue(got, want[i])
		})
	}, func(b *testing.B) {
		db := incumbentSQLConn()
		i := 0
		for b.Loop() {
			var out T
			if err := trip(db, i, &out); err != nil {
				b.Fatal(err)
			}
			if i++; i == n {
				i = 0
			}
		}
	})
}

func init() {
	entries := f4FormatInputs()["fixed2dp"]
	valid := f8NullPattern(len(entries))
	n := len(entries)
	want := make([]*big.Rat, n)
	for i, e := range entries {
		want[i] = mustRat(newF8Oracle(e).text)
	}
	{
		values, _ := parseEach(entries, ssParse)
		f8Row("shopspring", "valuer-scan", "value-matched: Value drops trailing zeros", n, valid, want,
			func(db *sql.DB, i int, out *ss.Decimal) error { return db.QueryRow("echo", values[i]).Scan(out) },
			func(out *ss.Decimal) (string, bool) { return out.String(), true })
		f8Row("shopspring", "null-roundtrip", "value-matched: Value drops trailing zeros", n, valid, want,
			func(db *sql.DB, i int, out *ss.NullDecimal) error {
				return db.QueryRow("echo", ss.NullDecimal{Decimal: values[i], Valid: valid[i]}).Scan(out)
			},
			func(out *ss.NullDecimal) (string, bool) { return out.Decimal.String(), out.Valid })
		excluded("F8Database", "shopspring", "sqldecimal-compose", "no Decompose/Compose")
	}
	{
		values, _ := parseEach(entries, apdParse)
		f8Row("apd", "valuer-scan", "", n, valid, want,
			func(db *sql.DB, i int, out *apd.Decimal) error { return db.QueryRow("echo", values[i]).Scan(out) },
			func(out *apd.Decimal) (string, bool) { return out.String(), true })
		f8Row("apd", "sqldecimal-compose", "binds *Decimal (Decompose) and scans through Compose", n, valid, want,
			func(db *sql.DB, i int, out *apd.Decimal) error { return db.QueryRow("echo", &values[i]).Scan(out) },
			func(out *apd.Decimal) (string, bool) { return out.String(), true })
		f8Row("apd", "null-roundtrip", "", n, valid, want,
			func(db *sql.DB, i int, out *apd.NullDecimal) error {
				return db.QueryRow("echo", apd.NullDecimal{Decimal: values[i], Valid: valid[i]}).Scan(out)
			},
			func(out *apd.NullDecimal) (string, bool) { return out.Decimal.String(), out.Valid })
	}
	{
		values, _ := parseEach(entries, ericParse(ericExact))
		excluded("F8Database", "ericlagergren", "valuer-scan", "no driver.Valuer or sql.Scanner")
		// The zero Big with the exact context is the same value as
		// newEric(ericExact).
		f8Row("ericlagergren", "sqldecimal-compose", "binds *Big (Decompose) and scans through Compose", n, valid, want,
			func(db *sql.DB, i int, out *eric.Big) error {
				out.Context = ericExact
				return db.QueryRow("echo", values[i]).Scan(out)
			},
			func(out *eric.Big) (string, bool) { return out.String(), true })
		excluded("F8Database", "ericlagergren", "null-roundtrip", "no NULL wrapper")
	}
	{
		values, _ := parseEach(entries, gvParse)
		f8Row("govalues", "valuer-scan", "", n, valid, want,
			func(db *sql.DB, i int, out *gv.Decimal) error { return db.QueryRow("echo", values[i]).Scan(out) },
			func(out *gv.Decimal) (string, bool) { return out.String(), true })
		f8Row("govalues", "null-roundtrip", "", n, valid, want,
			func(db *sql.DB, i int, out *gv.NullDecimal) error {
				return db.QueryRow("echo", gv.NullDecimal{Decimal: values[i], Valid: valid[i]}).Scan(out)
			},
			func(out *gv.NullDecimal) (string, bool) { return out.Decimal.String(), out.Valid })
		excluded("F8Database", "govalues", "sqldecimal-compose", "no Decompose/Compose")
	}
}

func BenchmarkF8Database(b *testing.B) { decimalF8Database(b); runIncumbents(b, "F8Database") }

// TestIncumbentMatchedAccuracy runs every incumbent row's check and prints
// the matched-accuracy table (go test -v shows it): matched rows are timed, EXCLUDED
// rows never are. It fails only if a check panics or the table is empty.
func TestIncumbentMatchedAccuracy(t *testing.T) {
	checkRows()
	rows := append([]*incumbentRow(nil), incumbentRows...)
	sort.SliceStable(rows, func(i, j int) bool { return rows[i].family < rows[j].family })
	matched := 0
	for _, r := range rows {
		status := "matched"
		if r.err != nil {
			status = "EXCLUDED: " + r.err.Error()
			if strings.HasPrefix(r.err.Error(), "panic") {
				t.Errorf("%s/%s/%s: %v", r.family, r.lib, r.variant, r.err)
			}
		} else {
			matched++
			if r.label != "" {
				status += " (" + r.label + ")"
			}
		}
		t.Logf("%-13s %-14s %-20s %s", r.family, r.lib, r.variant, status)
	}
	if matched == 0 {
		t.Fatal("no incumbent row matched")
	}
	t.Logf("%d of %d incumbent rows matched", matched, len(rows))
}
