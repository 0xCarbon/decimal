// SPDX-License-Identifier: Apache-2.0

package main

import (
	"fmt"
	"hash/maphash"
	"math/big"
	"math/rand/v2"

	"github.com/0xCarbon/decimal"
)

// The property-law suite: algebraic
// laws, monotonicity, idempotence and directed-rounding enclosure over the
// public API, on seeded random inputs, with the exact math/big value as the
// arbiter where a law is numeric. Each law takes its operations as function
// values so the negative controls can pass deliberately defective ones.

// lawOps are the operations the laws exercise. The tests pass the
// library's; the controls pass defective variants.
type lawOps struct {
	add      func(x, y decimal.Decimal) (decimal.Decimal, error)
	mul      func(x, y decimal.Decimal) (decimal.Decimal, error)
	addCtx   func(x, y decimal.Decimal, c decimal.Context) (decimal.Decimal, decimal.Conditions, error)
	quantize func(x decimal.Decimal, k int32, m decimal.RoundingMode) (decimal.Decimal, decimal.Conditions, error)
	toPrec   func(x decimal.Decimal, p uint32, m decimal.RoundingMode) (decimal.Decimal, decimal.Conditions, error)
	reduce   func(x decimal.Decimal) decimal.Decimal
	compare  func(x, y decimal.Decimal) int
	text     func(x decimal.Decimal) string
}

var libraryOps = lawOps{
	add:      decimal.Decimal.Add,
	mul:      decimal.Decimal.Mul,
	addCtx:   decimal.Decimal.AddWithContext,
	quantize: decimal.Decimal.Quantize,
	toPrec:   decimal.Decimal.RoundToPrecision,
	reduce:   decimal.Decimal.Reduce,
	compare:  decimal.Decimal.Compare,
	text:     decimal.Decimal.String,
}

// law is one property: it checks one generated case and describes a
// violation; the empty string is a pass.
type law struct {
	name  string
	check func(g *gen, o lawOps) string
}

func ratOfDec(d decimal.Decimal) *big.Rat { return ratOf(d.String()) }

// sameCohort compares value and stored exponent (text identity).
func sameCohort(x, y decimal.Decimal) bool { return x.String() == y.String() }

var laws = []law{
	{"add-commutes", func(g *gen, o lawOps) string {
		x, y := parse(g.decimal(-20, 20)), parse(g.decimal(-20, 20))
		a, err1 := o.add(x, y)
		b, err2 := o.add(y, x)
		if err1 != nil || err2 != nil || !sameCohort(a, b) {
			return fmt.Sprintf("%v+%v = %v but %v+%v = %v (%v, %v)", x, y, a, y, x, b, err1, err2)
		}
		return ""
	}},
	{"mul-commutes", func(g *gen, o lawOps) string {
		x, y := parse(g.decimal(-20, 20)), parse(g.decimal(-20, 20))
		a, err1 := o.mul(x, y)
		b, err2 := o.mul(y, x)
		if err1 != nil || err2 != nil || !sameCohort(a, b) {
			return fmt.Sprintf("%v*%v = %v but %v*%v = %v", x, y, a, y, x, b)
		}
		return ""
	}},
	{"exact-add-is-rational-sum-at-min-exponent", func(g *gen, o lawOps) string {
		x, y := parse(g.decimal(-20, 20)), parse(g.decimal(-20, 20))
		s, err := o.add(x, y)
		want := new(big.Rat).Add(ratOfDec(x), ratOfDec(y))
		if err != nil || ratOfDec(s).Cmp(want) != 0 || s.Exponent() != min(x.Exponent(), y.Exponent()) {
			return fmt.Sprintf("%v+%v = %v, want %s at exponent %d", x, y, s, want.RatString(), min(x.Exponent(), y.Exponent()))
		}
		return ""
	}},
	{"exact-mul-is-rational-product-at-exponent-sum", func(g *gen, o lawOps) string {
		x, y := parse(g.decimal(-20, 20)), parse(g.decimal(-20, 20))
		p, err := o.mul(x, y)
		want := mul(ratOfDec(x), ratOfDec(y))
		if err != nil || ratOfDec(p).Cmp(want) != 0 || p.Exponent() != x.Exponent()+y.Exponent() {
			return fmt.Sprintf("%v*%v = %v, want %s at exponent %d", x, y, p, want.RatString(), x.Exponent()+y.Exponent())
		}
		return ""
	}},
	{"add-associates", func(g *gen, o lawOps) string {
		x, y, z := parse(g.decimal(-20, 20)), parse(g.decimal(-20, 20)), parse(g.decimal(-20, 20))
		xy, _ := o.add(x, y)
		l, _ := o.add(xy, z)
		yz, _ := o.add(y, z)
		r, _ := o.add(x, yz)
		if !sameCohort(l, r) {
			return fmt.Sprintf("(%v+%v)+%v = %v but %v+(%v+%v) = %v", x, y, z, l, x, y, z, r)
		}
		return ""
	}},
	{"context-add-associates-when-exact", func(g *gen, o lawOps) string {
		// Exactness-conditioned associativity: when neither grouping
		// rounds, both give the exact sum.
		c := ctx(g.precision()+10, libModes[g.rng.IntN(int(modeCount)-1)])
		x, y, z := parse(g.decimal(-6, 6)), parse(g.decimal(-6, 6)), parse(g.decimal(-6, 6))
		xy, c1, _ := o.addCtx(x, y, c)
		l, c2, _ := o.addCtx(xy, z, c)
		yz, c3, _ := o.addCtx(y, z, c)
		r, c4, _ := o.addCtx(x, yz, c)
		if (c1|c2|c3|c4)&decimal.Inexact != 0 {
			return ""
		}
		if l.Compare(r) != 0 {
			return fmt.Sprintf("exact groupings of %v+%v+%v differ: %v and %v", x, y, z, l, r)
		}
		return ""
	}},
	{"rounding-is-monotone", func(g *gen, o lawOps) string {
		m := libModes[g.rng.IntN(int(modeCount)-1)]
		k := int32(g.target())
		x, y := parse(g.decimal(-15, 10)), parse(g.decimal(-15, 10))
		if ratOfDec(x).Cmp(ratOfDec(y)) > 0 {
			x, y = y, x
		}
		qx, _, err1 := o.quantize(x, k, m)
		qy, _, err2 := o.quantize(y, k, m)
		p := uint32(g.precision())
		px, _, err3 := o.toPrec(x, p, m)
		py, _, err4 := o.toPrec(y, p, m)
		if err1 != nil || err2 != nil || err3 != nil || err4 != nil {
			return fmt.Sprintf("refusal: %v %v %v %v", err1, err2, err3, err4)
		}
		if ratOfDec(qx).Cmp(ratOfDec(qy)) > 0 || ratOfDec(px).Cmp(ratOfDec(py)) > 0 {
			return fmt.Sprintf("%v <= %v but rounds to %v > %v (10^%d) or %v > %v (%d digits) under %v", x, y, qx, qy, k, px, py, p, m)
		}
		return ""
	}},
	{"rounding-is-idempotent", func(g *gen, o lawOps) string {
		m := libModes[g.rng.IntN(int(modeCount)-1)]
		k, p := int32(g.target()), uint32(g.precision())
		x := parse(g.decimal(-15, 10))
		q, _, _ := o.quantize(x, k, m)
		qq, c, err := o.quantize(q, k, decimal.Exact)
		if err != nil || c != 0 || !sameCohort(q, qq) {
			return fmt.Sprintf("Quantize(%v) = %v is not a fixed point: %v %v %v", x, k, qq, c, err)
		}
		r, _, _ := o.toPrec(x, p, m)
		rr, c, err := o.toPrec(r, p, decimal.Exact)
		if err != nil || c != 0 || !sameCohort(r, rr) {
			return fmt.Sprintf("RoundToPrecision(%v, %d) = %v is not a fixed point: %v %v %v", x, p, r, rr, c, err)
		}
		if red := o.reduce(x); !sameCohort(o.reduce(red), red) || red.Compare(x) != 0 {
			return fmt.Sprintf("Reduce(%v) = %v is not an equal fixed point", x, red)
		}
		return ""
	}},
	{"directed-modes-enclose-the-exact-value", func(g *gen, o lawOps) string {
		// Independent checker: TowardNegativeInfinity and
		// TowardPositiveInfinity bracket the exact value one unit apart
		// (or coincide when exact), and every other mode picks one of them.
		k := int32(g.target())
		x := parse(g.decimal(-15, 10))
		if g.rng.IntN(2) == 0 {
			x = parse(g.tieAt(int(k)))
		}
		lo, _, _ := o.quantize(x, k, decimal.TowardNegativeInfinity)
		hi, _, _ := o.quantize(x, k, decimal.TowardPositiveInfinity)
		v, l, h := ratOfDec(x), ratOfDec(lo), ratOfDec(hi)
		gap := new(big.Rat).Sub(h, l)
		if l.Cmp(v) > 0 || h.Cmp(v) < 0 || (gap.Sign() != 0 && gap.Cmp(pow10(int(k))) != 0) || (gap.Sign() == 0) != (l.Cmp(v) == 0) {
			return fmt.Sprintf("%v at 10^%d: [%v, %v] does not enclose it one unit wide", x, k, lo, hi)
		}
		for m := range modeCount - 1 {
			r, _, _ := o.quantize(x, k, libModes[m])
			if rv := ratOfDec(r); rv.Cmp(l) != 0 && rv.Cmp(h) != 0 {
				return fmt.Sprintf("%v at 10^%d under %v = %v, outside {%v, %v}", x, k, libModes[m], r, lo, hi)
			}
		}
		return ""
	}},
	{"negation-mirrors-the-modes", func(g *gen, o lawOps) string {
		k := int32(g.target())
		x := parse(g.decimal(-15, 10))
		if g.rng.IntN(2) == 0 {
			x = parse(g.tieAt(int(k)))
		}
		mirror := map[decimal.RoundingMode]decimal.RoundingMode{
			decimal.TowardPositiveInfinity: decimal.TowardNegativeInfinity, decimal.TowardNegativeInfinity: decimal.TowardPositiveInfinity,
		}
		for m := range modeCount - 1 {
			mm := libModes[m]
			neg := mm
			if n, ok := mirror[mm]; ok {
				neg = n
			}
			a, _, _ := o.quantize(x, k, mm)
			b, _, _ := o.quantize(x.Neg(), k, neg)
			if ratOfDec(a).Cmp(new(big.Rat).Neg(ratOfDec(b))) != 0 {
				return fmt.Sprintf("round(%v, %v) = %v but round(-x, %v) = %v", x, mm, a, neg, b)
			}
		}
		return ""
	}},
	{"compare-equal-and-hash-agree", func(g *gen, o lawOps) string {
		x := parse(g.decimal(-6, 6))
		y := x
		switch g.rng.IntN(3) {
		case 0:
			y = parse(g.decimal(-6, 6))
		case 1:
			y, _, _ = x.Quantize(x.Exponent()-int32(1+g.rng.IntN(4)), decimal.Exact)
		}
		c, want := o.compare(x, y), ratOfDec(x).Cmp(ratOfDec(y))
		if c != want || o.compare(y, x) != -want || x.Equal(y) != (want == 0) {
			return fmt.Sprintf("Compare(%v, %v) = %d, reverse %d, Equal %v; exact order %d", x, y, c, o.compare(y, x), x.Equal(y), want)
		}
		if want == 0 {
			seed := maphash.MakeSeed()
			var h1, h2 maphash.Hash
			h1.SetSeed(seed)
			h2.SetSeed(seed)
			decimal.Hasher{}.Hash(&h1, x)
			decimal.Hasher{}.Hash(&h2, y)
			var hasher decimal.Hasher
			if h1.Sum64() != h2.Sum64() || !hasher.Equal(x, y) || !sameCohort(o.reduce(x), o.reduce(y)) {
				return fmt.Sprintf("equal values %v and %v hash or reduce differently", x, y)
			}
		}
		return ""
	}},
	{"text-round-trips", func(g *gen, o lawOps) string {
		x := parse(g.decimal(-40, 40))
		y, err := decimal.Parse(o.text(x))
		b, merr := x.MarshalJSON()
		var z decimal.Decimal
		uerr := z.UnmarshalJSON(b)
		same := func(a decimal.Decimal) bool { return a.Equal(x) && a.Exponent() == x.Exponent() }
		if err != nil || merr != nil || uerr != nil || !same(y) || !same(z) {
			return fmt.Sprintf("%v does not round-trip: %v %v %v (%v %v %v)", x, y, z, string(b), err, merr, uerr)
		}
		return ""
	}},
}

// runLaws checks every law n times with a seeded stream and returns the
// violations by law.
func runLaws(seed uint64, n int, o lawOps) map[string][]string {
	out := map[string][]string{}
	for i, l := range laws {
		g := &gen{rng: rand.New(rand.NewPCG(seed, uint64(i)))}
		for range n {
			if msg := l.check(g, o); msg != "" {
				out[l.name] = append(out[l.name], msg)
			}
		}
	}
	return out
}
