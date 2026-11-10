// SPDX-License-Identifier: Apache-2.0

package main

import (
	"math"
	"math/big"
	"strconv"
	"strings"

	"github.com/0xCarbon/decimal"
)

// The operation table: every operation of the library that rounds an exactly
// known value, including fused multiplication/addition.
// Quo/Rem/RemNear return exact results and have their own integer oracle.

// multipliers are terminating reciprocals, so t/y is a decimal for the Mul
// tie construction.
var multipliers = []string{"2", "4", "5", "8", "25", "0.5", "0.2", "1.25", "125E-3", "16", "-2", "-0.25"}

// multiples are RoundToMultiple quanta (cash, lot and odd steps).
var multiples = []string{"0.05", "0.25", "5", "3", "7E-2", "1E+2", "0.3", "0.01", "12.5"}

func ratOf(s string) *big.Rat { return mustRat(s) }

// ratSourceExponent is the cohort a rational source brings (the Div ideal
// exponent 0 of its integer numerator and denominator): the
// exponent nearest 0 that represents it, min(0, reduced exponent).
func ratSourceExponent(r *big.Rat) int {
	if r.Sign() == 0 {
		return 0
	}
	if isTerminating(r.Denom()) {
		return min(0, reducedExponent(r))
	}
	return 0
}

// isTerminating reports a denominator with no prime factors but 2 and 5.
func isTerminating(d *big.Int) bool {
	d = new(big.Int).Set(d)
	for _, f := range []int64{2, 5} {
		for new(big.Int).Mod(d, big.NewInt(f)).Sign() == 0 {
			d.Quo(d, big.NewInt(f))
		}
	}
	return d.Cmp(bigOne) == 0
}

// expOf is the stored exponent of generated decimal text.
func expOf(s string) int {
	_, _, e, _ := parseText(s)
	return e
}

func mul(a, b *big.Rat) *big.Rat { return new(big.Rat).Mul(a, b) }

func (g *gen) nonzero(lo, hi int) string {
	for {
		if s := g.decimal(lo, hi); ratOf(s).Sign() != 0 {
			return s
		}
	}
}

func (g *gen) target() int { return -12 + g.rng.IntN(21) }

// double draws a normal binary64 with magnitude between about 1e-30 and
// 1e30, or, as a tie, n/2^j with n odd, whose decimal expansion ends in 5.
func (g *gen) double(tie bool) float64 {
	if tie {
		j := 1 + g.rng.IntN(14)
		n := float64(2*g.rng.IntN(1<<20) + 1)
		f := math.Ldexp(n, -j)
		if g.rng.IntN(2) == 0 {
			f = -f
		}
		return f
	}
	f := math.Ldexp(1+g.rng.Float64(), -100+g.rng.IntN(200))
	if g.rng.IntN(2) == 0 {
		f = -f
	}
	return f
}

// nudge keeps a tie double one time in three and otherwise moves it one
// binary64 step up or down: just above or just below the decimal tie.
func (g *gen) nudge(f float64) float64 {
	switch g.rng.IntN(3) {
	case 1:
		return math.Nextafter(f, math.Inf(1))
	case 2:
		return math.Nextafter(f, math.Inf(-1))
	}
	return f
}

// nearHalfDigits picks a precision at which the exact power v ties or
// nearly ties: its last digit is 5, so p = digits-1 is an exact tie; a
// position whose first dropped digit is 4 or 5 (and not the last) is just
// below or just above half.
func (g *gen) nearHalfDigits(v *big.Rat) int {
	mant, _, _ := strings.Cut(ratText(new(big.Rat).Abs(v)), "E")
	mant = strings.TrimLeft(mant, "0")
	var near []int
	for i := 1; i < len(mant)-1; i++ {
		if mant[i] == '4' || mant[i] == '5' {
			near = append(near, i)
		}
	}
	if len(near) == 0 || g.rng.IntN(3) == 0 {
		return max(len(strings.TrimRight(mant, "0"))-1, 1)
	}
	return near[g.rng.IntN(len(near))]
}

// tieExponent is the exponent at which n/2^j (the tie double) ties: its
// expansion has j fractional digits ending in 5.
func tieExponent(f float64) int {
	r := new(big.Rat).SetFloat64(f)
	j := 0
	for d := new(big.Int).Set(r.Denom()); d.Cmp(bigOne) > 0; d.Rsh(d, 1) {
		j++
	}
	return -(j - 1)
}

// digitsOf counts the significant digits of a terminating rational.
func digitsOf(r *big.Rat) int {
	if r.Sign() == 0 {
		return 1
	}
	mant, _, _ := strings.Cut(ratText(new(big.Rat).Abs(r)), "E")
	return len(strings.Trim(mant, "0"))
}

var ops = []opSpec{
	{
		name: "FMAWithContext", digitTarget: true,
		gen: func(g *gen, tie bool) input {
			p, x, y := g.precision(), g.decimal(-12, 12), g.decimal(-12, 12)
			product := mul(ratOf(x), ratOf(y))
			if tie {
				// Construct the exact sum first, then solve z=t-x*y using
				// rational arithmetic. Neither factor is rounded.
				target := ratOf(g.tieDigits(p, -8, 8))
				return input{x: x, y: y, z: ratText(new(big.Rat).Sub(target, product)), p: p, tie: true}
			}
			if g.rng.IntN(5) == 0 {
				return input{x: x, y: y, z: ratText(new(big.Rat).Neg(product)), p: p}
			}
			return input{x: x, y: y, z: g.decimal(-12, 12), p: p}
		},
		lib: func(in input, m decimal.RoundingMode) output {
			return dec(parse(in.x).FMAWithContext(parse(in.y), parse(in.z), ctx(in.p, m)))
		},
		ref: func(in input, m mode) expect {
			sum := new(big.Rat).Add(mul(ratOf(in.x), ratOf(in.y)), ratOf(in.z))
			return expDigitsIdeal(roundToDigits(sum, in.p, m), in.p, min(expOf(in.x)+expOf(in.y), expOf(in.z)))
		},
	},
	{
		name: "AddWithContext", digitTarget: true,
		gen: func(g *gen, tie bool) input {
			p, y := g.precision(), g.decimal(-12, 12)
			if !tie {
				return input{x: g.decimal(-12, 12), y: y, p: p}
			}
			t := ratOf(g.tieDigits(p, -8, 8))
			return input{x: ratText(new(big.Rat).Sub(t, ratOf(y))), y: y, p: p, tie: true}
		},
		lib: func(in input, m decimal.RoundingMode) output {
			return dec(parse(in.x).AddWithContext(parse(in.y), ctx(in.p, m)))
		},
		ref: func(in input, m mode) expect {
			return expDigitsIdeal(roundToDigits(new(big.Rat).Add(ratOf(in.x), ratOf(in.y)), in.p, m), in.p, min(expOf(in.x), expOf(in.y)))
		},
	},
	{
		name: "SubWithContext", digitTarget: true,
		gen: func(g *gen, tie bool) input {
			p, y := g.precision(), g.decimal(-12, 12)
			if !tie {
				return input{x: g.decimal(-12, 12), y: y, p: p}
			}
			t := ratOf(g.tieDigits(p, -8, 8))
			return input{x: ratText(new(big.Rat).Add(t, ratOf(y))), y: y, p: p, tie: true}
		},
		lib: func(in input, m decimal.RoundingMode) output {
			return dec(parse(in.x).SubWithContext(parse(in.y), ctx(in.p, m)))
		},
		ref: func(in input, m mode) expect {
			return expDigitsIdeal(roundToDigits(new(big.Rat).Sub(ratOf(in.x), ratOf(in.y)), in.p, m), in.p, min(expOf(in.x), expOf(in.y)))
		},
	},
	{
		name: "MulWithContext", digitTarget: true,
		gen: func(g *gen, tie bool) input {
			p := g.precision()
			if !tie {
				return input{x: g.decimal(-12, 12), y: g.decimal(-12, 12), p: p}
			}
			y := multipliers[g.rng.IntN(len(multipliers))]
			t := ratOf(g.tieDigits(p, -8, 8))
			return input{x: ratText(new(big.Rat).Quo(t, ratOf(y))), y: y, p: p, tie: true}
		},
		lib: func(in input, m decimal.RoundingMode) output {
			return dec(parse(in.x).MulWithContext(parse(in.y), ctx(in.p, m)))
		},
		ref: func(in input, m mode) expect {
			return expDigitsIdeal(roundToDigits(mul(ratOf(in.x), ratOf(in.y)), in.p, m), in.p, expOf(in.x)+expOf(in.y))
		},
	},
	{
		name: "DivWithContext", digitTarget: true,
		gen: func(g *gen, tie bool) input {
			p, y := g.precision(), g.nonzero(-12, 12)
			if !tie {
				return input{x: g.decimal(-12, 12), y: y, p: p}
			}
			t := ratOf(g.tieDigits(p, -8, 8))
			return input{x: ratText(mul(t, ratOf(y))), y: y, p: p, tie: true}
		},
		lib: func(in input, m decimal.RoundingMode) output {
			return dec(parse(in.x).DivWithContext(parse(in.y), ctx(in.p, m)))
		},
		ref: func(in input, m mode) expect {
			return expDigitsIdeal(roundToDigits(new(big.Rat).Quo(ratOf(in.x), ratOf(in.y)), in.p, m), in.p, expOf(in.x)-expOf(in.y))
		},
	},
	{
		name: "DivToExponent",
		gen: func(g *gen, tie bool) input {
			k, y := g.target(), g.nonzero(-12, 12)
			if !tie {
				return input{x: g.decimal(-12, 12), y: y, k: k}
			}
			return input{x: ratText(mul(ratOf(g.tieAt(k)), ratOf(y))), y: y, k: k, tie: true}
		},
		lib: func(in input, m decimal.RoundingMode) output {
			return dec(parse(in.x).DivToExponent(parse(in.y), int32(in.k), m))
		},
		ref: func(in input, m mode) expect {
			return expAtFrom(roundToExponent(new(big.Rat).Quo(ratOf(in.x), ratOf(in.y)), in.k, m), in.k, expOf(in.x)-expOf(in.y))
		},
	},
	{
		name: "PowWithContext", digitTarget: true,
		gen: func(g *gen, tie bool) input {
			if !tie {
				n := -3 + g.rng.IntN(9)
				x := g.sign() + g.digits(1+g.rng.IntN(6)) + "E" + strconv.Itoa(-4+g.rng.IntN(9))
				return input{x: x, n: n, p: g.precision()}
			}
			// A base ending in 5 has a power ending in 5; the harness sets p
			// one below the power's digit count, so the power ties.
			x := g.sign() + g.digits(g.rng.IntN(3)) + "5E" + strconv.Itoa(-3+g.rng.IntN(7))
			n := 2 + g.rng.IntN(3)
			v := new(big.Rat).SetInt64(1)
			for range n {
				v.Mul(v, ratOf(x))
			}
			return input{x: x, n: n, p: g.nearHalfDigits(v), tie: true}
		},
		lib: func(in input, m decimal.RoundingMode) output {
			return dec(parse(in.x).PowWithContext(int32(in.n), ctx(in.p, m)))
		},
		ref: func(in input, m mode) expect {
			b := ratOf(in.x)
			v := new(big.Rat).SetInt64(1)
			for range max(in.n, -in.n) {
				v.Mul(v, b)
			}
			if in.n < 0 {
				// The reciprocal's cohort is checked elsewhere; only value and digits.
				v.Inv(v)
				return expDigits(roundToDigits(v, in.p, m), in.p)
			}
			return expDigitsIdeal(roundToDigits(v, in.p, m), in.p, in.n*expOf(in.x))
		},
	},
	{
		name: "SqrtWithContext", digitTarget: true,
		gen: func(g *gen, tie bool) input {
			p := g.precision()
			if !tie {
				x := g.decimal(-12, 12)
				if x[0] == '-' {
					x = x[1:]
				}
				return input{x: x, p: p}
			}
			// root = p digits then 5 (an exact tie at p digits); its square,
			// or the square plus or minus one unit, is the operand.
			root := ratOf(g.digits(p) + "5E" + strconv.Itoa(-6+g.rng.IntN(13)))
			v := mul(root, root)
			_, _, e, _ := parseText(ratText(v))
			switch g.rng.IntN(3) {
			case 1:
				v.Add(v, pow10(e))
			case 2:
				v.Sub(v, pow10(e))
			}
			return input{x: ratText(v), p: p, tie: true}
		},
		lib: func(in input, m decimal.RoundingMode) output {
			return dec(parse(in.x).SqrtWithContext(ctx(in.p, m)))
		},
		ref: func(in input, m mode) expect {
			return expDigits(roundSqrtToDigits(ratOf(in.x), in.p, m), in.p)
		},
	},
	{
		name: "Quantize",
		gen:  genToExponent,
		lib: func(in input, m decimal.RoundingMode) output {
			return dec(parse(in.x).Quantize(int32(in.k), m))
		},
		ref: func(in input, m mode) expect {
			return expAtFrom(roundToExponent(ratOf(in.x), in.k, m), in.k, expOf(in.x))
		},
	},
	{
		name: "QuantizeWithContext",
		gen: func(g *gen, tie bool) input {
			in := genToExponent(g, tie)
			in.p = g.precision()
			return in
		},
		lib: func(in input, m decimal.RoundingMode) output {
			return dec(parse(in.x).QuantizeWithContext(int32(in.k), ctx(in.p, m)))
		},
		ref: func(in input, m mode) expect {
			return fitsOrInvalid(expAtFrom(roundToExponent(ratOf(in.x), in.k, m), in.k, expOf(in.x)), in.p)
		},
	},
	{
		name: "RoundToIntegral",
		gen:  func(g *gen, tie bool) input { in := genToExponent(g, tie); in.k = 0; return retarget(g, in, tie) },
		lib: func(in input, m decimal.RoundingMode) output {
			return dec(parse(in.x).RoundToIntegral(m))
		},
		ref: func(in input, m mode) expect { return expAtFrom(roundToExponent(ratOf(in.x), 0, m), 0, expOf(in.x)) },
	},
	{
		name: "RoundToIntegralWithContext",
		gen: func(g *gen, tie bool) input {
			in := genToExponent(g, tie)
			in.k = 0
			in = retarget(g, in, tie)
			in.p = g.precision()
			return in
		},
		lib: func(in input, m decimal.RoundingMode) output {
			return dec(parse(in.x).RoundToIntegralWithContext(ctx(in.p, m)))
		},
		ref: func(in input, m mode) expect {
			return fitsOrInvalid(expAtFrom(roundToExponent(ratOf(in.x), 0, m), 0, expOf(in.x)), in.p)
		},
	},
	{
		name: "RoundToPrecision", digitTarget: true,
		gen: genToDigits,
		lib: func(in input, m decimal.RoundingMode) output {
			return dec(parse(in.x).RoundToPrecision(uint32(in.p), m))
		},
		ref: func(in input, m mode) expect {
			return expDigitsIdeal(roundToDigits(ratOf(in.x), in.p, m), in.p, expOf(in.x))
		},
	},
	{
		name: "RoundToPrecisionWithContext", digitTarget: true,
		gen: genToDigits,
		lib: func(in input, m decimal.RoundingMode) output {
			return dec(parse(in.x).RoundToPrecisionWithContext(ctx(in.p, m)))
		},
		ref: func(in input, m mode) expect {
			return expDigitsIdeal(roundToDigits(ratOf(in.x), in.p, m), in.p, expOf(in.x))
		},
	},
	{
		name: "RoundToMultiple",
		gen: func(g *gen, tie bool) input {
			q := multiples[g.rng.IntN(len(multiples))]
			if !tie {
				return input{x: g.decimal(-6, 4), y: q}
			}
			// (2r+1)·q/2 lies halfway between the multiples r·q and (r+1)·q;
			// a tail moves it just off the tie.
			r := int64(g.rng.IntN(20001) - 10000)
			v := mul(big.NewRat(2*r+1, 2), ratOf(q))
			if g.rng.IntN(3) == 1 {
				v.Add(v, pow10(-30))
			}
			return input{x: ratText(v), y: q, tie: true}
		},
		lib: func(in input, m decimal.RoundingMode) output {
			return dec(parse(in.x).RoundToMultiple(parse(in.y), m))
		},
		ref: func(in input, m mode) expect {
			q := ratOf(in.y)
			r := roundToExponent(new(big.Rat).Quo(ratOf(in.x), q), 0, m)
			r.value = mul(r.value, q)
			_, _, e, _ := parseText(in.y)
			return expAt(r, e)
		},
	},
	{
		name: "FromRatToExponent",
		gen: func(g *gen, tie bool) input {
			k := g.target()
			if tie {
				return input{r: ratOf(g.tieAt(k)), k: k, tie: true}
			}
			return input{r: g.rational(), k: k}
		},
		lib: func(in input, m decimal.RoundingMode) output {
			return dec(decimal.FromRatToExponent(in.r, int32(in.k), m))
		},
		ref: func(in input, m mode) expect {
			return expAtFrom(roundToExponent(in.r, in.k, m), in.k, ratSourceExponent(in.r))
		},
	},
	{
		name: "FromRatWithContext", digitTarget: true,
		gen: func(g *gen, tie bool) input {
			p := g.precision()
			if tie {
				return input{r: ratOf(g.tieDigits(p, -10, 10)), p: p, tie: true}
			}
			return input{r: g.rational(), p: p}
		},
		lib: func(in input, m decimal.RoundingMode) output {
			return dec(decimal.FromRatWithContext(in.r, ctx(in.p, m)))
		},
		ref: func(in input, m mode) expect { return expDigitsIdeal(roundToDigits(in.r, in.p, m), in.p, 0) },
	},
	{
		name: "FromFloat64ToExponent",
		gen: func(g *gen, tie bool) input {
			f := g.double(tie)
			k := g.target()
			if tie {
				k = tieExponent(f)
				f = g.nudge(f)
			}
			return input{f: f, k: k, tie: tie}
		},
		lib: func(in input, m decimal.RoundingMode) output {
			return dec(decimal.FromFloat64ToExponent(in.f, int32(in.k), m))
		},
		ref: func(in input, m mode) expect {
			v := new(big.Rat).SetFloat64(in.f)
			return expAtFrom(roundToExponent(v, in.k, m), in.k, ratSourceExponent(v))
		},
	},
	{
		name: "FromFloat64WithContext", digitTarget: true,
		gen: func(g *gen, tie bool) input {
			f := g.double(tie)
			p := g.precision()
			if tie {
				p = max(digitsOf(new(big.Rat).SetFloat64(f))-1, 1)
				f = g.nudge(f)
			}
			return input{f: f, p: p, tie: tie}
		},
		lib: func(in input, m decimal.RoundingMode) output {
			return dec(decimal.FromFloat64WithContext(in.f, ctx(in.p, m)))
		},
		ref: func(in input, m mode) expect {
			return expDigitsIdeal(roundToDigits(new(big.Rat).SetFloat64(in.f), in.p, m), in.p, 0)
		},
	},
	{
		name: "Float64Rounded",
		gen: func(g *gen, tie bool) input {
			if !tie {
				return input{x: g.sign() + g.digits(1+g.rng.IntN(30)) + "E" + strconv.Itoa(-40+g.rng.IntN(60))}
			}
			// The midpoint of two adjacent doubles is a terminating decimal
			// tie; a tail moves it just off.
			f := math.Abs(g.double(false))
			mid := new(big.Rat).Add(new(big.Rat).SetFloat64(f), new(big.Rat).SetFloat64(math.Nextafter(f, math.Inf(1))))
			mid.Mul(mid, ratHalf)
			switch g.rng.IntN(3) {
			case 1:
				mid.Add(mid, mul(pow10(-40), new(big.Rat).SetFloat64(f)))
			case 2:
				mid.Sub(mid, mul(pow10(-40), new(big.Rat).SetFloat64(f)))
			}
			return input{x: g.sign() + ratText(mid), tie: true}
		},
		lib: func(in input, m decimal.RoundingMode) output {
			f, c, err := parse(in.x).Float64Rounded(m)
			return output{f: f, conds: c, err: err}
		},
		ref: func(in input, m mode) expect {
			f, r := roundToFloat64(ratOf(in.x), m)
			return expect{r: r, f: f, isFloat: true}
		},
	},
	{
		name: "ParseToExponent",
		gen:  genToExponent,
		lib: func(in input, m decimal.RoundingMode) output {
			return dec(decimal.ParseToExponent(in.x, int32(in.k), m))
		},
		ref: func(in input, m mode) expect {
			return expAtFrom(roundToExponent(ratOf(in.x), in.k, m), in.k, expOf(in.x))
		},
	},
	{
		name: "ParseWithContext", digitTarget: true,
		gen: genToDigits,
		lib: func(in input, m decimal.RoundingMode) output {
			return dec(decimal.ParseWithContext(in.x, ctx(in.p, m)))
		},
		ref: func(in input, m mode) expect {
			return expDigitsIdeal(roundToDigits(ratOf(in.x), in.p, m), in.p, expOf(in.x))
		},
	},
}

// genToExponent draws x and a target exponent k; ties sit at k.
func genToExponent(g *gen, tie bool) input {
	k := g.target()
	if tie {
		return input{x: g.tieAt(k), k: k, tie: true}
	}
	return input{x: g.decimal(-15, 10), k: k}
}

// retarget rebuilds a tie for target exponent 0 after the caller fixed k.
func retarget(g *gen, in input, tie bool) input {
	if tie {
		in.x = g.tieAt(0)
	}
	return in
}

// genToDigits draws x and a precision p; ties sit at digit p+1.
func genToDigits(g *gen, tie bool) input {
	p := g.precision()
	if tie {
		return input{x: g.tieDigits(p, -15, 10), p: p, tie: true}
	}
	return input{x: g.decimal(-15, 10), p: p}
}

// rational draws a/b with b holding factors 2, 5 and sometimes 3 or 7, so
// both terminating and non-terminating quotients occur.
func (g *gen) rational() *big.Rat {
	a := new(big.Int)
	a.SetString(g.digits(1+g.rng.IntN(25)), 10)
	if g.rng.IntN(2) == 0 {
		a.Neg(a)
	}
	b := big.NewInt(1)
	for _, f := range []int64{2, 5, 3, 7} {
		for range g.rng.IntN(6) {
			if (f == 3 || f == 7) && g.rng.IntN(2) == 0 {
				continue
			}
			b.Mul(b, big.NewInt(f))
		}
	}
	return new(big.Rat).SetFrac(a, b)
}
