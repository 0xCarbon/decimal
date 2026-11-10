// SPDX-License-Identifier: Apache-2.0

package main

import (
	"math"
	"math/big"
	"strings"
)

// The reference: exact rational arithmetic from math/big and a rounding
// decision written here from the rounding-mode
// definitions, independent of the library. The harness always supplies the
// target (an exponent or a number of significant digits) and the mode; the
// reference never infers a policy from the value it checks.

// mode names a rounding rule. The reference implements each rule from
// its definition; the harness maps it to the library's constant by name.
type mode int

const (
	tiesToEven mode = iota
	tiesAwayFromZero
	tiesTowardZero
	towardZero
	awayFromZero
	towardPositive
	towardNegative
	exactOnly
	modeCount
)

var modeNames = [...]string{"TiesToEven", "TiesAwayFromZero", "TiesTowardZero", "TowardZero",
	"AwayFromZero", "TowardPositiveInfinity", "TowardNegativeInfinity", "Exact"}

func (m mode) String() string { return modeNames[m] }

// rounded is a reference result: the rounded value, whether rounding
// changed the value, the sign of (rounded - exact), and refused for an
// Exact-mode value change.
type rounded struct {
	value   *big.Rat
	inexact bool
	dir     int
	refused bool
}

var (
	ratHalf = big.NewRat(1, 2)
	bigOne  = big.NewInt(1)
	bigTen  = big.NewInt(10)
)

// pow10 returns 10^k as a rational for any int k.
func pow10(k int) *big.Rat {
	n := k
	if n < 0 {
		n = -n
	}
	p := new(big.Int).Exp(bigTen, big.NewInt(int64(n)), nil)
	if k >= 0 {
		return new(big.Rat).SetInt(p)
	}
	return new(big.Rat).SetFrac(big.NewInt(1), p)
}

// roundUp decides whether the magnitude floor q is incremented, given
// whether the discarded part is zero and its comparison with one half.
func roundUp(q *big.Int, exact bool, half int, negative bool, m mode) bool {
	if exact {
		return false
	}
	switch m {
	case towardZero, exactOnly:
		return false
	case awayFromZero:
		return true
	case towardPositive:
		return !negative
	case towardNegative:
		return negative
	}
	switch {
	case half > 0:
		return true
	case half < 0:
		return false
	case m == tiesAwayFromZero:
		return true
	case m == tiesTowardZero:
		return false
	default: // tiesToEven: up only from an odd floor
		return q.Bit(0) == 1
	}
}

// roundToExponent rounds x to an integer multiple of 10^k.
func roundToExponent(x *big.Rat, k int, m mode) rounded {
	scaled := new(big.Rat).Mul(new(big.Rat).Abs(x), pow10(-k))
	q := new(big.Int).Quo(scaled.Num(), scaled.Denom())
	frac := new(big.Rat).Sub(scaled, new(big.Rat).SetInt(q))
	exact := frac.Sign() == 0
	if roundUp(q, exact, frac.Cmp(ratHalf), x.Sign() < 0, m) {
		q.Add(q, bigOne)
	}
	v := new(big.Rat).Mul(new(big.Rat).SetInt(q), pow10(k))
	if x.Sign() < 0 {
		v.Neg(v)
	}
	return rounded{value: v, inexact: !exact, dir: v.Cmp(x), refused: m == exactOnly && !exact}
}

// adjusted returns floor(log10 |x|) for nonzero x by exact comparison.
func adjusted(x *big.Rat) int {
	a := new(big.Rat).Abs(x)
	e := len(a.Num().String()) - len(a.Denom().String())
	for pow10(e).Cmp(a) > 0 {
		e--
	}
	for pow10(e+1).Cmp(a) <= 0 {
		e++
	}
	return e
}

// roundToDigits rounds x to p > 0 significant digits; zero is exact.
func roundToDigits(x *big.Rat, p int, m mode) rounded {
	if x.Sign() == 0 {
		return rounded{value: new(big.Rat)}
	}
	return roundToExponent(x, adjusted(x)-p+1, m)
}

// floorDiv returns floor(a / b) for b > 0.
func floorDiv(a, b int) int {
	q := a / b
	if a%b != 0 && (a < 0) != (b < 0) {
		q--
	}
	return q
}

// roundSqrtToDigits rounds sqrt(v), v >= 0, to p significant digits using
// integer comparisons only: with N = v·10^(-2k) and q = floor(sqrt(N)) =
// isqrt(floor(N)), the root is exact iff q² = N, and it compares with the
// midpoint q + 1/2 as 4N compares with (2q+1)². The direction of an inexact
// result is the sign of result² - v.
func roundSqrtToDigits(v *big.Rat, p int, m mode) rounded {
	if v.Sign() == 0 {
		return rounded{value: new(big.Rat)}
	}
	k := floorDiv(adjusted(v), 2) - p + 1
	n := new(big.Rat).Mul(v, pow10(-2*k))
	q := new(big.Int).Sqrt(new(big.Int).Quo(n.Num(), n.Denom()))
	exact := new(big.Rat).SetInt(new(big.Int).Mul(q, q)).Cmp(n) == 0
	odd := new(big.Int).Add(new(big.Int).Lsh(q, 1), bigOne)
	half := new(big.Rat).Mul(n, big.NewRat(4, 1)).Cmp(new(big.Rat).SetInt(new(big.Int).Mul(odd, odd)))
	if roundUp(q, exact, half, false, m) {
		q.Add(q, bigOne)
	}
	value := new(big.Rat).Mul(new(big.Rat).SetInt(q), pow10(k))
	r := rounded{value: value, inexact: !exact, refused: m == exactOnly && !exact}
	if !exact {
		r.dir = new(big.Rat).Mul(value, value).Cmp(v)
	}
	return r
}

// roundToFloat64 rounds x to a binary64 under m. The harness keeps
// 2^-1000 <= |x| <= 2^1000, the normal range, where a 53-bit big.Float
// truncation is the lower neighbor exactly.
func roundToFloat64(x *big.Rat, m mode) (float64, rounded) {
	neg := x.Sign() < 0
	a := new(big.Rat).Abs(x)
	f, _ := new(big.Float).SetPrec(53).SetMode(big.ToZero).SetRat(a).Float64()
	out := f
	lo := new(big.Rat).SetFloat64(f)
	exact := lo.Cmp(a) == 0
	if !exact {
		hiF := math.Nextafter(f, math.Inf(1))
		mid := new(big.Rat).Add(lo, new(big.Rat).SetFloat64(hiF))
		mid.Mul(mid, ratHalf)
		q := new(big.Int).SetUint64(math.Float64bits(f) & 1)
		if roundUp(q, false, a.Cmp(mid), neg, m) {
			out = hiF
		}
	}
	if neg {
		out = -out
	}
	v := new(big.Rat).SetFloat64(out)
	return out, rounded{value: v, inexact: !exact, dir: v.Cmp(x), refused: m == exactOnly && !exact}
}

// parseText reads canonical or literal decimal text into its exact value,
// coefficient digit count (without leading zeros) and stored exponent,
// independently of the library.
func parseText(s string) (value *big.Rat, digits int, exponent int, ok bool) {
	v, ok := new(big.Rat).SetString(s)
	if !ok {
		return nil, 0, 0, false
	}
	t := strings.TrimLeft(s, "+-")
	mant, expText, hasExp := strings.Cut(strings.ToUpper(t), "E")
	intPart, frac, _ := strings.Cut(mant, ".")
	e := 0
	if hasExp {
		n, ok := new(big.Int).SetString(expText, 10)
		if !ok || !n.IsInt64() || n.Int64() > math.MaxInt32 || n.Int64() < math.MinInt32 {
			return nil, 0, 0, false
		}
		e = int(n.Int64())
	}
	coeff := strings.TrimLeft(intPart+frac, "0")
	return v, max(len(coeff), 1), e - len(frac), true
}
