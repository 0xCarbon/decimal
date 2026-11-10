// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"errors"
	"fmt"
	"math"
	"math/big"
	"math/rand/v2"
	"testing"
)

// The independent trigonometric oracle. It shares no code with production: π
// from Euler's π/4 = atan(1/2) + atan(1/3); sin and cos from the Taylor
// polynomial of e^{ir} in exact rationals with remainder 3·|r|^{N+1}/(N+1)!;
// atan by the π/4 split; asin and acos by bisection on the oracle's sine; the
// hyperbolic functions from the Exp oracle, and their inverses by bisection on
// it. Final rounding reuses the exact big.Rat rounding of the exponential
// oracle.

// trigOracleSeriesError bounds the accumulated rounding of n operations
// on values of magnitude at most 4 at w bits of nearest rounding.
func trigOracleSeriesError(n int64, w uint) *big.Rat {
	return new(big.Rat).SetFrac(big.NewInt(16*(n+2)), new(big.Int).Lsh(big.NewInt(1), w))
}

// trigOracleAtanRat encloses atan u for a rational 0 ≤ u ≤ 1/2 by its
// alternating series at w = prec+64 bits: the first omitted term bounds the
// tail and trigOracleSeriesError every rounding, including u's.
func trigOracleAtanRat(u *big.Rat, prec uint) (lo, hi *big.Rat) {
	w := prec + 64
	eps := new(big.Float).SetMantExp(big.NewFloat(1), -int(prec)-8)
	uf := new(big.Float).SetPrec(w).SetRat(u)
	u2 := new(big.Float).SetPrec(w).Mul(uf, uf)
	pow := new(big.Float).SetPrec(w).Set(uf)
	sum := new(big.Float).SetPrec(w)
	for n := int64(0); ; n++ {
		term := new(big.Float).SetPrec(w).Quo(pow, big.NewFloat(float64(2*n+1)))
		if term.Cmp(eps) < 0 {
			t, _ := term.Rat(nil)
			bound := new(big.Rat).Add(t, trigOracleSeriesError(3*n, w))
			c, _ := sum.Rat(nil)
			return new(big.Rat).Sub(c, bound), new(big.Rat).Add(c, bound)
		}
		if n%2 == 0 {
			sum.Add(sum, term)
		} else {
			sum.Sub(sum, term)
		}
		pow.Mul(pow, u2)
	}
}

// trigOraclePi encloses π = 4·(atan(1/2) + atan(1/3)).
func trigOraclePi(prec uint) (lo, hi *big.Rat) {
	l2, h2 := trigOracleAtanRat(big.NewRat(1, 2), prec+4)
	l3, h3 := trigOracleAtanRat(big.NewRat(1, 3), prec+4)
	four := big.NewRat(4, 1)
	return new(big.Rat).Mul(four, new(big.Rat).Add(l2, l3)), new(big.Rat).Mul(four, new(big.Rat).Add(h2, h3))
}

// trigOracleCis encloses (cos r, sin r) for a rational |r| ≤ 1 from the
// real and imaginary parts of Σ (ir)^n/n! at w = prec+64 bits, with the
// common remainder 3·|r|^{N+1}/(N+1)! (e < 3) plus the rounding bound.
func trigOracleCis(r *big.Rat, prec uint) (cl, ch, sl, sh *big.Rat) {
	w := prec + 64
	eps := new(big.Float).SetMantExp(big.NewFloat(1), -int(prec)-8)
	rf := new(big.Float).SetPrec(w).SetRat(r)
	re, im := new(big.Float).SetPrec(w), new(big.Float).SetPrec(w)
	term := new(big.Float).SetPrec(w).SetInt64(1) // r^n/n!
	for n := int64(0); ; n++ {
		switch n % 4 {
		case 0:
			re.Add(re, term)
		case 1:
			im.Add(im, term)
		case 2:
			re.Sub(re, term)
		case 3:
			im.Sub(im, term)
		}
		term = new(big.Float).SetPrec(w).Quo(new(big.Float).SetPrec(w).Mul(term, rf), big.NewFloat(float64(n+1)))
		if new(big.Float).Abs(term).Cmp(eps) < 0 {
			t, _ := new(big.Float).Abs(term).Rat(nil)
			bound := new(big.Rat).Add(new(big.Rat).Mul(big.NewRat(3, 1), t), trigOracleSeriesError(3*n, w))
			c, _ := re.Rat(nil)
			s, _ := im.Rat(nil)
			return new(big.Rat).Sub(c, bound), new(big.Rat).Add(c, bound), new(big.Rat).Sub(s, bound), new(big.Rat).Add(s, bound)
		}
	}
}

// trigOracleSinCos encloses sin x and cos x for a rational x after reducing
// by the oracle's π with an exact rational quotient: x = r + q·π/2.
func trigOracleSinCos(x *big.Rat, prec uint) (sl, sh, cl, ch *big.Rat) {
	extra := uint(new(big.Int).Abs(new(big.Int).Quo(x.Num(), x.Denom())).BitLen())
	pl, ph := trigOraclePi(prec + extra + 16)
	mid := new(big.Rat).Quo(new(big.Rat).Mul(x, big.NewRat(4, 1)), new(big.Rat).Add(pl, ph))
	q := new(big.Int).Quo(new(big.Int).Add(new(big.Int).Mul(mid.Num(), big.NewInt(2)), mid.Denom()), new(big.Int).Mul(mid.Denom(), big.NewInt(2)))
	if mid.Sign() < 0 {
		q.Sub(q, big.NewInt(1))
	}
	qr := new(big.Rat).SetInt(q)
	// r ∈ [x − q·π_hi/2, x − q·π_lo/2] for q ≥ 0 (and swapped for q < 0).
	a := new(big.Rat).Sub(x, new(big.Rat).Mul(qr, new(big.Rat).Quo(ph, big.NewRat(2, 1))))
	b := new(big.Rat).Sub(x, new(big.Rat).Mul(qr, new(big.Rat).Quo(pl, big.NewRat(2, 1))))
	if a.Cmp(b) > 0 {
		a, b = b, a
	}
	ca, _, sa, _ := trigOracleCis(a, prec+8)
	_, cbh, _, sbh := trigOracleCis(b, prec+8)
	_, cah, _, _ := trigOracleCis(a, prec+8)
	cbl, _, _, _ := trigOracleCis(b, prec+8)
	// sin rises on |r| ≤ 1; cos peaks at zero.
	sl, sh = sa, sbh
	cl, ch = minRat(ca, cbl), maxRat(cah, cbh)
	if a.Sign() <= 0 && b.Sign() >= 0 {
		ch = big.NewRat(1, 1)
	}
	switch new(big.Int).And(q, big.NewInt(3)).Int64() {
	case 1:
		sl, sh, cl, ch = cl, ch, neg(sh), neg(sl)
	case 2:
		sl, sh, cl, ch = neg(sh), neg(sl), neg(ch), neg(cl)
	case 3:
		sl, sh, cl, ch = neg(ch), neg(cl), sl, sh
	}
	return sl, sh, cl, ch
}

func neg(r *big.Rat) *big.Rat { return new(big.Rat).Neg(r) }

func minRat(a, b *big.Rat) *big.Rat {
	if a.Cmp(b) < 0 {
		return a
	}
	return b
}

func maxRat(a, b *big.Rat) *big.Rat {
	if a.Cmp(b) > 0 {
		return a
	}
	return b
}

// trigOracleAtan encloses atan u for any rational u by the π/4 split:
// |u| ≤ 1/2 directly; 1/2 < u ≤ 1 as π/4 + atan((u−1)/(u+1)); u > 1 as
// π/2 − atan(1/u).
func trigOracleAtan(u *big.Rat, prec uint) (lo, hi *big.Rat) {
	if u.Sign() < 0 {
		l, h := trigOracleAtan(neg(u), prec)
		return neg(h), neg(l)
	}
	one := big.NewRat(1, 1)
	pl, ph := trigOraclePi(prec + 8)
	switch {
	case u.Cmp(big.NewRat(1, 2)) <= 0:
		return trigOracleAtanRat(u, prec)
	case u.Cmp(one) <= 0:
		v := new(big.Rat).Quo(new(big.Rat).Sub(u, one), new(big.Rat).Add(u, one))
		l, h := trigOracleAtan(v, prec)
		return new(big.Rat).Add(new(big.Rat).Quo(pl, big.NewRat(4, 1)), l), new(big.Rat).Add(new(big.Rat).Quo(ph, big.NewRat(4, 1)), h)
	default:
		l, h := trigOracleAtan(new(big.Rat).Inv(u), prec)
		return new(big.Rat).Sub(new(big.Rat).Quo(pl, big.NewRat(2, 1)), h), new(big.Rat).Sub(new(big.Rat).Quo(ph, big.NewRat(2, 1)), l)
	}
}

// trigOracleInvert brackets the θ in [lo, hi] with f(θ) = target for an
// increasing f enclosed by fenc, by bisection at rational points until the
// bracket is narrower than 2^−prec.
func trigOracleInvert(fenc func(*big.Rat) (*big.Rat, *big.Rat), target, lo, hi *big.Rat, prec uint) (*big.Rat, *big.Rat) {
	width := new(big.Rat).SetFrac(big.NewInt(1), new(big.Int).Lsh(big.NewInt(1), prec))
	lo, hi = new(big.Rat).Set(lo), new(big.Rat).Set(hi)
	for new(big.Rat).Sub(hi, lo).Cmp(width) > 0 {
		mid := new(big.Rat).Quo(new(big.Rat).Add(lo, hi), big.NewRat(2, 1))
		fl, fh := fenc(mid)
		switch {
		case fh.Cmp(target) < 0:
			lo = mid
		case fl.Cmp(target) > 0:
			hi = mid
		default:
			return nil, nil // undecided at this precision
		}
	}
	return lo, hi
}

// trigOracleHyper encloses sinh, cosh or tanh of a rational from the Exp
// oracle.
func trigOracleHyper(kind evalKind, a *big.Rat, prec uint) (lo, hi *big.Rat) {
	el, eh := oracleExp(a, prec+64)
	il, ih := oracleExp(neg(a), prec+64)
	two := big.NewRat(2, 1)
	switch kind {
	case evalSinh:
		return new(big.Rat).Quo(new(big.Rat).Sub(el, ih), two), new(big.Rat).Quo(new(big.Rat).Sub(eh, il), two)
	case evalCosh:
		return new(big.Rat).Quo(new(big.Rat).Add(el, il), two), new(big.Rat).Quo(new(big.Rat).Add(eh, ih), two)
	}
	// tanh = (e^a − e^−a)/(e^a + e^−a), rising in e^a for a ≥ 0.
	if a.Sign() < 0 {
		l, h := trigOracleHyper(kind, neg(a), prec)
		return neg(h), neg(l)
	}
	return new(big.Rat).Quo(new(big.Rat).Sub(el, ih), new(big.Rat).Add(el, ih)),
		new(big.Rat).Quo(new(big.Rat).Sub(eh, il), new(big.Rat).Add(eh, il))
}

// trigOracle encloses kind at x (and y for Atan2) or reports that the
// bracket is still undecided.
func trigOracle(kind evalKind, x, y *big.Rat, prec uint) (lo, hi *big.Rat) {
	pl, ph := trigOraclePi(prec + 8)
	switch kind {
	case evalSin, evalCos, evalTan:
		sl, sh, cl, ch := trigOracleSinCos(x, prec)
		switch kind {
		case evalSin:
			return sl, sh
		case evalCos:
			return cl, ch
		}
		if cl.Sign() != ch.Sign() {
			return nil, nil
		}
		qs := []*big.Rat{new(big.Rat).Quo(sl, cl), new(big.Rat).Quo(sl, ch), new(big.Rat).Quo(sh, cl), new(big.Rat).Quo(sh, ch)}
		lo, hi = qs[0], qs[0]
		for _, q := range qs[1:] {
			lo, hi = minRat(lo, q), maxRat(hi, q)
		}
		return lo, hi
	case evalAtan:
		return trigOracleAtan(x, prec)
	case evalAtan2:
		// Quadrant from the signs, angle from the ratio.
		if x.Sign() == 0 {
			l, h := new(big.Rat).Quo(pl, big.NewRat(2, 1)), new(big.Rat).Quo(ph, big.NewRat(2, 1))
			if y.Sign() < 0 {
				return neg(h), neg(l)
			}
			return l, h
		}
		l, h := trigOracleAtan(new(big.Rat).Quo(y, x), prec)
		if x.Sign() < 0 {
			if y.Sign() >= 0 {
				return new(big.Rat).Add(l, pl), new(big.Rat).Add(h, ph)
			}
			return new(big.Rat).Sub(l, ph), new(big.Rat).Sub(h, pl)
		}
		return l, h
	case evalAsin, evalAcos:
		sin := func(t *big.Rat) (*big.Rat, *big.Rat) {
			l, h, _, _ := trigOracleSinCos(t, prec+16)
			return l, h
		}
		a := new(big.Rat).Abs(x)
		l, h := trigOracleInvert(sin, a, new(big.Rat), big.NewRat(16, 10), prec)
		if l == nil {
			return nil, nil
		}
		if kind == evalAsin {
			if x.Sign() < 0 {
				return neg(h), neg(l)
			}
			return l, h
		}
		// acos x = π/2 − asin x.
		if x.Sign() < 0 {
			l, h = neg(h), neg(l)
		}
		return new(big.Rat).Sub(new(big.Rat).Quo(pl, big.NewRat(2, 1)), h), new(big.Rat).Sub(new(big.Rat).Quo(ph, big.NewRat(2, 1)), l)
	case evalSinh, evalCosh, evalTanh:
		return trigOracleHyper(kind, x, prec)
	}
	// Inverse hyperbolic functions from the root-reduced logarithm
	// oracle and directed big.Float square roots: asinh a = ln(a+√(a²+1)),
	// acosh a = ln(a+√(a²−1)), atanh a = ½·ln((1+a)/(1−a)), each rising in
	// its inner expression.
	a := new(big.Rat).Abs(x)
	one := big.NewRat(1, 1)
	var innerLo, innerHi *big.Rat
	if kind == evalAtanh {
		r := new(big.Rat).Quo(new(big.Rat).Add(one, a), new(big.Rat).Sub(one, a))
		innerLo, innerHi = r, r
	} else {
		w := prec + 64
		sq := new(big.Rat).Mul(a, a)
		if kind == evalAsinh {
			sq.Add(sq, one)
		} else {
			sq.Sub(sq, one)
		}
		sl := oracleSqrt(oracleFloat(w, big.ToNegativeInf).SetRat(sq), w, false)
		sh := oracleSqrt(oracleFloat(w, big.ToPositiveInf).SetRat(sq), w, true)
		innerLo = new(big.Rat).Add(a, oracleFloatRat(sl))
		innerHi = new(big.Rat).Add(a, oracleFloatRat(sh))
	}
	l, _ := trigOracleLnRat(innerLo, prec)
	_, h := trigOracleLnRat(innerHi, prec)
	if kind == evalAtanh {
		l.Quo(l, big.NewRat(2, 1))
		h.Quo(h, big.NewRat(2, 1))
	}
	if x.Sign() < 0 {
		return neg(h), neg(l)
	}
	return l, h
}

// trigOracleLnRat encloses ln r for a rational r ≥ 1 with the power of ten
// kept symbolic.
func trigOracleLnRat(r *big.Rat, prec uint) (lo, hi *big.Rat) {
	k := int64(0)
	m := new(big.Rat).Set(r)
	ten := big.NewRat(10, 1)
	for m.Cmp(ten) >= 0 {
		m.Quo(m, ten)
		k++
	}
	lo, hi = oracleLnMantissa(m, prec+64)
	if k > 0 {
		tl, th := oracleLnTen(prec + 64)
		kr := big.NewRat(k, 1)
		lo.Add(lo, new(big.Rat).Mul(kr, tl))
		hi.Add(hi, new(big.Rat).Mul(kr, th))
	}
	return lo, hi
}

// trigCall runs one public context form.
func trigCall(kind evalKind, x, y Decimal, ctx Context) (Decimal, Conditions, error) {
	switch kind {
	case evalSin:
		return x.SinWithContext(ctx)
	case evalCos:
		return x.CosWithContext(ctx)
	case evalTan:
		return x.TanWithContext(ctx)
	case evalAsin:
		return x.AsinWithContext(ctx)
	case evalAcos:
		return x.AcosWithContext(ctx)
	case evalAtan:
		return x.AtanWithContext(ctx)
	case evalAtan2:
		return y.Atan2WithContext(x, ctx)
	case evalSinh:
		return x.SinhWithContext(ctx)
	case evalCosh:
		return x.CoshWithContext(ctx)
	case evalTanh:
		return x.TanhWithContext(ctx)
	case evalAsinh:
		return x.AsinhWithContext(ctx)
	case evalAcosh:
		return x.AcoshWithContext(ctx)
	default:
		return x.AtanhWithContext(ctx)
	}
}

var trigKinds = []evalKind{evalSin, evalCos, evalTan, evalAsin, evalAcos, evalAtan, evalAtan2, evalSinh, evalCosh, evalTanh, evalAsinh, evalAcosh, evalAtanh}

// trigRandomInput draws an operand of 1–12 digits in the kind's domain.
func trigRandomInput(rng *rand.Rand, kind evalKind) Decimal {
	digits := 1 + rng.IntN(12)
	c := int64(1)
	for range digits - 1 {
		c = 10*c + rng.Int64N(10)
	}
	var adj int
	switch kind {
	case evalAsin, evalAcos, evalAtanh:
		adj = -1 - rng.IntN(4)
	case evalAcosh:
		adj = rng.IntN(4)
	case evalSinh, evalCosh, evalTanh:
		adj = rng.IntN(5) - 3
	default:
		adj = rng.IntN(9) - 4
	}
	d := New(c, int32(adj-digits+1))
	if kind != evalAcosh && rng.IntN(2) == 0 {
		d = d.Neg()
	}
	return d
}

// TestTrigonometricMatchesOracleInEveryMode checks that all rounding modes
// certify the thirteen functions against the independent oracle.
func TestTrigonometricMatchesOracleInEveryMode(t *testing.T) {
	rng := rand.New(rand.NewPCG(67, 1))
	for _, kind := range trigKinds {
		t.Run(fmt.Sprint(kind), func(t *testing.T) { trigDifferential(t, rng, kind) })
	}
}

func trigDifferential(t *testing.T, rng *rand.Rand, kind evalKind) {
	{
		checked := 0
		for i := range 24 {
			x := trigRandomInput(rng, kind)
			y := trigRandomInput(rng, evalAtan)
			if kind == evalAcosh && x.Equal(One()) {
				x = New(2, 0) // Acosh(1) is the exact case, tested separately
			}
			p := uint32(1 + rng.IntN(24))
			mode := inexactModes[i%len(inexactModes)]
			xr, yr := oracleRat(x), oracleRat(y)
			want := oracleDecide(t, func(prec uint) (*big.Rat, *big.Rat) {
				lo, hi := trigOracle(kind, xr, yr, prec)
				if lo == nil {
					return big.NewRat(-1, 1), big.NewRat(1, 1) // undecided: refine
				}
				return lo, hi
			}, int64(p), mode)
			got, c, err := trigCall(kind, x, y, mustContext(t, p, mode))
			oracleMatch(t, fmt.Sprintf("kind %d (%s, %s) p=%d %v", kind, x, y, p, mode), got, c, err, want)
			checked++
		}
		if checked < 24 {
			t.Fatalf("kind %d: only %d cases", kind, checked)
		}
	}
}

// TestTrigonometricOracleSelfChecks pins the oracle on published values.
func TestTrigonometricOracleSelfChecks(t *testing.T) {
	check := func(name string, lo, hi *big.Rat, want string) {
		t.Helper()
		r, ok := enclosureRound(lo, hi, 20, TowardZero)
		if !ok || r.String() != want {
			t.Fatalf("%s: %v %v, want %s", name, r, ok, want)
		}
	}
	pl, ph := trigOraclePi(200)
	check("π", pl, ph, "+31415926535897932384E-19")
	sl, sh, cl, ch := trigOracleSinCos(big.NewRat(1, 1), 200)
	check("sin 1", sl, sh, "+84147098480789650665E-20")
	check("cos 1", cl, ch, "+54030230586813971740E-20")
	lo, hi := trigOracleAtan(big.NewRat(1, 2), 200)
	check("atan 1/2", lo, hi, "+46364760900080611621E-20")
	lo, hi = trigOracleHyper(evalSinh, big.NewRat(1, 1), 200)
	check("sinh 1", lo, hi, "+11752011936438014568E-19")
}

// TestTrigonometricExactCasesAndDomains covers exact cases, domains
// and exact-context refusals.
func TestTrigonometricExactCasesAndDomains(t *testing.T) {
	zero, one := Zero(), One()
	for _, tc := range []struct {
		kind evalKind
		x, y Decimal
		want string
	}{
		{evalSin, zero, zero, "0"}, {evalCos, zero, zero, "1"}, {evalTan, New(0, -5), zero, "0"},
		{evalAsin, zero, zero, "0"}, {evalAcos, one, zero, "0"}, {evalAcos, New(100, -2), zero, "0"},
		{evalAtan, zero, zero, "0"}, {evalAtan2, New(5, 0), zero, "0"}, {evalSinh, zero, zero, "0"},
		{evalCosh, zero, zero, "1"}, {evalTanh, zero, zero, "0"}, {evalAsinh, zero, zero, "0"},
		{evalAcosh, one, zero, "0"}, {evalAtanh, zero, zero, "0"},
	} {
		for _, ctx := range []Context{{}, mustContext(t, 3, Exact), Decimal64Context()} {
			got, c, err := trigCall(tc.kind, tc.x, tc.y, ctx)
			if err != nil || got.String() != tc.want || got.Exponent() != 0 || c != 0 {
				t.Fatalf("kind %d exact: %s E%d %v %v", tc.kind, got, got.Exponent(), c, err)
			}
		}
	}
	for _, tc := range []struct {
		kind evalKind
		x, y Decimal
		err  error
	}{
		{evalAsin, New(11, -1), zero, ErrInvalidOperation}, {evalAcos, New(-2, 0), zero, ErrInvalidOperation},
		{evalAtanh, one, zero, ErrDivisionByZero}, {evalAtanh, one.Neg(), zero, ErrDivisionByZero},
		{evalAtanh, New(2, 0), zero, ErrInvalidOperation}, {evalAcosh, New(9, -1), zero, ErrInvalidOperation},
		{evalAcosh, New(-5, 0), zero, ErrInvalidOperation}, {evalAtan2, zero, zero, ErrInvalidOperation},
	} {
		_, c, err := trigCall(tc.kind, tc.x, tc.y, mustContext(t, 9, TiesToEven))
		var oe *Error
		if !errors.Is(err, tc.err) || !errors.As(err, &oe) || c != 0 {
			t.Fatalf("kind %d domain: %v", tc.kind, err)
		}
	}
	var ce *Error
	for _, kind := range trigKinds {
		x := New(5, -1)
		if kind == evalAcosh {
			x = New(2, 0)
		}
		_, _, err := trigCall(kind, x, One(), Context{})
		if !errors.As(err, &ce) || ce.Code != 0 || ce.Condition != Inexact || ce.Remedy != elementaryRemedy(kind) || ce.Remedy == "" {
			t.Fatalf("kind %d bare refusal: %v", kind, err)
		}
		if _, _, err := trigCall(kind, x, One(), mustContext(t, 9, Exact)); !errors.Is(err, ErrInexact) {
			t.Fatalf("kind %d Exact: %v", kind, err)
		}
	}
	// Domain edges are valid and inexact: Asin(±1) = ±π/2, Acos(−1) = π.
	for _, tc := range []struct {
		kind evalKind
		x    Decimal
		want string
	}{{evalAsin, One(), "1.570796326794897"}, {evalAsin, One().Neg(), "-1.570796326794897"}, {evalAcos, One().Neg(), "3.141592653589793"}} {
		got, c, err := trigCall(tc.kind, tc.x, Zero(), mustContext(t, 16, TiesToEven))
		if err != nil || got.String() != tc.want || c&Inexact == 0 {
			t.Fatalf("kind %d at %s = %s %v %v", tc.kind, tc.x, got, c, err)
		}
	}
	// The negative x-axis is +π, the vertical axis ±π/2.
	for _, tc := range []struct {
		y, x Decimal
		want string
	}{
		{zero, New(-5, 0), "3.141592653589793"}, {New(3, 0), zero, "1.570796326794897"}, {New(-3, 0), zero, "-1.570796326794897"},
	} {
		got, c, err := tc.y.Atan2WithContext(tc.x, mustContext(t, 16, TiesToEven))
		if err != nil || got.String() != tc.want || c&Inexact == 0 {
			t.Fatalf("atan2(%s, %s) = %s %v %v", tc.y, tc.x, got, c, err)
		}
	}
}

// TestTrigonometricTinyArguments covers tiny arguments: every odd
// function and Cos/Cosh settle a tiny operand in one stage through the
// one-sided filters, with the displacement's direction.
func TestTrigonometricTinyArguments(t *testing.T) {
	ctx := mustContext(t, 16, TowardZero)
	for _, s := range []string{"1E-1000000", "-3E-2147483000", "1.25E-400"} {
		x, _ := Parse(s)
		for _, kind := range trigKinds {
			if kind == evalAcos || kind == evalAcosh || kind == evalAtan2 {
				continue
			}
			ev := newEvaluator(Budget{MaxWork: 1 << 24})
			got, c, err := ev.elementary(kind, x, Zero(), ctx, "tiny")
			if err != nil || ev.stages != 1 {
				t.Fatalf("kind %d at %s: %v after %d stages", kind, s, err, ev.stages)
			}
			// Toward zero: functions above their center keep it, below drop one unit.
			var above bool
			switch kind {
			case evalTan, evalSinh, evalAsin, evalAtanh, evalCosh:
				above = true
			}
			center := x.Abs()
			if kind == evalCos || kind == evalCosh {
				center = One()
			}
			mag := got.Abs()
			if above {
				if mag.Compare(center) != 0 || c != Inexact|Rounded|roundingDirection(false, got.negative()) {
					t.Fatalf("kind %d at %s = %s %v", kind, s, got, c)
				}
			} else if mag.Compare(center) >= 0 || c&Inexact == 0 {
				t.Fatalf("kind %d at %s = %s %v", kind, s, got, c)
			}
		}
	}
	// Acos near zero is π/2 − x: no filter, but 1 ± x must stay admitted.
	for _, tc := range []struct {
		x   string
		ctx Context
	}{{"1E-200", Decimal64Context()}, {"-1E-500", mustContext(t, 16, TiesToEven)}, {"1E-6000", Decimal128Context()}, {"1E-2147483648", mustContext(t, 16, TowardZero)}} {
		x, _ := Parse(tc.x)
		got, c, err := x.AcosWithContext(tc.ctx)
		p := int64(tc.ctx.Precision())
		want := oracleDecide(t, func(prec uint) (*big.Rat, *big.Rat) {
			pl, ph := trigOraclePi(prec + 16)
			half := big.NewRat(1, 2)
			// |acos x − π/2| = |asin x| ≤ |x| + |x|³ < 10^−199 for these
			// |x| ≤ 10^−200 (1E−2147483648 has no big.Rat form).
			slack := new(big.Rat).SetFrac(big.NewInt(1), new(big.Int).Exp(big.NewInt(10), big.NewInt(199), nil))
			return new(big.Rat).Sub(new(big.Rat).Mul(pl, half), slack), new(big.Rat).Add(new(big.Rat).Mul(ph, half), slack)
		}, p, tc.ctx.Rounding())
		oracleMatch(t, "Acos("+tc.x+")", got, c, err, want)
	}
	// Unguarded, a p-digit result below 1E−2147483648 has no stored exponent.
	if _, _, err := New(1, -2147483648).SinWithContext(mustContext(t, 16, TiesToEven)); !errors.Is(err, ErrExponentRange) {
		t.Fatalf("Sin(1E-2147483648): %v", err)
	}
	got, c, err := New(1, -2147483648).SinWithContext(Decimal64Context())
	if err != nil || !got.isZero() || c != Subnormal|Underflow|Inexact|Rounded|Decreased {
		t.Fatalf("guarded tiny: %s %v %v", got, c, err)
	}
}

// TestTrigonometricLargeArgumentsAndSaturation covers huge
// reduction and saturation: reductions of hundreds of digits certify
// against the oracle; a finite quota refuses 1E+2000000000 before its π
// arena exists; Tanh saturates below one; huge Asinh and Acosh are small
// computations.
func TestTrigonometricLargeArgumentsAndSaturation(t *testing.T) {
	// π/2, π and 2π to 70 digits put the reduced interval next to zero, where
	// cos peaks (its enclosure must not assume monotonicity).
	for _, s := range []string{"1E+300", "-7.25E+120", "1.5707963267948966192313216916397514420985846996875529104874722962",
		"3.141592653589793238462643383279502884197169399375105820974944592307816",
		"6.283185307179586476925286766559005768394338798750211641949889184615633",
		// (10^20+1)·π/2 and (10^40+3)·π/2 to about 80 fractional digits.
		"157079632679489661924.70296549077004082908979166039504249084581431507837322479792222755564947",
		"15707963267948966192313216916397514420990.5593858559137947324169266140012857573407472392367854420477567992"} {
		x, _ := Parse(s)
		for _, kind := range []evalKind{evalSin, evalCos, evalTan} {
			want := oracleDecide(t, func(prec uint) (*big.Rat, *big.Rat) {
				lo, hi := trigOracle(kind, oracleRat(x), nil, prec)
				if lo == nil {
					return big.NewRat(-1, 1), big.NewRat(1, 1)
				}
				return lo, hi
			}, 16, TiesToEven)
			got, c, err := trigCall(kind, x, Zero(), mustContext(t, 16, TiesToEven))
			oracleMatch(t, fmt.Sprintf("kind %d at %s", kind, s), got, c, err, want)
		}
	}
	// π at Lq limbs certifies a 300-digit reduction in one stage.
	ev := newEvaluator(Budget{})
	if _, _, err := ev.elementary(evalSin, New(1, 300), Zero(), mustContext(t, 16, TiesToEven), "stages"); err != nil || ev.stages != 1 {
		t.Fatalf("Sin(1E+300): %v after %d stages", err, ev.stages)
	}
	huge := New(1, 2000000000)
	w := uint64(1 << 22)
	bound, _ := BoundEvaluation(Budget{MaxWork: w})
	var err error
	used := coldAllocatedWithin(func() {
		_, _, err = huge.SinWithContext(mustContext(t, 16, TiesToEven).WithBudget(Budget{MaxWork: w}))
	}, bound.HeapBytes)
	var limit *Error
	if !errors.As(err, &limit) || limit.Resource == 0 || used > 1<<20 {
		t.Fatalf("Sin(1E+2000000000) at W=%d: %v after %d bytes", w, err, used)
	}
	for _, tc := range []struct {
		mode RoundingMode
		want string
		c    Conditions
	}{{TiesToEven, "1.000000000000000", Inexact | Rounded | Increased}, {TowardZero, "0.9999999999999999", Inexact | Rounded | Decreased}} {
		// 1E+9 stays in exp's range; 1E+11 and beyond saturate from the
		// range filter.
		for _, x := range []Decimal{New(1, 9), New(1, 11), New(1, 2147483647)} {
			got, c, err := x.TanhWithContext(mustContext(t, 16, tc.mode))
			if err != nil || got.String() != tc.want || c != tc.c {
				t.Fatalf("Tanh(%s) %v = %s %v %v", x, tc.mode, got, c, err)
			}
		}
	}
	// asinh a ∈ (ln 2a, ln 2a + 1/(4a²)] and acosh a ∈ (ln 2a − 1/a², ln 2a).
	a := New(1, 2000)
	for _, kind := range []evalKind{evalAsinh, evalAcosh} {
		want := oracleDecide(t, func(prec uint) (*big.Rat, *big.Rat) {
			lo, hi := oracleLn(New(2, 2000), prec)
			slack := new(big.Rat).SetFrac(big.NewInt(1), new(big.Int).Exp(big.NewInt(10), big.NewInt(3999), nil))
			if kind == evalAsinh {
				return lo, hi.Add(hi, slack)
			}
			return lo.Sub(lo, slack), hi
		}, 16, TiesToEven)
		got, c, err := trigCall(kind, a, Zero(), mustContext(t, 16, TiesToEven))
		oracleMatch(t, fmt.Sprintf("kind %d at 1E+2000", kind), got, c, err, want)
	}
	// Sinh and Cosh beyond the range filter overflow under guards.
	for _, kind := range []evalKind{evalSinh, evalCosh} {
		got, c, err := trigCall(kind, New(-1, 12), Zero(), Decimal64Context())
		wantSign := kind == evalSinh
		if err != nil || c&Overflow == 0 || got.negative() != wantSign {
			t.Fatalf("kind %d at -1E+12: %s %v %v", kind, got, c, err)
		}
	}
}

// TestTrigonometricSharedLedgerAndInventory covers the budget of the
// trigonometric functions:
// nested reductions, square roots and logarithms debit one quota, and the
// heap holds only admitted arenas and the published holder.
func TestTrigonometricSharedLedgerAndInventory(t *testing.T) {
	x := New(12345, -2)
	for _, kind := range []evalKind{evalSin, evalAsin, evalAsinh, evalAtan2, evalAcosh} {
		arg := x
		switch kind {
		case evalAsin:
			arg = New(7, -1)
		case evalAcosh:
			arg = New(3, 0)
		}
		ev := newEvaluator(Budget{MaxWork: 1 << 22})
		_, _, err := ev.elementary(kind, arg, New(-2, 0), mustContext(t, 30, TiesToEven), "ledger")
		if err != nil || ev.meter.spent > 1<<22 || ev.meter.spent != (1<<22)-ev.meter.remaining {
			t.Fatalf("kind %d: %v spent %d", kind, err, ev.meter.spent)
		}
		var objects uint64
		n := testing.AllocsPerRun(10, func() {
			e := newEvaluator(Budget{})
			if _, _, err := e.elementary(kind, arg, New(-2, 0), mustContext(t, 16, TiesToEven), "inventory"); err != nil {
				t.Fatal(err)
			}
			objects = e.objects
		})
		if uint64(n) != objects {
			t.Fatalf("kind %d: %v allocations, %d admitted arenas", kind, n, objects)
		}
	}
}

// TestAlternatingSeriesEnclosesAcrossLimbBoundary checks the
// alternating-series primitive's tail bound. For a
// decreasing term sequence t_j = F·r^j/d_j (d_j = (2j)!, (2j+1)! or 2j+1)
// chosen so that S_1 = F − t_1 < 1 ≤ S_2 = S_1 + t_2 ≈ 1 + t_3/4 and
// t_1 ≥ 10^−18 (one unit of S_1 at W = 2) while t_2 < 10^−9 (one unit of a
// sum ≥ 1), the lower sum at L = 1 continues past t_1 and stops right
// after t_2 on exactly one, a power of 10⁹ it crossed upward, while the
// value lies below S_4 < 1 (all asserted):
// only the tail brings the lower bound under it. The exact partial sums
// S_5 ≤ value ≤ S_6 are the oracle.
func TestAlternatingSeriesEnclosesAcrossLimbBoundary(t *testing.T) {
	ev := newEvaluator(Budget{})
	size := 32
	st := evalStage{ar: ev.arena(uint64(size * 32)), L: 2, size: size}
	for _, c := range []struct {
		kind int
		F, r string
	}{
		{seriesCosine, "1.000075", "0.0001499906256069909109360792357736825613"},
		{seriesCosine, "1.00005", "0.0000999958335131864760543478980603459861"},
		{seriesCosine, "1.00002", "0.0000399993333448442404481299571367253158"},
		{seriesSine, "1.00002", "0.0001199983200273252449226086558828513211"},
		{seriesSine, "1.00001", "0.0000599995800034156849502600942787601843"},
		{seriesAtan, "1.00002", "0.0000600009600699811435938051968742809978"},
		{seriesAtan, "1.00001", "0.0000300002400087473928944489544545372024"},
	} {
		F, r := MustParse(c.F), MustParse(c.r)
		Fr, rr := oracleRat(F), oracleRat(r)
		// S_n = Σ_{j≤n} (−1)^j t_j exactly.
		S, T := make([]*big.Rat, 7), make([]*big.Rat, 7) // partial sums, term magnitudes
		sum, pow := new(big.Rat), new(big.Rat).Set(Fr)
		den := big.NewInt(1)
		for j := range int64(7) {
			if j > 0 {
				pow.Mul(pow, rr)
				switch c.kind {
				case seriesCosine:
					den.Mul(den, big.NewInt((2*j-1)*(2*j)))
				case seriesSine:
					den.Mul(den, big.NewInt((2*j)*(2*j+1)))
				default:
					den.SetInt64(2*j + 1)
				}
			}
			term := new(big.Rat).Quo(pow, new(big.Rat).SetInt(den))
			T[j] = new(big.Rat).Set(term)
			if j%2 == 1 {
				term.Neg(term)
			}
			S[j] = new(big.Rat).Set(sum.Add(sum, term))
		}
		one := big.NewRat(1, 1)
		if S[1].Cmp(one) >= 0 || S[2].Cmp(one) < 0 || S[4].Cmp(one) >= 0 {
			t.Fatalf("kind %d F=%s: S_1, S_2, S_4 = %s, %s, %s do not cross one", c.kind, c.F, S[1].FloatString(20), S[2].FloatString(20), S[4].FloatString(20))
		}
		// The loop continues after t_1 (at least one unit 10^−18 of S_1 < 1)
		// and stops right after t_2 (below one unit 10^−9 of a sum ≥ 1).
		if T[1].Cmp(big.NewRat(1, 1e18)) < 0 || T[2].Cmp(big.NewRat(1, 1e9)) >= 0 {
			t.Fatalf("kind %d F=%s: t_1 = %s, t_2 = %s miss the stop window", c.kind, c.F, T[1].FloatString(25), T[2].FloatString(25))
		}
		mark := st.scope()
		fv, rv := coefficientViewOf(F), coefficientViewOf(r)
		fd, _ := arithmeticDigits(&fv)
		rd, _ := arithmeticDigits(&rv)
		first := ev.load(st.buf(&ev), &fv, fd, int64(F.exponent()), false, 8, false)
		ratio := ev.load(st.buf(&ev), &rv, rd, int64(r.exponent()), false, 8, false)
		lo := ev.alternatingSeries(&st, st.buf(&ev), first, ratio, ratio, c.kind, 1, false)
		hi := ev.alternatingSeries(&st, st.buf(&ev), first, ratio, ratio, c.kind, 1, true)
		if !ev.ok() || enclosureRat(lo).Cmp(S[5]) > 0 || enclosureRat(hi).Cmp(S[6]) < 0 {
			t.Fatalf("kind %d F=%s r=%s: [%s, %s] excludes [S_5, S_6] = [%s, %s] (%+v)", c.kind, c.F, c.r,
				enclosureRat(lo).FloatString(30), enclosureRat(hi).FloatString(30), S[5].FloatString(30), S[6].FloatString(30), ev.status)
		}
		st.restore(mark)
	}
}

// TestCosineEnclosesWideReducedIntervals covers arguments longer than the first
// stage's L+2 = 6 limbs: x = 10^45 + k + 1/2 loads as [10^45 + k, 10^45 + k +
// 1], so the reduced interval is about [−1/2, 1/2] around a true r = x − mπ
// near zero, and cos is not monotone on it. The first stage must enclose cos
// over the whole interval (its maximum is one); treating cos as monotone there
// encloses cos(1/2) instead, which certifies a wrong result for k = 331 and 686
// (r ≈ +0.002) and an inverted enclosure for k = 57464 and 57819 (r ≈ −0.002).
func TestCosineEnclosesWideReducedIntervals(t *testing.T) {
	for _, k := range []int64{331, 686, 57464, 57819} {
		x := MustParse(fmt.Sprintf("1%045d.5", k))
		xr := oracleRat(x)
		// The guard: the first stage's reduced interval straddles zero and
		// is wider than one half.
		ev := newEvaluator(Budget{})
		L := evalStageLimbs(evalFirstDigits(4)) // the first stage for p ≤ 16
		var al, ah, rl, rh [16]uint32
		xv := coefficientViewOf(x)
		xd, _ := arithmeticDigits(&xv)
		alo := ev.load(al[:], &xv, xd, int64(x.exponent()), false, L+2, false)
		ahi := ev.load(ah[:], &xv, xd, int64(x.exponent()), false, L+2, true)
		rlo, rhi, _, ok := ev.reduce(rl[:], rh[:], alo, ahi, L)
		if !ok || !ev.ok() || !rlo.neg || rhi.neg || new(big.Rat).Sub(enclosureRat(rhi), enclosureRat(rlo)).Cmp(big.NewRat(1, 2)) <= 0 {
			t.Fatalf("x=%s: stage-one reduced interval [%s, %s] does not straddle zero widely", x, enclosureRat(rlo).FloatString(6), enclosureRat(rhi).FloatString(6))
		}
		for p := uint32(1); p <= 4; p++ {
			for _, mode := range inexactModes {
				want := oracleDecide(t, func(prec uint) (*big.Rat, *big.Rat) {
					return trigOracle(evalCos, xr, nil, prec)
				}, int64(p), mode)
				got, c, err := x.CosWithContext(mustContext(t, p, mode))
				oracleMatch(t, fmt.Sprintf("Cos(%s) p=%d %v", x, p, mode), got, c, err, want)
			}
		}
	}
}

// TestTrigonometricKernelsEncloseOracle checks the trigonometric kernels
// behind the correct-rounding guarantee at one to four limbs: sinDirected
// and cosDirected (the alternating Taylor series with its tail) for exact
// 0 < |a| ≤ 0.8, and atanDirected (odd symmetry, π/2 − atan(1/a) above
// one, two half-angle steps and the series) for 0 < |a| ≤ 30, must
// enclose the independent oracle (trigOracle: sin and cos from
// the exact-rational Taylor polynomial of e^{ir}, atan from the π/4 split)
// from the requested side, and each enclosure must be narrow: at most two
// units of its L-th limb for sin and cos (observed: one) and four for
// atan, which composes π, a reciprocal, two half-angle steps and a
// scaling (observed: two), so a loose or reversed bound cannot pass by
// containment alone. At least 200 sin, 200 cos and 2000 atan cases run or
// the test is vacuous.
func TestTrigonometricKernelsEncloseOracle(t *testing.T) {
	rng := rand.New(rand.NewPCG(67, 9))
	ev := newEvaluator(Budget{})
	size := 64
	st := evalStage{ar: ev.arena(uint64(size * 64)), L: 4, size: size}
	checked := [3]int{}
	worst := [3]*big.Rat{new(big.Rat), new(big.Rat), new(big.Rat)}
	for i := range 3000 {
		L := 1 + i%4
		k := 1 + rng.IntN(12)
		n := 1 + rng.Int64N(int64(30*decimalPowers[min(k, 8)]))
		if rng.IntN(2) == 0 {
			n = -n
		}
		a := New(n, -int32(k))
		av := coefficientViewOf(a)
		ad, _ := arithmeticDigits(&av)
		mark := st.scope()
		x := ev.load(st.buf(&ev), &av, ad, int64(a.exponent()), a.negative(), 8, false)
		xr := enclosureRat(x)
		check := func(name string, j int, units int64, lo, hi evalNum, olo, ohi *big.Rat) {
			t.Helper()
			if olo == nil || enclosureRat(lo).Cmp(olo) > 0 || enclosureRat(hi).Cmp(ohi) < 0 {
				t.Fatalf("%s(%s) at L=%d: [%s, %s] excludes the oracle", name, xr.FloatString(20), L,
					enclosureRat(lo).FloatString(40), enclosureRat(hi).FloatString(40))
			}
			width := new(big.Rat).Quo(new(big.Rat).Sub(enclosureRat(hi), enclosureRat(lo)), enclosureUnit(hi, L))
			if width.Cmp(worst[j]) > 0 {
				worst[j] = width
			}
			if width.Cmp(big.NewRat(units, 1)) > 0 {
				t.Fatalf("%s(%s) at L=%d: [%s, %s] is wider than %d units of the L-th limb", name, xr.FloatString(20), L,
					enclosureRat(lo).FloatString(40), enclosureRat(hi).FloatString(40), units)
			}
			checked[j]++
		}
		if new(big.Rat).Abs(xr).Cmp(big.NewRat(4, 5)) <= 0 {
			for j, kind := range []evalKind{evalSin, evalCos} {
				olo, ohi := trigOracle(kind, xr, nil, 200)
				kernel := []func(*evalStage, []uint32, evalNum, int, bool) evalNum{ev.sinDirected, ev.cosDirected}[j]
				lo := kernel(&st, st.buf(&ev), x, L, false)
				hi := kernel(&st, st.buf(&ev), x, L, true)
				check([]string{"sin", "cos"}[j], j, 2, lo, hi, olo, ohi)
			}
		}
		olo, ohi := trigOracle(evalAtan, xr, nil, 200)
		lo := ev.atanDirected(&st, st.buf(&ev), x, L, false)
		hi := ev.atanDirected(&st, st.buf(&ev), x, L, true)
		check("atan", 2, 4, lo, hi, olo, ohi)
		st.restore(mark)
	}
	if !ev.ok() {
		t.Fatalf("status %+v", ev.status)
	}
	t.Logf("checked sin %d, cos %d, atan %d; widest %s, %s, %s units", checked[0], checked[1], checked[2],
		worst[0].FloatString(3), worst[1].FloatString(3), worst[2].FloatString(3))
	if checked[0] < 200 || checked[1] < 200 || checked[2] < 2000 {
		t.Fatalf("checked sin %d, cos %d, atan %d cases: the check is vacuous", checked[0], checked[1], checked[2])
	}
}

// TestTrigonometricKernelsEncloseBesideLimbBoundaries checks the
// trigonometric kernels where a sub-unit error decides the bound, which
// TestTrigonometricKernelsEncloseOracle's random arguments rarely reach.
// For each
// L = 1..4 and a few targets, g is the L-limb grid point at the target and
// a runs over the grid of one unit of g's (L+1)-th limb, on which f moves
// by less than that unit (|f′| ≤ 1); bisection with the independent
// oracle finds the neighbours a with f(a) just above and just below
// g, within one unit of the (L+1)-th limb (asserted). sinDirected,
// cosDirected and atanDirected (series only, one or two half-angle steps,
// and π/2 − atan(1/a)) must enclose the oracle there from both sides within
// the widths of TestTrigonometricKernelsEncloseOracle, so a guard-limb
// rounding in the wrong direction, which only such a value exposes, fails.
func TestTrigonometricKernelsEncloseBesideLimbBoundaries(t *testing.T) {
	ev := newEvaluator(Budget{})
	size := 64
	st := evalStage{ar: ev.arena(uint64(size * 64)), L: 4, size: size}
	kernels := []struct {
		name    string
		kind    evalKind
		f       func(*evalStage, []uint32, evalNum, int, bool) evalNum
		seed    func(float64) float64 // approximate inverse
		rising  bool
		units   int64
		targets []float64
	}{
		{"sin", evalSin, ev.sinDirected, math.Asin, true, 2, []float64{0.0731, 0.6953}},
		{"cos", evalCos, ev.cosDirected, math.Acos, false, 2, []float64{0.7288, 0.9819}},
		{"atan", evalAtan, ev.atanDirected, math.Tan, true, 4, []float64{0.1437, 0.3162, 0.7071, 1.2345}},
	}
	witnesses := 0
	for L := 1; L <= 4; L++ {
		prec := uint(30*(L+2) + 64)
		for _, k := range kernels {
			for _, target := range k.targets {
				mark := st.scope()
				// g on the L-limb grid below the target; unit is one unit of
				// g's (L+1)-th limb and the grid of a.
				top := int64(0) // g's top limb: 10^(9(top−1)) ≤ g < 10^(9·top)
				if target >= 1 {
					top = 1
				}
				e := top - int64(L) - 1 // a = n·10^(9e)
				unit := new(big.Rat).SetFrac(big.NewInt(1), enclosurePow10(-e))
				unitL := new(big.Rat).Mul(unit, new(big.Rat).SetInt(enclosurePow10(1)))
				tr := new(big.Rat).Quo(new(big.Rat).SetFloat64(target), unitL)
				g := new(big.Rat).Mul(new(big.Rat).SetInt(new(big.Int).Quo(tr.Num(), tr.Denom())), unitL)
				gf, _ := g.Float64()
				// side reports +1 when f(n·unit) lies above g, −1 below.
				side := func(n *big.Int) int {
					lo, hi := trigOracle(k.kind, new(big.Rat).Mul(new(big.Rat).SetInt(n), unit), nil, prec)
					switch {
					case lo.Cmp(g) > 0:
						return 1
					case hi.Cmp(g) < 0:
						return -1
					}
					t.Fatalf("%s at L=%d: the oracle cannot place f(%s·unit) against %s", k.name, L, n, g.FloatString(9*(L+1)))
					return 0
				}
				n0, _ := new(big.Rat).Quo(new(big.Rat).SetFloat64(k.seed(gf)), unit).Float64()
				// Search n0 ± (10^−12/unit + 2), far beyond the seed's error.
				sr := new(big.Rat).Quo(big.NewRat(1, 1e12), unit)
				span := new(big.Int).Add(new(big.Int).Quo(sr.Num(), sr.Denom()), big.NewInt(2))
				nb, _ := new(big.Float).SetFloat64(n0).Int(nil)
				lo, hi := new(big.Int).Sub(nb, span), new(big.Int).Add(nb, span)
				dir := 1
				if !k.rising {
					dir = -1
				}
				if side(lo) != -dir || side(hi) != dir {
					t.Fatalf("%s at L=%d: the seed does not bracket %s", k.name, L, g.FloatString(9*(L+1)))
				}
				for new(big.Int).Sub(hi, lo).Cmp(big.NewInt(1)) > 0 {
					mid := new(big.Int).Rsh(new(big.Int).Add(lo, hi), 1)
					if side(mid) == dir {
						hi = mid
					} else {
						lo = mid
					}
				}
				for _, n := range []*big.Int{lo, hi} {
					xr := new(big.Rat).Mul(new(big.Rat).SetInt(n), unit)
					olo, ohi := trigOracle(k.kind, xr, nil, prec)
					gap := new(big.Rat).Sub(olo, g)
					if gap.Sign() < 0 {
						gap = new(big.Rat).Sub(g, ohi)
					}
					if gap.Sign() <= 0 || gap.Cmp(unit) >= 0 {
						t.Fatalf("%s(%s) at L=%d: not within one unit of the (L+1)-th limb beside %s", k.name,
							xr.FloatString(9*(L+2)), L, g.FloatString(9*(L+1)))
					}
					x := enclosureNum(st.buf(&ev), n, e)
					if enclosureRat(x).Cmp(xr) != 0 {
						t.Fatalf("argument %s loads as %s", xr.FloatString(9*(L+2)), enclosureRat(x).FloatString(9*(L+2)))
					}
					l, h := k.f(&st, st.buf(&ev), x, L, false), k.f(&st, st.buf(&ev), x, L, true)
					width := new(big.Rat).Quo(new(big.Rat).Sub(enclosureRat(h), enclosureRat(l)), enclosureUnit(h, L))
					if !ev.ok() || enclosureRat(l).Cmp(olo) > 0 || enclosureRat(h).Cmp(ohi) < 0 || width.Cmp(big.NewRat(k.units, 1)) > 0 {
						t.Fatalf("%s(%s) at L=%d beside %s: [%s, %s] excludes the oracle or is wider than %d units (%+v)", k.name,
							xr.FloatString(9*(L+2)), L, g.FloatString(9*(L+1)), enclosureRat(l).FloatString(9*(L+2)),
							enclosureRat(h).FloatString(9*(L+2)), k.units, ev.status)
					}
					witnesses++
				}
				st.restore(mark)
			}
		}
	}
	if witnesses != 2*4*8 {
		t.Fatalf("%d witnesses, want %d", witnesses, 2*4*8)
	}
}
