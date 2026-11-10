// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"errors"
	"hash/maphash"
	"math"
	"math/big"
	"math/bits"
	"math/rand"
	randv2 "math/rand/v2"
	"slices"
	"strconv"
	"strings"
	"testing"
)

// inlineSample draws an inline Decimal whose magnitude bit length is spread
// across 0..128 and whose exponent lies within 45 of base. Pairs share a base,
// so aligned limb results stay small even at the int32 exponent extremes.
func inlineSample(r *rand.Rand, base int32) Decimal {
	var w uint128
	switch bitsLen := r.Intn(130); {
	case bitsLen == 0:
	case bitsLen <= 64:
		w.lo = r.Uint64() >> (64 - bitsLen)
	case bitsLen <= 128:
		w.lo, w.hi = r.Uint64(), r.Uint64()>>(128-bitsLen)
	default:
		w = uint128{math.MaxUint64, math.MaxUint64}
	}
	if r.Intn(8) == 0 {
		// Powers of ten and their neighbours stress digit-length boundaries.
		k := r.Intn(20)
		w = uint128{pow10Words[k] - uint64(r.Intn(2)), 0}
	}
	exponent := base + int32(r.Intn(91)-45)
	return inlineDecimal(w, exponent, w != (uint128{}) && r.Intn(2) == 0)
}

// asSlowBand presents a nonzero value through slow limbs, a non-canonical
// carrier that the general paths accept, to force them in differentials.
func asSlowBand(d Decimal) Decimal {
	v := coefficientViewOf(d)
	limbs := make([]uint32, v.count)
	for i := range v.count {
		limbs[i] = v.limb(i)
	}
	return slowDecimal(&slowCoefficient{limbs: limbs}, d.exponent(), d.negative())
}

func sameRepresentation(a, b Decimal) bool {
	if !a.validRepresentation() || !b.validRepresentation() {
		return false
	}
	if a.words != b.words || a.exponent() != b.exponent() || a.negative() != b.negative() || (a.slow == nil) != (b.slow == nil) {
		return false
	}
	if a.slow == nil {
		return true
	}
	if len(a.slow.limbs) != len(b.slow.limbs) {
		return false
	}
	for i := range a.slow.limbs {
		if a.slow.limbs[i] != b.slow.limbs[i] {
			return false
		}
	}
	return true
}

// TestInlineQuantizeHalfMapping checks the half mapping over every cut 1-19,
// mode, sign, quotient parity and decimal guard/sticky equivalence class.
// math/big doubling independently distinguishes below, equal and above half.
func TestInlineQuantizeHalfMapping(t *testing.T) {
	checks := 0
	for cut := 1; cut <= 19; cut++ {
		divisor := new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(cut)), nil)
		step := new(big.Int).Quo(new(big.Int).Set(divisor), big.NewInt(10))
		for guard := uint32(0); guard <= 9; guard++ {
			low := []*big.Int{big.NewInt(0)}
			if cut > 1 {
				low = append(low, big.NewInt(1), new(big.Int).Sub(step, big.NewInt(1)))
			}
			for _, tail := range low {
				r := new(big.Int).Mul(new(big.Int).SetUint64(uint64(guard)), step)
				r.Add(r, tail)
				mappedGuard, mappedSticky := uint32(0), false
				half := new(big.Int).Lsh(new(big.Int).Set(r), 1).Cmp(divisor)
				if r.Sign() != 0 {
					mappedGuard = 1
					if half >= 0 {
						mappedGuard, mappedSticky = 5, half > 0
					}
				}
				for mode := TiesToEven; mode <= Exact; mode++ {
					for _, negative := range []bool{false, true} {
						for parity := uint32(0); parity <= 1; parity++ {
							want := false
							inexact := r.Sign() != 0
							switch mode {
							case TiesToEven:
								want = half > 0 || half == 0 && parity == 1
							case TiesAwayFromZero:
								want = half >= 0
							case TiesTowardZero:
								want = half > 0
							case TowardZero, Exact:
							case AwayFromZero:
								want = inexact
							case TowardPositiveInfinity:
								want = inexact && !negative
							case TowardNegativeInfinity:
								want = inexact && negative
							}
							direct := contextRoundUp(mode, negative, guard, tail.Sign() != 0, parity)
							mapped := contextRoundUp(mode, negative, mappedGuard, mappedSticky, parity)
							if direct != want || mapped != want {
								t.Fatalf("cut%d guard%d tail%s mode%v negative%v parity%d: direct%v mapped%v oracle%v", cut, guard, tail, mode, negative, parity, direct, mapped, want)
							}
							checks++
						}
					}
				}
			}
		}
	}
	if checks != 17600 {
		t.Fatalf("checked %d half-mapping classes; want 17600", checks)
	}
	t.Logf("half mapping: %d exhaustive guard/sticky/parity/mode/sign classes over all 19 cuts", checks)
}

// TestInlineFastPathsMatchLimbPaths pins each unbudgeted inline fast path to
// the general limb path, which the math/big oracle tests validate separately.
// A fast-path result must be representation-identical; a fallback is allowed
// only where the exact result or an operand scaling leaves 128 bits.
// It additionally pins directed alignment classes to an independent
// signed math/big coefficient oracle and counts actual fast-path outcomes.
func TestInlineFastPathsMatchLimbPaths(t *testing.T) {
	t.Run("alignment boundaries", func(t *testing.T) {
		var equal, oneWord, wideScale, deferred int
		max128 := uint128{math.MaxUint64, math.MaxUint64}
		pairs := [][2]Decimal{
			{inlineDecimal(uint128{math.MaxUint64, 0}, 0, false), One()},
			{inlineDecimal(max128, 0, false), One()},
			{inlineDecimal(uint128{0, 1}, -2, false), One()},
			{New(123, -2), New(123, -2)},
			{New(0, math.MaxInt32), New(0, math.MinInt32)},
			{New(0, math.MaxInt32), New(-7, math.MinInt32)},
			{New(7, math.MinInt32), New(0, math.MaxInt32)},
		}
		for _, shift := range []int32{0, 1, 18, 19, 20, 37, 38, 39} {
			for _, words := range []uint128{{}, {1, 0}, {math.MaxUint64, 0}, {0, 1}, max128} {
				for _, base := range []int32{math.MinInt32, -19, math.MaxInt32 - 39} {
					pairs = append(pairs, [2]Decimal{inlineDecimal(words, base+shift, words != (uint128{})), New(1, base)})
				}
			}
		}
		magnitude := func(d Decimal, exponent int32) *big.Int {
			n := new(big.Int).SetUint64(d.words.hi)
			n.Lsh(n, 64).Or(n, new(big.Int).SetUint64(d.words.lo))
			// Zero needs no expansion, including a full int32 exponent gap.
			if n.Sign() != 0 {
				n.Mul(n, new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(d.exponent())-int64(exponent)), nil))
			}
			return n
		}
		for _, pair := range pairs {
			for _, operands := range [][2]Decimal{pair, {pair[1], pair[0]}} {
				a, b := operands[0], operands[1]
				e := min(a.exponent(), b.exponent())
				am, bm := magnitude(a, e), magnitude(b, e)
				for _, subtract := range []bool{false, true} {
					x, y := new(big.Int).Set(am), new(big.Int).Set(bm)
					if a.negative() {
						x.Neg(x)
					}
					if b.negative() != subtract {
						y.Neg(y)
					}
					want := x.Add(x, y)
					fits := am.BitLen() <= 128 && bm.BitLen() <= 128 && want.BitLen() <= 128
					got, ok := inlineAddSub(a, b, subtract)
					if ok != fits {
						t.Fatalf("alignment (%#v, %#v, subtract=%v): ok=%v, independent fit=%v", a, b, subtract, ok, fits)
					}
					general, err := a.addSubLimbs(b, limits{}, "alignment", subtract)
					if err != nil {
						t.Fatal(err)
					}
					assertOracleParts(t, general, want, e)
					var public Decimal
					if subtract {
						public, err = a.Sub(b)
					} else {
						public, err = a.Add(b)
					}
					if err != nil || !sameRepresentation(public, general) {
						t.Fatalf("public alignment differs: %#v / %#v, %v", public, general, err)
					}
					if !ok {
						deferred++
						continue
					}
					assertOracleParts(t, got, want, e)
					if !sameRepresentation(got, general) {
						t.Fatal("inline and general alignment representations differ")
					}
					if a.exponent() == b.exponent() {
						equal++
					}
					for _, d := range operands {
						shift := int64(d.exponent()) - int64(e)
						if d.words != (uint128{}) && shift > 0 {
							if d.words.hi == 0 && shift <= 19 {
								oneWord++
							} else {
								wideScale++
							}
						}
					}
				}
			}
		}
		if equal < 30 || oneWord < 30 || wideScale < 30 || deferred < 30 {
			t.Fatalf("vacuous alignment classes: equal=%d one-word=%d wide=%d deferred=%d", equal, oneWord, wideScale, deferred)
		}
		t.Logf("actual alignment outcomes: equal=%d one-word=%d wide=%d deferred=%d", equal, oneWord, wideScale, deferred)
	})
	r := rand.New(rand.NewSource(20260925))
	const trials = 200_000
	var fastAdd, fastMul int
	for range trials {
		base := int32(0)
		switch r.Intn(10) {
		case 0:
			base = math.MaxInt32 - 45
		case 1:
			base = math.MinInt32 + 45
		}
		a, b := inlineSample(r, base), inlineSample(r, base)
		for _, subtract := range []bool{false, true} {
			want, err := a.addSubLimbs(b, limits{}, "Add", subtract)
			got, ok := inlineAddSub(a, b, subtract)
			if !ok {
				continue
			}
			fastAdd++
			if err != nil || !sameRepresentation(got, want) {
				t.Fatalf("inlineAddSub(%v, %v, subtract=%v) = %#v, limb path = %#v, %v", a, b, subtract, got, want, err)
			}
		}
		e := int64(a.exponent()) + int64(b.exponent())
		if e >= math.MinInt32 && e <= math.MaxInt32 {
			want, err := a.multiplyLimbs(b, limits{}, "Mul", int32(e))
			got, ok := inlineMul(a, b)
			if ok {
				fastMul++
				if err != nil || !sameRepresentation(got, want) {
					t.Fatalf("inlineMul(%v, %v) = %#v, limb path = %#v, %v", a, b, got, want, err)
				}
			} else if err != nil || want.slow == nil {
				t.Fatalf("inlineMul(%v, %v) fell back for a product below 2^128: %#v, %v", a, b, want, err)
			}
		}
		if !a.isZero() && !b.isZero() {
			av, bv := coefficientViewOf(a), coefficientViewOf(b)
			want := compareMagnitude(&av, int64(a.exponent()), &bv, int64(b.exponent()))
			if got := inlineCompareMagnitude(a.words, a.exponent(), b.words, b.exponent()); got != want {
				t.Fatalf("inlineCompareMagnitude(%v, %v) = %d, limb path = %d", a, b, got, want)
			}
		}
	}
	// Guard against a vacuous pass: most sampled pairs must take the fast path.
	if fastAdd < trials/2 || fastMul < trials/4 {
		t.Fatalf("fast paths exercised too rarely: add/sub %d, mul %d of %d pairs", fastAdd, fastMul, trials)
	}
}

// TestInlineScaleBoundaries checks the one-word carry, shift admission
// and two-word overflow against independent math/big multiplication.
func TestInlineScaleBoundaries(t *testing.T) {
	max128 := uint128{math.MaxUint64, math.MaxUint64}
	for _, tc := range []struct {
		w    uint128
		k    uint64
		want uint128
		ok   bool
	}{
		{uint128{}, 1 << 40, uint128{}, true},
		{uint128{1, 0}, 0, uint128{1, 0}, true},
		{uint128{1, 0}, 19, uint128{pow10Words[19], 0}, true},
		// 10^38 = 0x4B3B4CA85A86C47A_098A224000000000 fits; 10^39 does not.
		{uint128{1, 0}, 38, uint128{0x098A224000000000, 0x4B3B4CA85A86C47A}, true},
		{uint128{1, 0}, 39, uint128{}, false},
		{uint128{4, 0}, 38, uint128{}, false},
		{max128, 1, uint128{}, false},
	} {
		got, ok := inlineScale(tc.w, tc.k)
		if ok != tc.ok || ok && got != tc.want {
			t.Errorf("inlineScale(%x, %d) = %x, %v; want %x, %v", tc.w, tc.k, got, ok, tc.want, tc.ok)
		}
	}
	var oneWord, highCarry, wide, overflow int
	for _, w := range []uint128{{}, {1, 0}, {2, 0}, {math.MaxUint64, 0}, {0, 1}, {math.MaxUint64, math.MaxUint64}} {
		for _, k := range []uint64{0, 1, 18, 19, 20, 37, 38, 39, math.MaxUint64} {
			got, ok := inlineScale(w, k)
			if w != (uint128{}) && k > 38 {
				if ok {
					t.Fatalf("nonzero scale admitted shift %d", k)
				}
				overflow++
				continue
			}
			want := new(big.Int).SetUint64(w.hi)
			want.Lsh(want, 64).Or(want, new(big.Int).SetUint64(w.lo))
			if want.Sign() != 0 {
				want.Mul(want, new(big.Int).Exp(big.NewInt(10), new(big.Int).SetUint64(k), nil))
			}
			if ok != (want.BitLen() <= 128) {
				t.Fatalf("scale (%x, %d): ok=%v, oracle bits=%d", w, k, ok, want.BitLen())
			}
			if !ok {
				overflow++
				continue
			}
			wantWords := uint128{want.Uint64(), new(big.Int).Rsh(new(big.Int).Set(want), 64).Uint64()}
			if got != wantWords {
				t.Fatalf("scale (%x, %d)=%x; independent product=%x", w, k, got, wantWords)
			}
			if w.lo != 0 && w.hi == 0 && k > 0 && k <= 19 {
				oneWord++
				if got.hi != 0 {
					highCarry++
				}
			} else if w != (uint128{}) && k > 0 {
				wide++
			}
		}
	}
	if oneWord < 9 || highCarry < 3 || wide < 5 || overflow < 10 {
		t.Fatalf("vacuous scale classes: one-word=%d high-carry=%d wide=%d overflow=%d", oneWord, highCarry, wide, overflow)
	}
	t.Logf("actual scale outcomes: one-word=%d high-carry=%d wide=%d overflow=%d", oneWord, highCarry, wide, overflow)
}

// TestCompareMagnitudeGroupsMatchDigitCursor pins the limb-group comparison to
// the digit cursor across inline, slow and mixed coefficients with equal
// adjusted exponents, where group alignment decides the order.
func TestCompareMagnitudeGroupsMatchDigitCursor(t *testing.T) {
	r := rand.New(rand.NewSource(20260926))
	digits := func(n int) string {
		b := make([]byte, n)
		for i := range b {
			b[i] = byte('0' + r.Intn(10))
		}
		b[0] = byte('1' + r.Intn(9))
		return string(b)
	}
	for range 50_000 {
		n := 1 + r.Intn(120)
		x := digits(n)
		y := []byte(x)
		// Perturb one digit, or keep equal and append zeros (same value).
		switch r.Intn(3) {
		case 0:
			i := r.Intn(n)
			y[i] = byte('0' + r.Intn(10))
			if y[0] == '0' {
				y[0] = '1'
			}
		case 1:
			y = append(y, make([]byte, r.Intn(20))...)
			for i := n; i < len(y); i++ {
				y[i] = '0'
			}
		default:
			y = append(y, digits(1+r.Intn(20))...)
		}
		// Place both at the same adjusted exponent.
		a := MustParse(x + "E-" + strconv.Itoa(n-1))
		b := MustParse(string(y) + "E-" + strconv.Itoa(len(y)-1))
		av, bv := coefficientViewOf(a), coefficientViewOf(b)
		want := compareDigits(&av, &bv)
		if got := compareMagnitude(&av, int64(a.exponent()), &bv, int64(b.exponent())); got != want {
			t.Fatalf("compareMagnitude(%s, %s) = %d, digit cursor = %d", a, b, got, want)
		}
	}
}

// TestInlineTextMatchesLimbText pins the inline emitter to the general limb
// emitter, including every quota boundary, across layout-changing exponents.
func TestInlineTextMatchesLimbText(t *testing.T) {
	r := rand.New(rand.NewSource(20260927))
	limbText := func(d Decimal, maxBytes uint64) (string, error) {
		// Present the same value through the slow band to force the limb path.
		v := coefficientViewOf(d)
		limbs := make([]uint32, max(v.count, 1))
		for i := range v.count {
			limbs[i] = v.limb(i)
		}
		if v.count == 0 {
			return zeroDecimal(d.exponent()).Text(maxBytes)
		}
		return slowDecimal(&slowCoefficient{limbs: limbs}, d.exponent(), d.negative()).Text(maxBytes)
	}
	for range 100_000 {
		base := int32(0)
		switch r.Intn(10) {
		case 0:
			base = math.MaxInt32 - 45
		case 1:
			base = math.MinInt32 + 45
		}
		d := inlineSample(r, base)
		want, err := limbText(d, 0)
		if err != nil {
			t.Fatal(err)
		}
		got, err := d.Text(0)
		if err != nil || got != want {
			t.Fatalf("Text(%#v) = %q, %v; limb path %q", d, got, err, want)
		}
		limit := uint64(len(want))
		if _, err := d.Text(limit); err != nil {
			t.Fatalf("Text(%q, exact size %d) refused: %v", want, limit, err)
		}
		if limit == 1 {
			continue // a zero quota means unlimited, so no smaller quota exists
		}
		if _, err := d.Text(limit - 1); err == nil || err.Error() != "decimal: Text: insufficient storage" {
			t.Fatalf("Text(%q, %d) = %v, want insufficient storage", want, limit-1, err)
		}
	}
}

// TestWordIntegerMatchesLimbPath pins the one-word Int64/Uint64 fast path to
// the general limb conversion, including error identity and precedence.
func TestWordIntegerMatchesLimbPath(t *testing.T) {
	r := rand.New(rand.NewSource(20260928))
	errorCode := func(err error) ErrorCode {
		if err == nil {
			return 0
		}
		return err.(*Error).Code
	}
	for range 200_000 {
		w := r.Uint64() >> r.Intn(64)
		if r.Intn(4) == 0 {
			w = pow10Words[r.Intn(20)] * uint64(1+r.Intn(9))
		}
		if w == 0 {
			continue
		}
		d := inlineDecimal(uint128{lo: w}, int32(r.Intn(50)-25), r.Intn(2) == 0)
		limit := uint64(1<<63 - 1)
		if d.negative() {
			limit++
		}
		want, wantErr := d.int64Limbs(limit)
		got, err := d.Int64()
		if got != want || errorCode(err) != errorCode(wantErr) {
			t.Fatalf("Int64(%v) = %d, %v; limb path %d, %v", d, got, err, want, wantErr)
		}
		wantU, wantErr := d.uint64Limbs()
		gotU, err := d.Uint64()
		if gotU != wantU || errorCode(err) != errorCode(wantErr) {
			t.Fatalf("Uint64(%v) = %d, %v; limb path %d, %v", d, gotU, err, wantU, wantErr)
		}
	}
}

// TestParseCoefficientAgainstBigInt checks parsed coefficients, exponents and
// the canonical inline/slow split against math/big, concentrating on digit
// lengths around 2^128 (39 digits) and leading-zero and point placement.
func TestParseCoefficientAgainstBigInt(t *testing.T) {
	r := rand.New(rand.NewSource(20260930))
	limit := new(big.Int).Lsh(big.NewInt(1), 128)
	anchors := []*big.Int{
		new(big.Int).Sub(limit, big.NewInt(1)), limit, new(big.Int).Add(limit, big.NewInt(1)),
		new(big.Int).Exp(big.NewInt(10), big.NewInt(38), nil), new(big.Int).Exp(big.NewInt(10), big.NewInt(39), nil),
	}
	for i := range 200_000 {
		var coefficient *big.Int
		if i < len(anchors) {
			coefficient = anchors[i]
		} else {
			n := int64(1 + r.Intn(60))
			if r.Intn(2) == 0 {
				n = int64(36 + r.Intn(6))
			}
			coefficient = new(big.Int).Rand(r, new(big.Int).Exp(big.NewInt(10), big.NewInt(n), nil))
			if r.Intn(8) == 0 {
				coefficient.Sub(limit, big.NewInt(int64(r.Intn(1000)-500)))
			}
		}
		digits := strings.Repeat("0", r.Intn(4)) + coefficient.String()
		point := r.Intn(len(digits) + 1)
		text := digits[:point] + "." + digits[point:]
		if point == len(digits) && r.Intn(2) == 0 {
			text = digits
		}
		exponent := r.Intn(40) - 20
		fractional := 0
		if strings.Contains(text, ".") {
			fractional = len(digits) - point
		}
		d, err := Parse(text + "E" + strconv.Itoa(exponent))
		if err != nil {
			t.Fatalf("Parse(%q): %v", text, err)
		}
		v := coefficientViewOf(d)
		got := new(big.Int)
		for j := v.count - 1; j >= 0; j-- {
			got.Mul(got, big.NewInt(1_000_000_000)).Add(got, big.NewInt(int64(v.limb(j))))
		}
		if got.Cmp(coefficient) != 0 || int(d.exponent()) != exponent-fractional || (d.slow != nil) != (coefficient.Cmp(limit) >= 0) {
			t.Fatalf("Parse(%qE%d) = coefficient %s exponent %d slow %v; want %s, %d", text, exponent, got, d.exponent(), d.slow != nil, coefficient, exponent-fractional)
		}
	}
}

// TestInlineDigitsAgainstDecimalWidth checks the digit estimate at every
// power-of-ten boundary below 2^128 and on random magnitudes.
func TestInlineDigitsAgainstDecimalWidth(t *testing.T) {
	check := func(w uint128) {
		t.Helper()
		var buf [40]byte
		if got, want := inlineDigits(w), uint64(len(appendUint128(buf[:0], w))); got != want {
			t.Fatalf("inlineDigits(%x) = %d, want %d", w, got, want)
		}
	}
	for k := range pow10Wide {
		p := pow10Wide[k]
		check(p)
		if k > 0 {
			below := p
			var borrow uint64
			below.lo, borrow = bits.Sub64(below.lo, 1, 0)
			below.hi -= borrow
			check(below)
		}
	}
	check(uint128{math.MaxUint64, math.MaxUint64})
	r := rand.New(rand.NewSource(20261001))
	for range 100_000 {
		if w := inlineSample(r, 0).words; w != (uint128{}) {
			check(w)
		}
	}
}

// TestInlineContextArithmeticMatchesStreams pins the exact-fit context
// shortcut to the streamed context path for Add, Sub and Mul.
func TestInlineContextArithmeticMatchesStreams(t *testing.T) {
	r := rand.New(rand.NewSource(20261003))
	shortcut := 0
	var exactHits, deferred [3]int
	for range 200_000 {
		base := int32(r.Intn(21) - 10)
		a, b := inlineSample(r, base), inlineSample(r, base)
		ctx := Context{precision: uint32(1 + r.Intn(40)), rounding: RoundingMode(r.Intn(int(Exact) + 1))}
		if r.Intn(2) == 0 {
			emin := int32(r.Intn(120) - 100)
			ctx.guards, ctx.guarded = ExponentGuards{Emin: emin, Emax: emin + int32(r.Intn(150))}, true
		}
		for op := range 3 {
			var got, want Decimal
			var events, wantEvents Conditions
			var err, wantErr error
			var exact Decimal
			var ok bool
			switch op {
			case 0, 1:
				got, events, err = a.contextAddSub(b, ctx.withLimits(limits{}), "AddWithContext", op == 1, true, nil)
				// Force the unreduced streamed path with a budget that admits
				// everything.
				want, wantEvents, wantErr = a.contextAddSub(b, ctx.withLimits(limits{MaxWork: math.MaxUint64}), "AddWithContext", op == 1, false, nil)
				exact, ok = inlineAddSub(a, b, op == 1)
			default:
				got, events, err = a.contextMul(b, ctx, limits{}, "MulWithContext")
				want, wantEvents, wantErr = a.contextMul(b, ctx, limits{MaxWork: math.MaxUint64}, "MulWithContext")
				e := int64(a.exponent()) + int64(b.exponent())
				if e >= math.MinInt32 && e <= math.MaxInt32 {
					exact, ok = inlineMul(a, b)
				}
			}
			if ok && contextExactFits(exact, ctx) {
				shortcut++
				exactHits[op]++
			} else {
				deferred[op]++
			}
			if !sameRepresentation(got, want) || events != wantEvents || (err == nil) != (wantErr == nil) ||
				err != nil && err.Error() != wantErr.Error() {
				t.Fatalf("op %d (%v, %v, %+v) = %#v, %b, %v; streamed %#v, %b, %v", op, a, b, ctx, got, events, err, want, wantEvents, wantErr)
			}
		}
	}
	if shortcut < 50_000 {
		t.Fatalf("exact-fit shortcut exercised only %d times", shortcut)
	}
	for op := range 3 {
		if exactHits[op] < 1_000 || deferred[op] < 1_000 {
			t.Fatalf("vacuous context op %d: exact=%d deferred=%d", op, exactHits[op], deferred[op])
		}
	}
	t.Logf("actual context outcomes by add/sub/mul: exact=%v deferred=%v", exactHits, deferred)
}

// TestInlineReduceMatchesLimbPath pins one-word Reduce to the general path,
// including the MaxInt32 exponent ceiling.
func TestInlineReduceMatchesLimbPath(t *testing.T) {
	r := rand.New(rand.NewSource(20261004))
	for range 200_000 {
		w := r.Uint64() >> r.Intn(64)
		if r.Intn(2) == 0 {
			w = (r.Uint64()%100_000 + 1) * pow10Words[r.Intn(15)]
		}
		if w == 0 {
			continue
		}
		exponent := int32(r.Intn(60) - 30)
		if r.Intn(4) == 0 {
			exponent = math.MaxInt32 - int32(r.Intn(25))
		}
		d := inlineDecimal(uint128{lo: w}, exponent, r.Intn(2) == 0)
		// The general path may return its slow input unchanged, so compare
		// value and cohort, and require canonical inline storage.
		if got, want := d.Reduce(), asSlowBand(d).Reduce(); got.exponent() != want.exponent() || !got.Equal(want) || got.slow != nil {
			t.Fatalf("Reduce(%#v) = %#v, limb path %#v", d, got, want)
		}
	}
}

// TestInlineDisplayMatchesLimbPath pins the pre-rendered inline display
// digits to the limb path for Fixed, Scientific and Engineering in every
// mode, including output and work budgets at the exact boundary.
func TestInlineDisplayMatchesLimbPath(t *testing.T) {
	r := rand.New(rand.NewSource(20261006))
	for range 60_000 {
		d := inlineSample(r, 0)
		if d.isZero() {
			continue
		}
		slow := asSlowBand(d)
		options := DisplayOptions{Mode: RoundingMode(r.Intn(int(Exact) + 1))}
		places := uint64(r.Intn(45))
		kind := displayKind(r.Intn(3))
		if kind == displayScientific {
			places++
		}
		want, wantErr := slow.display(kind, places, options, "Display")
		got, err := d.display(kind, places, options, "Display")
		if got != want || (err == nil) != (wantErr == nil) || err != nil && err.Error() != wantErr.Error() {
			t.Fatalf("display(%d, %v, %d, %+v) = %q, %v; limb path %q, %v", kind, d, places, options, got, err, want, wantErr)
		}
		if err != nil {
			continue
		}
		size := uint64(len(want))
		options.Budget = Budget{MaxOutputBytes: size}
		if _, err := d.display(kind, places, options, "Display"); err != nil {
			t.Fatalf("exact output budget refused %q: %v", want, err)
		}
		if size > 1 {
			options.Budget.MaxOutputBytes = size - 1
			_, err := d.display(kind, places, options, "Display")
			_, wantErr := slow.display(kind, places, options, "Display")
			if (err == nil) != (wantErr == nil) {
				t.Fatalf("output budget %d: inline %v, limb %v", size-1, err, wantErr)
			}
		}
	}
}

// TestInlineHashMatchesLimbEncoding requires the one-word hash to feed the
// same bytes as the general encoding: equal digests under a shared seed for
// the same value in both carriers and for equal values across cohorts.
func TestInlineHashMatchesLimbEncoding(t *testing.T) {
	r := rand.New(rand.NewSource(20261007))
	seed := maphash.MakeSeed()
	digest := func(d Decimal) uint64 {
		var h maphash.Hash
		h.SetSeed(seed)
		Hasher{}.Hash(&h, d)
		return h.Sum64()
	}
	for range 200_000 {
		w := r.Uint64() >> r.Intn(64)
		if r.Intn(2) == 0 {
			w = (r.Uint64()%1_000_000 + 1) * pow10Words[r.Intn(13)]
		}
		if w == 0 {
			continue
		}
		exponent := int32(r.Intn(60) - 30)
		if r.Intn(8) == 0 {
			exponent = math.MaxInt32 - int32(r.Intn(25))
		}
		d := inlineDecimal(uint128{lo: w}, exponent, r.Intn(2) == 0)
		if got, want := digest(d), digest(asSlowBand(d)); got != want {
			t.Fatalf("Hash(%v) inline digest %x != limb digest %x", d, got, want)
		}
		// An equal two-word cohort takes the general path and must agree.
		if scaled, ok := inlineScale(d.words, 19); ok && scaled.hi != 0 && exponent >= math.MinInt32+19 {
			wide := inlineDecimal(scaled, exponent-19, d.negative())
			if got, want := digest(d), digest(wide); got != want {
				t.Fatalf("Hash(%v) = %x but equal cohort %v = %x", d, got, wide, want)
			}
		}
	}
}

// TestDigitGroupAndLongCoefficients checks the SWAR eight-digit step on
// random groups and long slow-band coefficients against math/big, with the
// decimal point at every group offset so groups straddle it.
func TestDigitGroupAndLongCoefficients(t *testing.T) {
	r := rand.New(rand.NewSource(20261008))
	for range 100_000 {
		n := 1 + r.Intn(9)
		b := make([]byte, n)
		want := uint32(0)
		for i := range b {
			b[i] = byte('0' + r.Intn(10))
			want = want*10 + uint32(b[i]-'0')
		}
		if got := digitGroup(string(b)); got != want {
			t.Fatalf("digitGroup(%s) = %d", b, got)
		}
		if got := digitGroup(b); got != want {
			t.Fatalf("digitGroup([]byte %s) = %d", b, got)
		}
	}
	for range 3_000 {
		n := 40 + r.Intn(400)
		b := make([]byte, n)
		for i := range b {
			b[i] = byte('0' + r.Intn(10))
		}
		b[0] = byte('1' + r.Intn(9))
		point := r.Intn(n + 1)
		text := string(b[:point]) + "." + string(b[point:])
		want, _ := new(big.Int).SetString(string(b), 10)
		for _, carrier := range []string{"string", "bytes"} {
			var d Decimal
			var err error
			if carrier == "string" {
				d, err = Parse(text)
			} else {
				err = d.UnmarshalText([]byte(text))
			}
			if err != nil {
				t.Fatal(err)
			}
			v := coefficientViewOf(d)
			got := new(big.Int)
			for j := v.count - 1; j >= 0; j-- {
				got.Mul(got, big.NewInt(1_000_000_000)).Add(got, big.NewInt(int64(v.limb(j))))
			}
			if got.Cmp(want) != 0 || int(d.exponent()) != -(n-point) {
				t.Fatalf("%s Parse(%s) = %s E%d", carrier, text, got, d.exponent())
			}
		}
	}
}

// TestStickyRemoteOperandMatchesFullSum pins the context-addition reduction (the
// remote-operand collapse and the zero clamp) to the full aligned context
// sum of the unreduced reference seam (reduce=false) across gaps around and
// beyond the precision, every mode, borrows, carries and guarded contexts
// that make the result subnormal or overflow.
func TestStickyRemoteOperandMatchesFullSum(t *testing.T) {
	r := rand.New(rand.NewSource(20261009))
	collapsed := 0
	for range 200_000 {
		a := inlineSample(r, 0)
		b := inlineSample(r, int32(-r.Intn(120)))
		if r.Intn(4) == 0 { // a genuine slow-band operand
			digits := make([]byte, 40+r.Intn(50))
			for i := range digits {
				digits[i] = byte('0' + r.Intn(10))
			}
			digits[0] = '9'
			a = MustParse(string(digits) + "E" + strconv.Itoa(r.Intn(40)-20))
		}
		if r.Intn(2) == 0 {
			a, b = b, a
		}
		ctx := Context{precision: uint32(1 + r.Intn(30)), rounding: RoundingMode(r.Intn(int(Exact) + 1))}
		if r.Intn(3) == 0 {
			emin := int32(r.Intn(160) - 150)
			ctx.guards, ctx.guarded = ExponentGuards{Emin: emin, Emax: emin + int32(r.Intn(120))}, true
		}
		if x, y := contextReduceOperands(a, b, ctx); !sameRepresentation(x, a) || !sameRepresentation(y, b) {
			collapsed++
		}
		for _, subtract := range []bool{false, true} {
			got, events, err := a.contextAddSub(b, ctx.withLimits(limits{}), "AddWithContext", subtract, true, nil)
			want, wantEvents, wantErr := a.contextAddSub(b, ctx.withLimits(limits{MaxWork: math.MaxUint64}), "AddWithContext", subtract, false, nil)
			if !sameRepresentation(got, want) || events != wantEvents || (err == nil) != (wantErr == nil) ||
				err != nil && err.Error() != wantErr.Error() {
				t.Fatalf("%v %v sub=%v %+v: %#v %b %v; full sum %#v %b %v", a, b, subtract, ctx, got, events, err, want, wantEvents, wantErr)
			}
		}
	}
	if collapsed < 20_000 {
		t.Fatalf("collapse exercised only %d times", collapsed)
	}
}

// TestInlineFastPathsKeepGeneralPathDirection checks the direction bit of the fast
// paths: inlineQuantize returns the conditions of the general limb path,
// including the direction bit, which also equals the independent math/big
// quantize oracle's direction, and both directions occur on the fast path; the
// exact-fit context shortcut returns only exact results, for which the general
// (large-budget) path reports no condition and no direction.
func TestInlineFastPathsKeepGeneralPathDirection(t *testing.T) {
	r := rand.New(rand.NewSource(20260925))
	fast := map[Conditions]int{}
	for range 100_000 {
		d := inlineSample(r, 0)
		if d.isZero() {
			continue
		}
		target := d.exponent() + int32(r.Intn(41)-5)
		mode := RoundingMode(r.Intn(int(Exact)))
		if _, events, _, ok := inlineQuantize(d, target, mode); ok {
			want, wantEvents, wantErr := d.quantizeLimbs(target, Context{rounding: mode}, limits{}, "Quantize")
			got, gotEvents, err := d.Quantize(target, mode)
			if err != nil || wantErr != nil || !sameRepresentation(got, want) || gotEvents != wantEvents || events != wantEvents {
				t.Fatalf("inlineQuantize(%#v, %d, %v): %#v %v %v; limb path %#v %v %v", d, target, mode, got, gotEvents, err, want, wantEvents, wantErr)
			}
			if _, _, oracle := quantizeOracle(d, target, mode); oracle != gotEvents {
				t.Fatalf("inlineQuantize(%#v, %d, %v): conditions %v, oracle %v", d, target, mode, gotEvents, oracle)
			}
			fast[gotEvents&(Increased|Decreased)]++
		}
	}
	if fast[Increased] < 10_000 || fast[Decreased] < 10_000 || fast[0] < 1_000 {
		t.Fatalf("inlineQuantize direction coverage: %v", fast)
	}
	shortcut, rounded := 0, map[Conditions]int{}
	for range 100_000 {
		base := int32(r.Intn(21) - 10)
		a, b := inlineSample(r, base), inlineSample(r, base)
		ctx := Context{precision: uint32(1 + r.Intn(40)), rounding: RoundingMode(r.Intn(int(Exact)))}
		if r.Intn(2) == 0 {
			emin := int32(r.Intn(120) - 100)
			ctx.guards, ctx.guarded = ExponentGuards{Emin: emin, Emax: emin + int32(r.Intn(150))}, true
		}
		subtract := r.Intn(2) == 0
		got, events, err := a.contextAddSub(b, ctx.withLimits(limits{}), "AddWithContext", subtract, true, nil)
		want, wantEvents, wantErr := a.contextAddSub(b, ctx.withLimits(limits{MaxWork: math.MaxUint64}), "AddWithContext", subtract, false, nil)
		if (err == nil) != (wantErr == nil) || !sameRepresentation(got, want) || events != wantEvents {
			t.Fatalf("%v %v sub=%v %+v: %#v %v %v; general %#v %v %v", a, b, subtract, ctx, got, events, err, want, wantEvents, wantErr)
		}
		if exact, ok := inlineAddSub(a, b, subtract); ok && contextExactFits(exact, ctx) {
			shortcut++
			if wantEvents != 0 || !sameRepresentation(got, exact) {
				t.Fatalf("exact-fit shortcut %v %v: general path reports %v", a, b, wantEvents)
			}
			continue
		}
		rounded[events&(Increased|Decreased)]++
	}
	if shortcut < 5_000 || rounded[Increased] < 1_000 || rounded[Decreased] < 1_000 {
		t.Fatalf("context shortcut coverage: %d shortcuts, rounded %v", shortcut, rounded)
	}
}

// shortOperand returns a random inline decimal: digit count uniform in 1..39,
// exponent in a narrow or wide window, random sign, sometimes zero or with
// trailing zeros or all nines.
func shortOperand(r *randv2.Rand, expSpan int) Decimal {
	for {
		n := 1 + r.IntN(39)
		buf := make([]byte, n)
		kind := r.IntN(12)
		for i := range buf {
			switch kind {
			case 0:
				buf[i] = '0'
			case 1:
				buf[i] = '9'
			case 2:
				buf[i] = '0'
				if i == 0 {
					buf[i] = '1'
				}
			default:
				buf[i] = byte('0' + r.IntN(10))
			}
		}
		if kind >= 9 && n > 3 {
			for i := n - 1 - r.IntN(n-1); i < n; i++ {
				buf[i] = '0'
			}
		}
		if kind == 3 {
			buf = []byte("340282366920938463463374607431768211455")
		}
		d := MustParse(string(buf))
		if d.slow != nil {
			continue
		}
		e := int32(r.IntN(2*expSpan+1) - expSpan)
		return d.withExponent(e).withNegative(r.IntN(2) == 0)
	}
}

func shortContexts() []Context {
	var out []Context
	for _, p := range []uint32{1, 2, 7, 16, 19, 20, 34, 38, 39, 60} {
		for m := TiesToEven; m <= Exact; m++ {
			c, err := NewContext(p, m, nil, 0)
			if err != nil {
				panic(err)
			}
			out = append(out, c)
			g, err := NewContext(p, m, &ExponentGuards{Emin: -20, Emax: 25}, 0)
			if err != nil {
				panic(err)
			}
			out = append(out, g)
		}
	}
	d64 := Decimal64Context()
	d128 := Decimal128Context()
	tr, _ := d64.WithTraps(Inexact | Rounded | Subnormal)
	return append(out, d64, d128, tr)
}

func samePathOutcome(t *testing.T, what string, a Decimal, ac Conditions, ae error, b Decimal, bc Conditions, be error) {
	t.Helper()
	if (ae == nil) != (be == nil) || ae != nil && ae.Error() != be.Error() {
		t.Fatalf("%s: error %v vs %v", what, ae, be)
	}
	if ac != bc {
		t.Fatalf("%s: conditions %v vs %v (%v vs %v)", what, ac, bc, a, b)
	}
	if a.exponent() != b.exponent() || a.negative() != b.negative() || a.Compare(b) != 0 || a.String() != b.String() {
		t.Fatalf("%s: value %v (e=%d) vs %v (e=%d)", what, a, a.exponent(), b, b.exponent())
	}
	if (a.slow == nil) != (b.slow == nil) {
		t.Fatalf("%s: carrier differs", what)
	}
}

// TestInlineBudgetBoundsDominateEstimates checks the constant bounds of the
// budget gates: on every shape an inline path serves, they are at least the
// estimate, which bounds the general path's charges.
func TestInlineBudgetBoundsDominateEstimates(t *testing.T) {
	r := randv2.New(randv2.NewPCG(1, 2))
	ctxs := shortContexts()
	for range 400000 {
		x, y := shortOperand(r, 45), shortOperand(r, 45)
		ctx := ctxs[r.IntN(len(ctxs))]
		sub := r.IntN(2) == 0
		// context add/sub
		_, okI := inlineAddSub(x, y, sub)
		_, _, _, okW := wideAddSub(x, y, sub)
		if (okI || okW) && !x.isZero() && !y.isZero() {
			est := EstimateAdd
			if sub {
				est = EstimateSub
			}
			c, err := est(x.Shape(), y.Shape(), ctx)
			if err == nil && (c.WorkUnits > inlineContextAddSubWork || c.Digits > inlineAddSubDigits) && ctx.precision <= 38 && !ctx.guarded {
				t.Fatalf("ctx add bound: %v %v p=%d: %+v", x, y, ctx.precision, c)
			}
			if okI {
				// exact fit path is taken at any precision when the exact inline sum fits
				if c.WorkUnits > inlineContextAddSubWork || c.Digits > inlineAddSubDigits {
					exact, _ := inlineAddSub(x, y, sub)
					if contextExactFits(exact, ctx) && !ctx.guarded {
						t.Fatalf("ctx add exact-fit bound: %v %v p=%d: %+v", x, y, ctx.precision, c)
					}
				}
				c, err = est(x.Shape(), y.Shape(), Context{})
				if err == nil && (c.WorkUnits > inlineAddSubWork || c.Digits > inlineAddSubDigits) {
					t.Fatalf("exact add bound: %v %v: %+v", x, y, c)
				}
			}
		}
		// mul
		if _, ok := inlineMul(x, y); ok {
			c, err := EstimateMul(x.Shape(), y.Shape(), Context{})
			if err == nil && !inlineMulAdmitted(x, y, limits{MaxDigits: c.Digits, MaxWork: c.WorkUnits}, 0) && !x.isZero() && !y.isZero() {
				t.Fatalf("exact mul: estimate budget not admitted %v %v %+v", x, y, c)
			}
			if err == nil && c.Digits > 1 && inlineMulAdmitted(x, y, limits{MaxDigits: c.Digits - 1}, 0) && !x.isZero() && !y.isZero() {
				t.Fatalf("exact mul: digits below estimate admitted %v %v %+v", x, y, c)
			}
			if err == nil && c.WorkUnits > 1 && inlineMulAdmitted(x, y, limits{MaxWork: c.WorkUnits - 1}, 0) && !x.isZero() && !y.isZero() {
				t.Fatalf("exact mul: work below estimate admitted %v %v %+v", x, y, c)
			}
		}
		if !x.isZero() && !y.isZero() && ctx.precision <= 38 && !ctx.guarded {
			c, err := EstimateMul(x.Shape(), y.Shape(), ctx)
			// The multiplication bound is at least the estimate.
			da, db := inlineDigits(x.words), inlineDigits(y.words)
			digits := min(da+db, uint64(ctx.precision))
			work := digitLimbs(da)*digitLimbs(db) + da + db + 2*digits + 1
			if err == nil && (c.WorkUnits > work || c.Digits > digits) {
				t.Fatalf("ctx mul bound: %v %v p=%d: est %+v ours %d/%d", x, y, ctx.precision, c, digits, work)
			}
		}
		// quantize
		target := x.exponent() + int32(r.IntN(81)-40)
		if !x.isZero() {
			if _, _, _, ok := inlineQuantize(x, target, TiesToEven); ok {
				c, err := EstimateQuantize(x.Shape(), target, Context{rounding: AwayFromZero})
				if err == nil && (c.WorkUnits > inlineQuantizeWork || c.Digits > inlineResultDigits) {
					t.Fatalf("quantize bound: %v -> %d: %+v", x, target, c)
				}
			}
		}
		// division
		if inlineDivShape(x, y) {
			if _, _, _, ok := inlineDivToExponent(x, y, target, TiesToEven); ok {
				c, err := EstimateDivToExponent(x.Shape(), y.Shape(), target)
				if err == nil && (c.WorkUnits > inlineDivWork || c.Digits > inlineResultDigits) {
					// the estimate's digits bound is dn-dy+2 and may exceed the inline result
					q, _, _ := x.DivToExponentWithBudget(y, target, AwayFromZero, Budget{MaxDigits: inlineResultDigits, MaxWork: inlineDivWork})
					q2, _, err2 := x.divToExponentLimbs(y, target, AwayFromZero, limits{MaxDigits: inlineResultDigits, MaxWork: inlineDivWork}, "DivToExponentWithBudget")
					if err2 != nil || q.Compare(q2) != 0 {
						t.Fatalf("divToExponent bound: %v / %v -> %d: %+v err=%v", x, y, target, c, err2)
					}
				}
			}
			if ctx.precision <= inlineDivMaxPrecision {
				cc := ctx
				if _, _, _, ok := inlineDivContext(x, y, &cc, "DivWithContext"); ok {
					_, _, err1 := x.divContextLimbs(y, ctx, limits{}, "DivWithContext")
					_, _, err2 := x.divContextLimbs(y, ctx, limits{MaxDigits: inlineResultDigits, MaxWork: inlineDivWork}, "DivWithContext")
					if (err1 == nil) != (err2 == nil) || err1 != nil && err1.Error() != err2.Error() {
						t.Fatalf("div ctx bound: %v / %v p=%d: %v vs %v", x, y, ctx.precision, err1, err2)
					}
				}
			}
		}
	}
}

// TestInlineBudgetBoundsAtExtremes measures the general path's smallest
// admitting work cap on the dearest shape each machine-word gate serves:
// no gate bound lies below it, and the exact Add/Sub and the division
// bounds are attained.
func TestInlineBudgetBoundsAtExtremes(t *testing.T) {
	// Two 39-digit coefficients below 2^128 whose quotient, 1.003…, has 39
	// digits at 38 fraction places.
	high := MustParse("3" + strings.Repeat("0", 37) + "7")
	low := MustParse("2" + strings.Repeat("9", 38))
	shifted := MustParse("3" + strings.Repeat("0", 37) + "7E+38")
	ctx, err := NewContext(38, TiesToEven, nil, 0)
	if err != nil {
		t.Fatal(err)
	}
	least := func(call func(limits) error) uint64 {
		return smallestAdmitting(1<<20, func(w uint64) bool { return call(limits{MaxWork: w}) == nil })
	}

	if _, ok := inlineAddSub(high, low, true); !ok {
		t.Fatal("the exact difference left the inline path")
	}
	if got := least(func(b limits) error {
		_, err := high.addSubLimbs(low, b, "Sub", true)
		return err
	}); got != inlineAddSubWork {
		t.Fatalf("exact Sub admits from %d, bound %d", got, inlineAddSubWork)
	}

	if _, _, _, ok := wideAddSub(shifted, low, true); !ok {
		t.Fatal("the wide difference left the machine-word path")
	}
	if got := least(func(b limits) error {
		c := ctx
		c.arith = b
		_, _, err := shifted.contextAddSubGeneral(low, c, "SubWithContext", true, true, nil)
		return err
	}); got != inlineContextAddSubWork-2 {
		// N is at most 38 on this shape; the bound allows the 39 digits of
		// an exact fit, whose span is shorter.
		t.Fatalf("context Sub admits from %d, bound %d", got, inlineContextAddSubWork)
	}

	if _, _, refused, ok := inlineQuantize(low, 1, TiesToEven); !ok || refused {
		t.Fatal("the cut left the inline path")
	}
	if got := least(func(b limits) error {
		_, _, err := low.quantizeLimbs(1, Context{}, b, "Quantize")
		return err
	}); got != inlineQuantizeWork-1 {
		// 39 digits cut by one keep 38; a carry into a 39th would need a
		// coefficient of 38 nines, which is above 2^128.
		t.Fatalf("Quantize admits from %d, bound %d", got, inlineQuantizeWork)
	}

	if _, _, _, ok := inlineDivToExponent(high, low, -38, TiesToEven); !ok {
		t.Fatal("the quotient left the machine-word path")
	}
	if got := least(func(b limits) error {
		_, _, err := high.divToExponentLimbs(low, -38, TiesToEven, b, "DivToExponent")
		return err
	}); got != inlineDivWork {
		t.Fatalf("DivToExponent admits from %d, bound %d", got, inlineDivWork)
	}
	if got := least(func(b limits) error {
		_, _, err := high.divContextLimbs(low, ctx, b, "DivWithContext")
		return err
	}); got > inlineDivWork {
		t.Fatalf("DivWithContext admits from %d, bound %d", got, inlineDivWork)
	}
}

// TestBudgetedInlineMatchesGeneral pins budgeted calls served inline to the
// general path under the same budget, including budgets at each gate's
// threshold.
func TestBudgetedInlineMatchesGeneral(t *testing.T) {
	r := randv2.New(randv2.NewPCG(3, 4))
	ctxs := shortContexts()
	budgets := []limits{{}, {39, 290}, {39, 289}, {39, 261}, {39, 312}, {40, 195}, {39, 78}, {39, 183}, {0, 312}, {39, 0}, {38, 311}, {1 << 20, 1 << 40}, {40, 0}, {78, 103}, {20, 60}, {16, 100}}
	for range 300000 {
		x, y := shortOperand(r, 45), shortOperand(r, 45)
		ctx := ctxs[r.IntN(len(ctxs))]
		b := budgets[r.IntN(len(budgets))]
		sub := r.IntN(2) == 0
		bc := ctx
		bc.arith = b
		// Context add/sub against the planned general path.
		got, gc, gerr := x.contextAddSub(y, bc, "AddWithContext", sub, true, nil)
		var want Decimal
		var wc Conditions
		var werr error
		if ctx.precision == 0 {
			want, werr = x.addSubLimbs(y, b, "AddWithContext", sub)
		} else {
			want, wc, werr = x.contextAddSubGeneral(y, bc, "AddWithContext", sub, true, nil)
		}
		sameValueOutcome(t, "ctx addsub", got, gc, gerr, want, wc, werr)
		// exact add
		eg, egerr := x.addSub(y, b, "AddWithContext", sub)
		ew, ewerr := x.addSubLimbs(y, b, "AddWithContext", sub)
		sameValueOutcome(t, "exact addsub", eg, 0, egerr, ew, 0, ewerr)
		// mul
		mg, mgc, mgerr := x.contextMulPath(y, ctx, b, "MulWithContext", false)
		mw, mwc, mwerr := x.contextMulPath(y, ctx, b, "MulWithContext", true)
		_ = mwc
		_ = mgc
		if (mgerr == nil) != (mwerr == nil) {
			// The stream charges the same base, so both paths admit alike.
			t.Fatalf("ctx mul admission: %v * %v p=%d budget %+v: %v vs %v", x, y, ctx.precision, b, mgerr, mwerr)
		}
		if mgerr == nil {
			sameValueOutcome(t, "ctx mul", mg, mgc, mgerr, mw, mwc, mwerr)
		}
		if e := int64(x.exponent()) + int64(y.exponent()); e >= -1<<31 && e < 1<<31 {
			xg, xgerr := x.multiply(y, b, "MulWithContext")
			xw, xwerr := x.multiplyLimbs(y, b, "MulWithContext", int32(e))
			sameValueOutcome(t, "exact mul", xg, 0, xgerr, xw, 0, xwerr)
		}
		// quantize
		target := x.exponent() + int32(r.IntN(81)-40)
		qg, qgc, qgerr := x.quantize(target, Context{rounding: ctx.rounding}, b, "QuantizeWithContext")
		qw, qwc, qwerr := x.quantizeLimbs(target, Context{rounding: ctx.rounding}, b, "QuantizeWithContext")
		sameValueOutcome(t, "quantize", qg, qgc, qgerr, qw, qwc, qwerr)
		// division
		dg, dgc, dgerr := x.divToExponent(y, target, ctx.rounding, b, "DivToExponentWithBudget")
		dw, dwc, dwerr := x.divToExponentLimbs(y, target, ctx.rounding, b, "DivToExponentWithBudget")
		sameValueOutcome(t, "divToExponent", dg, dgc, dgerr, dw, dwc, dwerr)
		cg, cgc, cgerr := x.divContext(y, ctx, b, "DivWithContext")
		cw, cwc, cwerr := x.divContextLimbs(y, ctx, b, "DivWithContext")
		if ctx.precision != 0 {
			sameValueOutcome(t, "divContext", cg, cgc, cgerr, cw, cwc, cwerr)
		}
	}
}

func sameValueOutcome(t *testing.T, what string, a Decimal, ac Conditions, ae error, b Decimal, bc Conditions, be error) {
	t.Helper()
	if (ae == nil) != (be == nil) || ae != nil && ae.Error() != be.Error() {
		t.Fatalf("%s: error %v vs %v", what, ae, be)
	}
	if ae != nil {
		return
	}
	if ac != bc {
		t.Fatalf("%s: conditions %v vs %v (%v vs %v)", what, ac, bc, a, b)
	}
	if a.exponent() != b.exponent() || a.negative() != b.negative() || a.Compare(b) != 0 {
		t.Fatalf("%s: value %v (e=%d) vs %v (e=%d)", what, a, a.exponent(), b, b.exponent())
	}
}

// TestQuantizeContextInlineMatchesGeneral pins the inline Quantize under a
// precision and guards, and drops of more than 19 digits, to the general
// target-rounding path.
func TestQuantizeContextInlineMatchesGeneral(t *testing.T) {
	r := randv2.New(randv2.NewPCG(5, 6))
	ctxs := shortContexts()
	for i := range 600000 {
		x := shortOperand(r, 30)
		ctx := ctxs[r.IntN(len(ctxs))]
		if i%3 == 0 {
			ctx = Context{rounding: ctx.rounding}
		}
		target := x.exponent() + int32(r.IntN(101)-50)
		if i%7 == 0 {
			target = 0
		}
		g, gc, gerr := x.quantize(target, ctx, ctx.arith, "QuantizeWithContext")
		w, wc, werr := x.quantizeLimbs(target, ctx, ctx.arith, "QuantizeWithContext")
		samePathOutcome(t, "quantize ctx", g, gc, gerr, w, wc, werr)
		g, gc, gerr = x.Quantize(target, ctx.rounding)
		w, wc, werr = x.quantizeLimbs(target, Context{rounding: ctx.rounding}, limits{}, "Quantize")
		samePathOutcome(t, "Quantize", g, gc, gerr, w, wc, werr)
	}
}

// TestPowInlineMatchesGeneral pins the inline integer power, bare and in
// context, to the general power kernel.
func TestPowInlineMatchesGeneral(t *testing.T) {
	r := randv2.New(randv2.NewPCG(7, 8))
	ctxs := shortContexts()
	fast := 0
	for i := range 300000 {
		x := shortOperand(r, 12)
		if i%2 == 0 {
			// short operands, whose small powers stay within 256 bits
			x = New(int64(r.Uint64N(pow10Words[1+r.IntN(12)])), int32(r.IntN(13)-6))
			if r.IntN(2) == 0 {
				x = x.Neg()
			}
		}
		n := int32(2 + r.IntN(9))
		if i%11 == 0 {
			n = int32(2 + r.IntN(200))
		}
		ctx := ctxs[r.IntN(len(ctxs))]
		if i%5 == 0 {
			ctx = Context{}
		}
		if !x.isZero() {
			if a, b, ok := powInlineFactors(x, n); ok {
				_, _ = a, b
				fast++
			}
		}
		g, gc, gerr := x.powContext(n, ctx, limits{}, "PowWithContext", nil)
		w, wc, werr := x.powContext(n, ctx, limits{}, "PowWithContext", &powCount{})
		samePathOutcome(t, "pow", g, gc, gerr, w, wc, werr)
	}
	if fast < 50000 {
		t.Fatalf("fast path taken only %d times", fast)
	}
}

// TestIntDivInlineMatchesGeneral pins the two-word Quo, Rem and RemNear to the
// general integer-division kernel.
func TestIntDivInlineMatchesGeneral(t *testing.T) {
	r := randv2.New(randv2.NewPCG(9, 10))
	ctxs := shortContexts()
	fast := 0
	for i := range 600000 {
		x, y := shortOperand(r, 8), shortOperand(r, 8)
		if i%3 == 0 {
			x = New(int64(r.Uint64N(pow10Words[1+r.IntN(18)])), int32(r.IntN(9)-6))
			y = New(int64(r.Uint64N(pow10Words[1+r.IntN(10)])), int32(r.IntN(9)-6))
		}
		if i%13 == 0 && !y.isZero() {
			// exact multiples and exact halves
			k := New(int64(r.Uint64N(1000)), 0)
			x, _ = y.Mul(k)
			if i%2 == 0 {
				h, _ := y.Mul(New(5, -1))
				x, _ = x.Add(h)
			}
		}
		ctx := ctxs[r.IntN(len(ctxs))]
		if i%4 == 0 {
			ctx = Context{}
		}
		op := intDivOp(r.IntN(3))
		if i%5 == 1 && x.slow == nil && y.slow == nil {
			shift := int32(r.IntN(121) - 60)
			x, y = x.withExponent(x.exponent()+shift), y.withExponent(y.exponent()+shift)
		}
		if x.slow == nil && y.slow == nil && !x.isZero() && !y.isZero() {
			cc := ctx
			if _, _, ok := inlineIntDivide(x, y, op, &cc); ok {
				fast++
			}
		}
		g, gc, gerr := x.intDivide(y, op, ctx, limits{}, "Rem", nil)
		w, wc, werr := x.intDivide(y, op, ctx, limits{}, "Rem", &quoRemCount{})
		samePathOutcome(t, "intdiv", g, gc, gerr, w, wc, werr)
	}
	if fast < 100000 {
		t.Fatalf("fast path taken only %d times", fast)
	}
}

// TestIntDivInlineSubnormal checks the Subnormal report of the two-word
// integer division under guards.
func TestIntDivInlineSubnormal(t *testing.T) {
	ctx, err := NewContext(16, TiesToEven, &ExponentGuards{Emin: -20, Emax: 25}, 0)
	if err != nil {
		t.Fatal(err)
	}
	x, y := MustParse("7E-25"), MustParse("3E-25")
	g, gc, gerr := x.intDivide(y, intDivRem, ctx, limits{}, "Rem", nil)
	w, wc, werr := x.intDivide(y, intDivRem, ctx, limits{}, "Rem", &quoRemCount{})
	t.Logf("fast %v %v %v; general %v %v %v", g, gc, gerr, w, wc, werr)
	samePathOutcome(t, "sub", g, gc, gerr, w, wc, werr)
	if gc != Subnormal {
		t.Fatalf("no Subnormal")
	}
}

// wideOperand returns a random decimal of 1..maxDigits digits.
func wideOperand(r *randv2.Rand, maxDigits, expSpan int) Decimal {
	n := 1 + r.IntN(maxDigits)
	buf := make([]byte, n)
	kind := r.IntN(10)
	for i := range buf {
		switch kind {
		case 0:
			buf[i] = '9'
		case 1:
			buf[i] = '0'
			if i == 0 {
				buf[i] = '1'
			}
		default:
			buf[i] = byte('0' + r.IntN(10))
		}
	}
	if kind >= 8 && n > 3 {
		for i := n - 1 - r.IntN(n-1); i < n; i++ {
			buf[i] = '0'
		}
	}
	d := MustParse(string(buf))
	return d.withExponent(int32(r.IntN(2*expSpan+1) - expSpan)).withNegative(r.IntN(2) == 0)
}

// TestContextSumMatchesStream pins the stack sum of context Add and Sub to the
// three-pass stream on the same plan.
func TestContextSumMatchesStream(t *testing.T) {
	r := randv2.New(randv2.NewPCG(11, 12))
	ctxs := shortContexts()
	for i := range 400000 {
		maxDigits := 80
		if i%10 == 0 {
			maxDigits = 400
		}
		x, y := wideOperand(r, maxDigits, 40), wideOperand(r, maxDigits, 40)
		if i%7 == 0 {
			// near-cancellation and all-nines carries
			y = x.Neg()
			one := New(int64(r.IntN(3)-1), x.exponent()+int32(r.IntN(5)-2))
			y, _ = y.Add(one)
		}
		ctx := ctxs[r.IntN(len(ctxs))]
		if ctx.precision == 0 {
			continue
		}
		sub := r.IntN(2) == 0
		got, gc, gerr := x.contextAddSubGeneral(y, ctx, "AddWithContext", sub, true, nil)
		// Reference: the exact sum, rounded by the stream finisher as x+0.
		exact, err := x.addSubLimbs(y, limits{}, "AddWithContext", sub)
		if err != nil {
			t.Fatal(err)
		}
		if exact.isZero() {
			continue
		}
		v := coefficientViewOf(exact)
		digits, _ := arithmeticDigits(&v)
		p := contextPlan{a: v, ideal: int64(exact.exponent()), greaterA: true, add: true, negative: exact.negative(), groups: digitLimbs(digits), base: digits}
		want, wc, werr := contextRunStream(p, ctx, limits{}, "AddWithContext")
		samePathOutcome(t, "ctx sum", got, gc, gerr, want, wc, werr)
		// RoundToPrecision through the same seam.
		got, gc, gerr = exact.roundToPrecision(ctx, "AddWithContext")
		samePathOutcome(t, "rtp", got, gc, gerr, want, wc, werr)
	}
}

// TestSumInlineShapeMatchesFold pins the unbudgeted Sum of inline operands to
// a fold of exact additions.
func TestSumInlineShapeMatchesFold(t *testing.T) {
	r := randv2.New(randv2.NewPCG(13, 14))
	for i := range 20000 {
		n := 1 + r.IntN(40)
		vals := make([]Decimal, n)
		var fold Decimal
		for j := range vals {
			vals[j] = shortOperand(r, 9)
			if i%3 == 0 {
				vals[j] = New(int64(r.Uint64N(1e12)), int32(-r.IntN(7)))
			}
			if i%17 == 0 {
				vals[j] = zeroDecimal(int32(r.IntN(5)))
			}
			if i%19 == 0 {
				// Coefficients that are multiples of 2^64: only the high word is set.
				vals[j] = inlineDecimal(uint128{hi: 1 + r.Uint64N(1<<20)}, int32(r.IntN(5)), r.IntN(2) == 0)
			}
			if j == 0 {
				fold = vals[0]
			} else {
				fold, _ = fold.Add(vals[j])
			}
		}
		got, err := Sum(vals...)
		if err != nil {
			t.Fatal(err)
		}
		want, err := SumWithBudget(vals, Budget{MaxDigits: 1 << 30, MaxWork: 1 << 40})
		if err != nil {
			t.Fatal(err)
		}
		samePathOutcome(t, "sum vs budgeted", got, 0, nil, want, 0, nil)
		samePathOutcome(t, "sum vs fold", got, 0, nil, fold, 0, nil)
	}
}

// TestFinishContextInlineMatchesLimbs pins the word finisher to the limb
// finisher on the same truncated coefficient and class.
func TestFinishContextInlineMatchesLimbs(t *testing.T) {
	r := randv2.New(randv2.NewPCG(15, 16))
	ctxs := shortContexts()
	taken := 0
	for range 1000000 {
		x := shortOperand(r, 0)
		ctx := ctxs[r.IntN(len(ctxs))]
		if ctx.precision == 0 || ctx.precision > 38 {
			continue
		}
		class := divHalf(r.IntN(4))
		tPrime := int64(r.IntN(121) - 60)
		ideal := tPrime + int64(r.IntN(45)-4)
		var etiny int64
		if ctx.guarded {
			etiny = int64(ctx.guards.Emin) - (int64(ctx.precision) - 1)
		}
		negative := r.IntN(2) == 0
		g, gc, gerr, ok := finishContextInline(x.words, class, tPrime, etiny, ideal, negative, &ctx, "DivWithContext")
		if !ok {
			continue
		}
		var buf [6]uint32
		n := 0
		for q := x.words; q != (uint128{}); n++ {
			var rem, digit uint64
			q.hi, rem = bits.Div64(0, q.hi, decimalLimbBase)
			q.lo, digit = bits.Div64(rem, q.lo, decimalLimbBase)
			buf[n] = uint32(digit)
		}
		w, wc, werr := finishContext(buf[:n], class, tPrime, etiny, ideal, negative, &ctx, 0, limits{}, "DivWithContext")
		if werr != nil && werr.Error() == "decimal: DivWithContext: insufficient storage" {
			continue // an unreachable state (t′ above t), which the kernel never produces
		}
		taken++
		samePathOutcome(t, "finish", g, gc, gerr, w, wc, werr)
	}
	if taken < 100000 {
		t.Fatalf("inline finisher taken only %d times", taken)
	}
}

// TestDivWideInlineMatchesGeneral pins division by a two-word divisor and with
// a wide numerator to the general division path.
func TestDivWideInlineMatchesGeneral(t *testing.T) {
	r := randv2.New(randv2.NewPCG(17, 18))
	ctxs := shortContexts()
	for i := range 600000 {
		x, y := shortOperand(r, 30), shortOperand(r, 30)
		if i%2 == 0 {
			y = New(int64(r.Uint64N(pow10Words[1+r.IntN(18)])), int32(r.IntN(21)-10))
		}
		if i%5 == 0 {
			// terminating quotients
			y = New([]int64{2, 4, 5, 8, 16, 25, 125, 625, 1024, 3125, 10, 100, 1}[r.IntN(13)], int32(r.IntN(9)-4))
		}
		ctx := ctxs[r.IntN(len(ctxs))]
		target := int32(r.IntN(91) - 45)
		dg, dgc, dgerr := x.divToExponent(y, target, ctx.rounding, limits{}, "DivToExponent")
		dw, dwc, dwerr := x.divToExponentLimbs(y, target, ctx.rounding, limits{}, "DivToExponent")
		samePathOutcome(t, "divToExponent", dg, dgc, dgerr, dw, dwc, dwerr)
		if ctx.precision != 0 {
			cg, cgc, cgerr := x.divContext(y, ctx, limits{}, "DivWithContext")
			cw, cwc, cwerr := x.divContextLimbs(y, ctx, limits{}, "DivWithContext")
			samePathOutcome(t, "divContext", cg, cgc, cgerr, cw, cwc, cwerr)
		}
	}
}

// TestDivWideMatchesBigInt checks the 256-by-128-bit division against
// math/big.
func TestDivWideMatchesBigInt(t *testing.T) {
	r := randv2.New(randv2.NewPCG(19, 20))
	word := func() uint64 {
		switch r.IntN(9) {
		case 0:
			return 0
		case 1:
			return 1
		case 2:
			return 1<<63 - 1
		case 3:
			return 1 << 63
		case 4:
			return ^uint64(0)
		case 5:
			return ^uint64(0) - 1
		case 6:
			return r.Uint64() >> uint(r.IntN(64))
		default:
			return r.Uint64()
		}
	}
	toBig := func(ws ...uint64) *big.Int {
		z := new(big.Int)
		for _, w := range slices.Backward(ws) {
			z.Lsh(z, 64)
			z.Or(z, new(big.Int).SetUint64(w))
		}
		return z
	}
	limit := new(big.Int).Lsh(big.NewInt(1), 127)
	served, declinedTop := 0, 0
	for range 3000000 {
		v := uint128{word(), word()}
		if v.hi == 0 {
			continue
		}
		var u wide256
		switch r.IntN(3) {
		case 0:
			u = wide256{word(), word(), word(), word()}
		case 1:
			u = wide256{word(), word(), word(), 0}
		default:
			// u = q·v + rem for a chosen inline q: exercises exact and
			// near-exact digits on both sides of the 2^127 bound.
			q := uint128{word(), word() >> 1}
			if r.IntN(8) == 0 {
				q.hi |= 1 << 63
			}
			u = mulWide(q, v)
			rem := uint128{word(), word()}
			if inlineCompare(rem, v) < 0 || r.IntN(2) == 0 {
				u = addWide(u, wide256{rem.lo, rem.hi})
			}
		}
		q, rem, ok := divWide(u, v)
		bu, bv := toBig(u[0], u[1], u[2], u[3]), toBig(v.lo, v.hi)
		bq, br := new(big.Int).QuoRem(bu, bv, new(big.Int))
		if !ok {
			if bq.Cmp(limit) < 0 {
				t.Fatalf("declined a quotient below 2^127: %v / %v", bu, bv)
			}
			if bq.BitLen() == 128 {
				declinedTop++
			}
			continue
		}
		if bq.Cmp(limit) >= 0 {
			t.Fatalf("served a quotient at or above 2^127: %v / %v", bu, bv)
		}
		served++
		if toBig(q.lo, q.hi).Cmp(bq) != 0 || toBig(rem.lo, rem.hi).Cmp(br) != 0 {
			t.Fatalf("divWide(%v, %v) = %v r %v, want %v r %v", bu, bv, toBig(q.lo, q.hi), toBig(rem.lo, rem.hi), bq, br)
		}
		// the two-word kernel of the integer-division path
		if u[2]|u[3] == 0 {
			x := uint128{u[0], u[1]}
			q2, r2 := inlineDivMod(x, v)
			if toBig(q2.lo, q2.hi).Cmp(bq) != 0 || toBig(r2.lo, r2.hi).Cmp(br) != 0 {
				t.Fatalf("inlineDivMod(%v, %v)", bu, bv)
			}
		}
	}
	if declinedTop < 1000 {
		t.Fatalf("only %d quotients in [2^127, 2^128)", declinedTop)
	}
	if served < 500000 {
		t.Fatalf("served only %d", served)
	}
	// inlineDivMod on its own structured inputs, one- and two-word divisors
	for range 2000000 {
		x, v := uint128{word(), word()}, uint128{word(), word()}
		if r.IntN(3) == 0 {
			v.hi = 0
		}
		if v == (uint128{}) {
			continue
		}
		q, rem := inlineDivMod(x, v)
		bq, br := new(big.Int).QuoRem(toBig(x.lo, x.hi), toBig(v.lo, v.hi), new(big.Int))
		if toBig(q.lo, q.hi).Cmp(bq) != 0 || toBig(rem.lo, rem.hi).Cmp(br) != 0 {
			t.Fatalf("inlineDivMod(%v, %v)", x, v)
		}
	}
}

// TestRoundToMultipleInlineMatchesGeneral pins the inline RoundToMultiple to
// the general path.
func TestRoundToMultipleInlineMatchesGeneral(t *testing.T) {
	r := randv2.New(randv2.NewPCG(21, 22))
	steps := []string{"0.05", "0.25", "0.01", "5", "0.5", "1", "0.125", "25", "1E+2", "0.0005", "3", "0.07"}
	for i := range 500000 {
		x := shortOperand(r, 12)
		m := MustParse(steps[r.IntN(len(steps))])
		if i%4 == 0 {
			m = shortOperand(r, 12).Abs()
		}
		if i%9 == 0 && !m.isZero() {
			// exact multiples and exact ties
			k := New(int64(r.Uint64N(100000)), 0)
			x, _ = m.Mul(k)
			if i%2 == 0 {
				h, _ := m.Mul(New(5, -1))
				x, _ = x.Add(h)
			}
			if x.slow != nil {
				continue
			}
		}
		mode := RoundingMode(r.IntN(int(Exact) + 1))
		g, gc, gerr := x.roundToMultiple(m, mode, limits{}, "RoundToMultiple")
		w, wc, werr := x.roundToMultipleLimbs(m, mode, limits{}, "RoundToMultiple")
		samePathOutcome(t, "rtm", g, gc, gerr, w, wc, werr)
	}
}

// TestCompareSameScaleLimbs pins the same-exponent comparison of limb
// coefficients to the general magnitude comparison.
func TestCompareSameScaleLimbs(t *testing.T) {
	r := randv2.New(randv2.NewPCG(23, 24))
	for i := range 300000 {
		x := wideOperand(r, 120, 5)
		y := wideOperand(r, 120, 5)
		if i%2 == 0 {
			// same scale and sign, nearby values
			y = x
			if i%4 == 0 {
				delta := New(int64(r.IntN(5)-2), x.exponent()+int32(9*r.IntN(4)))
				y, _ = x.Add(delta)
				y = y.withExponent(x.exponent())
			}
		}
		got := x.Compare(y)
		want := x.compareGeneral(y)
		if got != want {
			t.Fatalf("Compare(%v, %v) = %d, general %d", x, y, got, want)
		}
		if x.Equal(y) != (want == 0) {
			t.Fatalf("Equal(%v, %v)", x, y)
		}
	}
}

// TestSqrtInlineMatchesGeneral pins the word square root in context to the
// limb Newton path.
func TestSqrtInlineMatchesGeneral(t *testing.T) {
	r := randv2.New(randv2.NewPCG(25, 26))
	ctxs := shortContexts()
	taken := 0
	for i := range 400000 {
		x := shortOperand(r, 40).Abs()
		switch i % 6 {
		case 0: // perfect squares
			s := New(int64(r.Uint64N(pow10Words[1+r.IntN(17)])), int32(r.IntN(21)-10))
			x, _ = s.Mul(s)
		case 1: // just above and below perfect squares, and half-way roots
			s := New(int64(r.Uint64N(pow10Words[1+r.IntN(9)])), 0)
			x, _ = s.Mul(s)
			x, _ = x.Add(New(int64(r.IntN(3)-1), 0))
			x, _ = x.Add(s)
			x = x.Abs().withExponent(int32(r.IntN(21) - 10))
		case 2:
			x = New(int64(1+r.IntN(1000)), int32(r.IntN(9)-4))
		}
		if x.slow != nil {
			continue
		}
		ctx := ctxs[r.IntN(len(ctxs))]
		if ctx.precision == 0 {
			continue
		}
		if !x.isZero() && ctx.precision <= sqrtInlineMaxPrecision {
			cc := ctx
			if _, _, _, ok := x.sqrtContextInline(&cc, "SqrtWithContext"); ok {
				taken++
			}
		}
		g, gc, gerr := x.sqrtContext(ctx, limits{}, "SqrtWithContext", nil)
		w, wc, werr := x.sqrtContext(ctx, limits{}, "SqrtWithContext", &sqrtCount{})
		samePathOutcome(t, "sqrt", g, gc, gerr, w, wc, werr)
	}
	if taken < 100000 {
		t.Fatalf("inline sqrt taken only %d times", taken)
	}
}

// TestSqrtWideMatchesBigInt checks the 256-bit integer root against math/big.
func TestSqrtWideMatchesBigInt(t *testing.T) {
	r := randv2.New(randv2.NewPCG(27, 28))
	word := func() uint64 {
		switch r.IntN(8) {
		case 0:
			return 0
		case 1:
			return 1
		case 2:
			return ^uint64(0)
		case 3:
			return 1 << 63
		case 4:
			return r.Uint64() >> uint(r.IntN(64))
		default:
			return r.Uint64()
		}
	}
	toBig := func(ws ...uint64) *big.Int {
		z := new(big.Int)
		for _, w := range slices.Backward(ws) {
			z.Lsh(z, 64)
			z.Or(z, new(big.Int).SetUint64(w))
		}
		return z
	}
	for range 1500000 {
		n := wide256{word(), word(), word(), word() >> 3} // below 2^253
		switch r.IntN(5) {
		case 0:
			n[3], n[2] = 0, 0
		case 1:
			n[3] = 0
		case 2: // perfect squares and their neighbours
			s := uint128{word(), word() >> 2}
			n = mulWide(s, s)
			switch r.IntN(3) {
			case 0:
				n = addWide(n, wide256{1})
			case 1:
				if n != (wide256{}) {
					n = subWide(n, wide256{1})
				}
			}
		}
		if n == (wide256{}) {
			continue
		}
		got, ok := sqrtWide(n)
		if !ok {
			t.Fatalf("sqrtWide declined %v", toBig(n[0], n[1], n[2], n[3]))
		}
		want := new(big.Int).Sqrt(toBig(n[0], n[1], n[2], n[3]))
		if toBig(got.lo, got.hi).Cmp(want) != 0 {
			t.Fatalf("sqrtWide(%v) = %v, want %v", toBig(n[0], n[1], n[2], n[3]), toBig(got.lo, got.hi), want)
		}
	}
}

// TestParseRoundedWordsMatchesGeneral pins ParseWithContext of a literal of up
// to 38 bytes to the rounding-source path.
func TestParseRoundedWordsMatchesGeneral(t *testing.T) {
	r := randv2.New(randv2.NewPCG(29, 30))
	ctxs := shortContexts()
	for range 500000 {
		n := 1 + r.IntN(36)
		buf := make([]byte, 0, 48)
		if r.IntN(3) == 0 {
			buf = append(buf, "+-"[r.IntN(2)])
		}
		point := -1
		if r.IntN(4) != 0 {
			point = r.IntN(n + 1)
		}
		kind := r.IntN(8)
		for j := range n {
			if j == point {
				buf = append(buf, '.')
			}
			switch kind {
			case 0:
				buf = append(buf, '9')
			case 1:
				buf = append(buf, '0')
			case 2:
				buf = append(buf, "05"[r.IntN(2)])
			default:
				buf = append(buf, byte('0'+r.IntN(10)))
			}
		}
		if r.IntN(4) == 0 {
			buf = append(buf, 'E')
			buf = strconv.AppendInt(buf, int64(r.IntN(121)-60), 10)
		}
		if r.IntN(50) == 0 {
			buf = append(buf, 'x') // syntax error
		}
		s := string(buf)
		ctx := ctxs[r.IntN(len(ctxs))]
		if ctx.precision == 0 {
			continue
		}
		g, gc, gerr := parseWithContext(s, ctx, textLimits{}, "ParseWithContext")
		w, wc, werr := parseRounded(s, ctx, textLimits{}, "ParseWithContext")
		if (gerr == nil) != (werr == nil) || gerr != nil && gerr.Error() != werr.Error() {
			t.Fatalf("parse %q p=%d: error %v vs %v", s, ctx.precision, gerr, werr)
		}
		if gerr != nil {
			continue
		}
		samePathOutcome(t, "parse "+s, g, gc, gerr, w, wc, werr)
	}
}

func roundingLiteral(r *randv2.Rand) string {
	n := 1 + r.IntN(36)
	buf := make([]byte, 0, 48)
	if r.IntN(3) == 0 {
		buf = append(buf, "+-"[r.IntN(2)])
	}
	point := -1
	if r.IntN(4) != 0 {
		point = r.IntN(n + 1)
	}
	kind := r.IntN(8)
	for j := range n {
		if j == point {
			buf = append(buf, '.')
		}
		switch kind {
		case 0:
			buf = append(buf, '9')
		case 1:
			buf = append(buf, '0')
		case 2:
			buf = append(buf, "05"[r.IntN(2)])
		default:
			buf = append(buf, byte('0'+r.IntN(10)))
		}
	}
	if r.IntN(4) == 0 {
		buf = append(buf, 'E')
		buf = strconv.AppendInt(buf, int64(r.IntN(121)-60), 10)
	}
	if r.IntN(50) == 0 {
		buf = append(buf, 'x') // syntax error
	}
	return string(buf)
}

// TestParseToExponentWordsMatchesSource pins ParseToExponent of a literal of
// up to 38 bytes to the rounding-source path.
func TestParseToExponentWordsMatchesSource(t *testing.T) {
	r := randv2.New(randv2.NewPCG(31, 32))
	budgets := []textLimits{{}, {MaxDigits: 39}, {MaxDigits: 38}, {MaxDigits: 40, MaxInputBytes: 64}, {MaxDigits: 5}, {MaxInputBytes: 10}, {MaxDigits: 1 << 20, MaxInputBytes: 1 << 20}}
	for range 600000 {
		s := roundingLiteral(r)
		target := int32(r.IntN(81) - 40)
		mode := RoundingMode(r.IntN(int(Exact) + 1))
		b := budgets[r.IntN(len(budgets))]
		g, gc, gerr := parseToExponent(s, target, mode, b, "ParseToExponent")
		w, wc, werr := parseToExponentSource(s, target, mode, b, "ParseToExponent")
		if (gerr == nil) != (werr == nil) || gerr != nil && gerr.Error() != werr.Error() {
			t.Fatalf("parse %q -> %d %v budget %+v: error %v vs %v", s, target, mode, b, gerr, werr)
		}
		if gerr != nil {
			continue
		}
		samePathOutcome(t, "parseToExponent "+s, g, gc, gerr, w, wc, werr)
	}
}

// displayOperand returns shortOperand's inline decimal, sometimes moved to
// an exponent at either int32 end. A nonzero value keeps a moderate or a
// very negative exponent when fixed is set, since Fixed renders every digit
// down to the units.
func displayOperand(r *randv2.Rand, fixed bool) Decimal {
	d := shortOperand(r, 45)
	switch r.IntN(48) {
	case 0:
		return d.withExponent(math.MinInt32 + int32(r.IntN(60)))
	case 1:
		if !fixed || d.isZero() {
			return d.withExponent(math.MaxInt32 - int32(r.IntN(60)))
		}
	}
	return d
}

// TestDisplayInlineMatchesPlanner pins the inline Fixed, Scientific and
// Engineering paths to the planner in every rounding mode: the same text,
// the same error identity and, under a budget, the same refusal, with
// budgets at each admission threshold and one below it and the budget of
// the estimate. The string and append forms are both checked. Counters
// require every inline class to be served and every threshold to be hit.
func TestDisplayInlineMatchesPlanner(t *testing.T) {
	r := randv2.New(randv2.NewPCG(41, 42))
	count := map[string]int{}
	prefix := []byte("x=")
	type call struct {
		text   func(Budget) (string, error)
		bytes  func(Budget) ([]byte, error)
		plan   func(Budget) (string, error)
		served func(Budget) bool
		cost   func() (Cost, error)
	}
	same := func(what string, d Decimal, b Budget, got string, gerr error, want string, werr error) {
		t.Helper()
		if got != want || (gerr == nil) != (werr == nil) || gerr != nil && gerr.Error() != werr.Error() {
			t.Fatalf("%s of %v (e=%d) budget %+v = %q, %v; planner %q, %v", what, d, d.exponent(), b, got, gerr, want, werr)
		}
	}
	for i := range 300000 {
		kind := displayKind(i % 3)
		d := displayOperand(r, kind == displayFixed)
		mode := RoundingMode(r.IntN(int(Exact) + 1))
		if r.IntN(200) == 0 {
			mode = Exact + 1
		}
		places := uint64(r.IntN(45))
		if r.IntN(100) == 0 {
			places = uint64(r.IntN(2000))
		}
		var c call
		var name string
		var wide [inlineTextMax]byte
		switch kind {
		case displayFixed:
			name = "fixed"
			c = call{
				text: func(b Budget) (string, error) {
					return d.FixedWithOptions(places, DisplayOptions{Mode: mode, Budget: b})
				},
				bytes: func(b Budget) ([]byte, error) {
					return d.AppendFixed(slices.Clone(prefix), places, DisplayOptions{Mode: mode, Budget: b})
				},
				plan: func(b Budget) (string, error) {
					return d.display(displayFixed, places, DisplayOptions{Mode: mode, Budget: b}, "FixedWithOptions")
				},
				served: func(b Budget) bool {
					if mode == TiesToEven {
						if _, ok := d.fixedTiesToEvenAdmitted(places, b.display()); ok {
							count["fixed/word"]++
							return true
						}
					}
					_, ok := d.fixedInline(&wide, places, mode, b.display())
					return ok
				},
				cost: func() (Cost, error) { return EstimateFixed(d.Shape(), places, mode) },
			}
			if mode == TiesToEven {
				got, gerr := d.Fixed(places)
				want, werr := d.display(displayFixed, places, DisplayOptions{}, "Fixed")
				same("Fixed", d, Budget{}, got, gerr, want, werr)
			}
		case displayScientific:
			name = "scientific"
			c = call{
				text: func(b Budget) (string, error) {
					return d.ScientificWithOptions(places, DisplayOptions{Mode: mode, Budget: b})
				},
				bytes: func(b Budget) ([]byte, error) {
					return d.AppendScientific(slices.Clone(prefix), places, DisplayOptions{Mode: mode, Budget: b})
				},
				plan: func(b Budget) (string, error) {
					return d.display(displayScientific, places, DisplayOptions{Mode: mode, Budget: b}, "ScientificWithOptions")
				},
				served: func(b Budget) bool {
					var buf [scientificInlineMax]byte
					if mode == TiesToEven {
						if j, ok := d.scientificTiesToEven(&buf, places); ok && b.display().admitsWord(d.words.lo, len(buf)-j) {
							count["scientific/word"]++
							return true
						}
					}
					_, ok := d.scientificInline(&wide, places, mode, b.display())
					return ok
				},
				cost: func() (Cost, error) { return EstimateScientific(d.Shape(), places, mode) },
			}
			if mode == TiesToEven {
				got, gerr := d.Scientific(places)
				want, werr := d.display(displayScientific, places, DisplayOptions{}, "Scientific")
				same("Scientific", d, Budget{}, got, gerr, want, werr)
			}
		default:
			name = "engineering"
			mode, places = TiesToEven, 0
			c = call{
				text:  d.EngineeringWithBudget,
				bytes: func(b Budget) ([]byte, error) { return d.AppendEngineering(slices.Clone(prefix), b) },
				plan: func(b Budget) (string, error) {
					return d.display(displayEngineering, 0, DisplayOptions{Budget: b}, "EngineeringWithBudget")
				},
				served: func(b Budget) bool {
					_, ok := d.engineeringInline(&wide, b.display())
					return ok
				},
				cost: func() (Cost, error) { return EstimateEngineering(d.Shape()) },
			}
			got, gerr := d.Engineering()
			want, werr := d.display(displayEngineering, 0, DisplayOptions{}, "Engineering")
			same("Engineering", d, Budget{}, got, gerr, want, werr)
		}
		check := func(b Budget) (text string, err error, served bool) {
			t.Helper()
			want, werr := c.plan(b)
			got, gerr := c.text(b)
			same(name, d, b, got, gerr, want, werr)
			appended, aerr := c.bytes(b)
			if werr != nil {
				want = ""
			}
			if string(appended) != string(prefix)+want || (aerr == nil) != (werr == nil) || aerr != nil && aerr.(*Error).Code != werr.(*Error).Code {
				t.Fatalf("%s append of %v budget %+v = %q, %v; planner %q, %v", name, d, b, appended, aerr, want, werr)
			}
			served = c.served(b)
			if served && werr != nil {
				t.Fatalf("%s of %v budget %+v: inline path served a call the planner refuses: %v", name, d, b, werr)
			}
			return want, werr, served
		}
		text, err, served := check(Budget{})
		check(Budget{MaxOutputBytes: uint64(1 + r.IntN(50)), MaxWork: uint64(r.IntN(100))})
		if err != nil {
			if errors.Is(err, ErrInexact) {
				count[name+"/exact refusal"]++
			} else {
				count[name+"/invalid"]++
			}
			continue
		}
		if !served {
			count[name+"/deferred"]++
			continue
		}
		count[name]++
		count[name+"/"+mode.String()]++
		n, size := d.CoefficientDigits(), uint64(len(text))
		digits := strings.Trim(text, "-")
		switch {
		case d.isZero():
			count[name+"/zero"]++
		case d.words.hi != 0:
			count[name+"/two words"]++
		}
		switch kind {
		case displayFixed:
			shift := int64(d.exponent()) + int64(places)
			switch {
			case d.isZero():
			case shift > 0:
				count["fixed/padded"]++
			case shift < -19:
				count["fixed/far cut"]++
			case shift < 0:
				count["fixed/cut"]++
			}
			if !d.isZero() && strings.Trim(text, "-0.") == "" {
				count["fixed/rounded to zero"]++
			}
			if len(strings.ReplaceAll(digits, ".", "")) > 20 {
				count["fixed/two-word result"]++
			}
		case displayScientific:
			adjusted := int64(d.exponent()) + int64(n) - 1
			if x, _ := strconv.ParseInt(digits[strings.IndexByte(digits, 'E')+1:], 10, 64); !d.isZero() && x != adjusted {
				if x != adjusted+1 {
					t.Fatalf("Scientific(%d) of %v = %q: exponent %d, adjusted %d", places, d, text, x, adjusted)
				}
				count["scientific/carry"]++
			}
			switch {
			case n <= places && !d.isZero():
				count["scientific/padded"]++
			case n-places > 19:
				count["scientific/far cut"]++
			}
			if places > 20 {
				count["scientific/two-word result"]++
			}
		case displayEngineering:
			leading := strings.IndexAny(digits, ".E")
			count[name+"/leading "+strconv.Itoa(leading)]++
			if !d.isZero() && uint64(leading) > n {
				count["engineering/padded"]++
			}
			if strings.Contains(text, "E-") {
				count["engineering/negative exponent"]++
			}
		}
		// The planner admits size bytes and n+size work units and nothing
		// below; the inline paths serve exactly the admitted budgets.
		for _, tc := range []struct {
			class  string
			budget Budget
			admits bool
		}{
			{"output threshold", Budget{MaxOutputBytes: size}, true},
			{"output below", Budget{MaxOutputBytes: size - 1}, size == 1},
			{"work threshold", Budget{MaxWork: n + size}, true},
			{"work below", Budget{MaxWork: n + size - 1}, false},
			{"both thresholds", Budget{MaxOutputBytes: size, MaxWork: n + size}, true},
			{"other axes", Budget{MaxDigits: 1, MaxInputBytes: 1, MaxInputDigits: 1}, true},
		} {
			_, err, served := check(tc.budget)
			if (err == nil) != tc.admits || served != tc.admits {
				t.Fatalf("%s of %v, %s %+v: planner %v, served inline %v, want admitted %v", name, d, tc.class, tc.budget, err, served, tc.admits)
			}
			count[name+"/"+tc.class]++
		}
		estimate, err := c.cost()
		if err != nil {
			t.Fatalf("%s estimate of %v: %v", name, d, err)
		}
		if _, err, served := check(estimate.Budget()); err != nil || !served {
			t.Fatalf("%s of %v under its estimate %+v: planner %v, served inline %v", name, d, estimate, err, served)
		}
	}
	for _, class := range []string{
		"fixed", "fixed/word", "fixed/zero", "fixed/two words", "fixed/padded", "fixed/cut", "fixed/far cut",
		"fixed/rounded to zero", "fixed/two-word result", "fixed/exact refusal", "fixed/invalid", "fixed/deferred",
		"fixed/output threshold", "fixed/output below", "fixed/work threshold", "fixed/work below",
		"scientific", "scientific/word", "scientific/zero", "scientific/two words", "scientific/padded",
		"scientific/far cut", "scientific/carry", "scientific/two-word result", "scientific/exact refusal",
		"scientific/invalid", "scientific/deferred", "scientific/output threshold", "scientific/output below",
		"scientific/work threshold", "scientific/work below",
		"engineering", "engineering/zero", "engineering/two words", "engineering/padded", "engineering/leading 1",
		"engineering/leading 2", "engineering/leading 3", "engineering/negative exponent",
		"engineering/output threshold", "engineering/output below", "engineering/work threshold", "engineering/work below",
	} {
		if count[class] < 100 {
			t.Fatalf("vacuous coverage: class %q has %d cases (%v)", class, count[class], count)
		}
	}
	for mode := TiesToEven; mode <= Exact; mode++ {
		if count["fixed/"+mode.String()] < 1000 || count["scientific/"+mode.String()] < 1000 {
			t.Fatalf("vacuous coverage: mode %v served %d Fixed and %d Scientific calls", mode, count["fixed/"+mode.String()], count["scientific/"+mode.String()])
		}
	}
	if count["engineering/deferred"] != 0 {
		t.Fatalf("Engineering deferred %d unbudgeted inline values", count["engineering/deferred"])
	}

	// An inline text appended within appendInlineRoom stays within the
	// planner's limit on every target.
	if limit := displayLimit(); limit < math.MaxInt32 || !appendInlineRoom(math.MaxInt32-inlineTextMax) || appendInlineRoom(math.MaxInt32-inlineTextMax+1) {
		t.Fatalf("appendInlineRoom does not match displayLimit %d", limit)
	}

	// A refused budgeted call allocates only its error.
	v, w := MustParse("-123456.789012"), MustParse("12345678901234567890123.456789012345")
	tight := DisplayOptions{Budget: Budget{MaxOutputBytes: 3}}
	for name, refused := range map[string]func() error{
		"Fixed":       func() error { _, err := v.FixedWithOptions(2, tight); return err },
		"Fixed/wide":  func() error { _, err := w.FixedWithOptions(2, tight); return err },
		"Scientific":  func() error { _, err := v.ScientificWithOptions(6, tight); return err },
		"Engineering": func() error { _, err := w.EngineeringWithBudget(tight.Budget); return err },
	} {
		if err := refused(); !errors.Is(err, ErrInsufficientStorage) {
			t.Fatalf("%s under %+v: %v", name, tight.Budget, err)
		}
		if allocs := testing.AllocsPerRun(50, func() { _ = refused() }); allocs > 1 {
			t.Fatalf("%s refusal allocates %.0f times", name, allocs)
		}
	}
}

// TestFromFloat64ToExponentBudgetedInlineMatchesGeneral pins the budgeted
// inline conversion to the general expansion under the same budget: the
// same value, exponent, Conditions and refusal. The gate must admit exactly
// the budgets the general path admits, which the test checks at the tariff
// W = B + 2N + 1 and the digit count N of each result, one below each, and
// under the budget of the estimate.
func TestFromFloat64ToExponentBudgetedInlineMatchesGeneral(t *testing.T) {
	r := randv2.New(randv2.NewPCG(43, 44))
	const op = "FromFloat64ToExponentWithBudget"
	var served, refused, padded, far, zero, estimated int
	for range 300000 {
		var f float64
		switch r.IntN(5) {
		case 0:
			f = math.Float64frombits(r.Uint64())
		case 1:
			f = float64(r.Int64N(1e12)) / 100
		case 2:
			f = math.Ldexp(float64(r.Int64N(1<<53)), r.IntN(80)-60) // exact values and ties
		case 3:
			f = r.NormFloat64() * math.Pow(10, float64(r.IntN(40)-20))
		default:
			f = math.Ldexp(1+r.Float64(), -r.IntN(1070))
		}
		if r.IntN(2) == 0 {
			f = -f
		}
		target := int32(-r.IntN(20))
		if r.IntN(30) == 0 {
			target = int32(r.IntN(50) - 30)
		}
		mode := RoundingMode(r.IntN(int(Exact) + 1))
		if r.IntN(100) == 0 {
			mode = Exact + 1
		}
		budgets := []Budget{{}, {MaxDigits: uint64(1 + r.IntN(40)), MaxWork: uint64(r.IntN(9000))}, {MaxWork: uint64(1 + r.IntN(600))}, {MaxDigits: uint64(1 + r.IntN(20))}}
		fast, _, inline := float64ToExponentInline(f, target, mode)
		thresholds := 0
		if inline {
			// The documented tariff of the general path, restated.
			_, _, e := binary64Parts(f)
			passes := uint64(e+28) / 29
			var pad uint64
			if e < 0 {
				passes = uint64(-e+12) / 13
				if int64(target) < e {
					pad = uint64(e - int64(target))
				}
			} else if target < 0 {
				pad = uint64(-int64(target))
			}
			n := fast.CoefficientDigits()
			w := 87*passes + (pad+8)/9 + 2*n + 1
			budgets = append(budgets, Budget{MaxDigits: n, MaxWork: w}, Budget{MaxWork: w}, Budget{MaxDigits: n}, Budget{MaxDigits: n, MaxWork: w - 1})
			thresholds = 3
			if n > 1 {
				budgets = append(budgets, Budget{MaxDigits: n - 1, MaxWork: w})
			}
			if pad != 0 {
				padded++
			}
			if e <= -128 {
				far++
			}
			if fast.isZero() {
				zero++
			}
			estimate, err := EstimateFromFloat64ToExponent(f, target)
			if err != nil {
				t.Fatalf("estimate of %v -> %d: %v", f, target, err)
			}
			if !float64ToExponentAdmitted(f, target, fast, estimate.Budget().arith()) {
				t.Fatalf("%v -> %d: the gate declines the estimate %+v", f, target, estimate)
			}
			estimated++
		}
		for i, b := range budgets {
			got, gc, gerr := FromFloat64ToExponentWithBudget(f, target, mode, b)
			want, wc, werr := fromFloat64ToExponent(f, target, mode, b.arith(), op)
			samePathOutcome(t, op, got, gc, gerr, want, wc, werr)
			if !inline {
				continue
			}
			admitted := float64ToExponentAdmitted(f, target, fast, b.arith())
			if admitted != (werr == nil) {
				t.Fatalf("%v -> %d mode %v budget %+v: gate admits %v, general path %v", f, target, mode, b, admitted, werr)
			}
			// The first four budgets are free; then come the thresholds,
			// which admit, and the budgets one below, which refuse.
			if i >= 4 && admitted != (i < 4+thresholds) {
				t.Fatalf("%v -> %d mode %v budget %+v: admitted %v at threshold index %d", f, target, mode, b, admitted, i-4)
			}
			if b != (Budget{}) {
				if admitted {
					served++
				} else {
					refused++
				}
			}
		}
	}
	if served < 100000 || refused < 100000 || padded < 10000 || far < 10000 || zero < 10000 || estimated < 100000 {
		t.Fatalf("vacuous coverage: %d served, %d refused, %d padded, %d far, %d zero, %d estimated", served, refused, padded, far, zero, estimated)
	}
}

// fmaShortOperands returns three inline operands for the FMA differentials:
// factors whose product often stays below 2^128 and an addend within reach
// of it, with a share of extreme shapes (twenty-digit factors, a 39-digit
// addend of the opposite sign at the product's exponent or 38 places from
// it) that reach the largest charges of the general path.
func fmaShortOperands(r *randv2.Rand) (x, y, z Decimal) {
	x, y, z = shortOperand(r, 20), shortOperand(r, 20), shortOperand(r, 20)
	switch r.IntN(16) {
	case 0:
		wide := []string{"18446744073709551615", "10000000000000000000", "99999999999999999999", "12345678901234567890"}
		x = MustParse(wide[r.IntN(len(wide))]).withExponent(x.exponent())
		y = MustParse(wide[r.IntN(len(wide))]).withExponent(y.exponent()).withNegative(r.IntN(2) == 0)
		tall := []string{"340282366920938463463374607431768211455", "100000000000000000000000000000000000000", "99999999999999999999999999999999999999"}
		z = MustParse(tall[r.IntN(len(tall))]).withNegative(!y.negative())
		gap := int32(38 - r.IntN(3))
		switch r.IntN(3) {
		case 0:
			gap = 0
		case 1:
			gap = -gap
		}
		z = z.withExponent(x.exponent() + y.exponent() - gap)
	case 1:
		// Exponent sums at and beyond the int32 ends; the addend stays near
		// them, since the bare sum spans the whole exponent gap.
		x = x.withExponent(math.MaxInt32 - int32(r.IntN(30)))
		z = z.withExponent(math.MaxInt32 - int32(r.IntN(60)))
	case 2:
		x = x.withExponent(math.MinInt32 + int32(r.IntN(30)))
		z = z.withExponent(math.MinInt32 + int32(r.IntN(60)))
	}
	return x, y, z
}

// fmaInlineServed reports whether the inline FMA path returns a result for
// the operands under ctx when its budget gate is open, and by which route.
func fmaInlineServed(x, y, z Decimal, ctx Context) (route string, served bool) {
	product, ok := inlineMul(x, y)
	if !ok {
		return "", false
	}
	if ctx.precision == 0 {
		_, ok = inlineAddSub(product, z, false)
		return "bare", ok
	}
	if exact, ok := inlineAddSub(product, z, false); ok {
		if contextExactFits(exact, ctx) {
			return "context exact", true
		}
		_, _, ok = contextRoundInline(exact, ctx)
		return "context rounded", ok
	}
	_, _, served, _ = product.contextAddSubInline(z, ctx, "FMAWithContext", false)
	return "context wide", served
}

// TestFMABudgetedInlineMatchesGeneral pins budgeted FMA calls served inline
// to the product-term path under the same budget, bare and in context: the
// same value, cohort, Conditions and error. Where the inline path serves a
// call under a budget its gate admits, the product-term path must not
// refuse for resources; the budgets include each gate's threshold and one
// below it on each axis.
func TestFMABudgetedInlineMatchesGeneral(t *testing.T) {
	r := randv2.New(randv2.NewPCG(45, 46))
	ctxs := shortContexts()
	budgets := []limits{{}, {contextFMAInlineDigits, contextFMAInlineWork}, {contextFMAInlineDigits, contextFMAInlineWork - 1},
		{contextFMAInlineDigits - 1, contextFMAInlineWork}, {fmaInlineDigits, fmaInlineWork}, {fmaInlineDigits, fmaInlineWork - 1},
		{fmaInlineDigits - 1, fmaInlineWork}, {0, contextFMAInlineWork}, {contextFMAInlineDigits, 0}, {0, fmaInlineWork},
		{fmaInlineDigits, 0}, {1 << 20, 1 << 40}, {20, 120}, {78, 200}, {16, 90}, {40, 300}}
	served := map[string]int{}
	for range 400000 {
		x, y, z := fmaShortOperands(r)
		ctx := ctxs[r.IntN(len(ctxs))]
		if r.IntN(4) == 0 {
			ctx = Context{}
		}
		route, inline := fmaInlineServed(x, y, z, ctx)
		gateDigits, gateWork := uint64(contextFMAInlineDigits), uint64(contextFMAInlineWork)
		if ctx.precision == 0 {
			gateDigits, gateWork = fmaInlineDigits, fmaInlineWork
		}
		for range 3 {
			b := budgets[r.IntN(len(budgets))]
			bc := ctx.withLimits(b)
			got, gc, gerr := x.FMAWithContext(y, z, bc)
			want, wc, werr := x.fmaGeneral(y, z, bc)
			samePathOutcome(t, "FMA "+route, got, gc, gerr, want, wc, werr)
			if !inline || !b.admits(gateDigits, gateWork) {
				continue
			}
			if errors.Is(werr, ErrInsufficientStorage) {
				t.Fatalf("FMA(%v, %v, %v) p=%d budget %+v: the gate admits a call the product-term path refuses: %v", x, y, z, ctx.precision, b, werr)
			}
			if b != (limits{}) {
				served[route]++
				if b == (limits{gateDigits, gateWork}) {
					served[route+" at threshold"]++
				}
			}
		}
	}
	for _, route := range []string{"bare", "context exact", "context rounded", "context wide"} {
		if served[route] < 2000 || served[route+" at threshold"] < 200 {
			t.Fatalf("vacuous coverage: %v", served)
		}
	}
}

// TestFMAInlineBudgetBoundsDominateEstimates checks the constant bounds of
// the FMA budget gates against the estimators, which bound the product-term
// path's charges for a shape: on every shape an inline path serves, the
// work bound is at least the estimate, and so is the digit bound wherever
// the estimate's digits are the result's (the bare form, and a context
// whose precision keeps the result inline). The largest estimates must
// reach the bounds, so the bounds are not loose.
func TestFMAInlineBudgetBoundsDominateEstimates(t *testing.T) {
	r := randv2.New(randv2.NewPCG(47, 48))
	ctxs := shortContexts()
	var bare, context, bareWork, bareDigits, contextWork uint64
	for range 400000 {
		x, y, z := fmaShortOperands(r)
		ctx := ctxs[r.IntN(len(ctxs))]
		if r.IntN(4) == 0 {
			ctx = Context{}
		}
		if _, inline := fmaInlineServed(x, y, z, ctx); !inline {
			continue
		}
		if x.isZero() || y.isZero() || z.isZero() {
			// The estimate of a zero shape also covers its exponent gap,
			// which the general path does not charge; the differential
			// test pins the zero shapes directly.
			continue
		}
		c, err := EstimateFMA(x.Shape(), y.Shape(), z.Shape(), ctx)
		if err != nil {
			t.Fatalf("EstimateFMA(%v, %v, %v) p=%d: %v", x, y, z, ctx.precision, err)
		}
		if ctx.precision == 0 {
			if c.WorkUnits > fmaInlineWork || c.Digits > fmaInlineDigits {
				t.Fatalf("bare FMA bound: %v %v %v: %+v", x, y, z, c)
			}
			bare, bareWork, bareDigits = bare+1, max(bareWork, c.WorkUnits), max(bareDigits, c.Digits)
			continue
		}
		if ctx.guarded {
			continue // the estimate also covers the overflow result, of precision digits
		}
		if c.WorkUnits > contextFMAInlineWork || ctx.precision <= contextFMAInlineDigits && c.Digits > contextFMAInlineDigits {
			t.Fatalf("context FMA bound: %v %v %v p=%d: %+v", x, y, z, ctx.precision, c)
		}
		context, contextWork = context+1, max(contextWork, c.WorkUnits)
	}
	if bare < 10000 || context < 10000 {
		t.Fatalf("vacuous coverage: %d bare, %d context", bare, context)
	}
	if bareWork != fmaInlineWork || bareDigits != fmaInlineDigits || contextWork != contextFMAInlineWork {
		t.Fatalf("loose bounds: largest estimates %d work and %d digits bare, %d work in context", bareWork, bareDigits, contextWork)
	}
}

// TestInlineReduceWideMatchesGeneral pins Reduce and Hash of a two-word
// coefficient to the general limb path and to a math/big oracle, over every
// count of trailing zeros and the MaxInt32 exponent ceiling.
func TestInlineReduceWideMatchesGeneral(t *testing.T) {
	r := randv2.New(randv2.NewPCG(49, 50))
	seed := maphash.MakeSeed()
	digest := func(hash func(*maphash.Hash, Decimal), d Decimal) uint64 {
		var h maphash.Hash
		h.SetSeed(seed)
		hash(&h, d)
		return h.Sum64()
	}
	ten := big.NewInt(10)
	var stripped [39]int
	var served, deferred, ceiling, oneWord, twoWords int
	for range 400000 {
		// c·10^zeros below 2^128 and at least 2^64.
		zeros := r.IntN(39)
		c := uint128{lo: r.Uint64(), hi: r.Uint64()}
		if shift := uint(r.IntN(128)); shift >= 64 {
			c = uint128{lo: c.hi >> (shift - 64)}
		} else if shift > 0 {
			c = uint128{lo: c.lo>>shift | c.hi<<(64-shift), hi: c.hi >> shift}
		}
		if r.IntN(8) == 0 {
			c = uint128{lo: uint64(1 + r.IntN(9))}
		}
		w, ok := inlineScale(c, uint64(zeros))
		if !ok || w.hi == 0 {
			continue
		}
		exponent := int32(r.IntN(60) - 30)
		if r.IntN(5) == 0 {
			exponent = math.MaxInt32 - int32(r.IntN(45))
		}
		d := inlineDecimal(w, exponent, r.IntN(2) == 0)
		got, want := d.Reduce(), reduceGeneral(d)
		if !sameRepresentation(got, want) {
			t.Fatalf("Reduce(%v e=%d) = %v e=%d; general path %v e=%d", d, exponent, got, got.exponent(), want, want.exponent())
		}
		// The oracle strips zeros from the big.Int coefficient one at a time.
		value := new(big.Int).SetUint64(w.hi)
		value.Lsh(value, 64).Add(value, new(big.Int).SetUint64(w.lo))
		n := 0
		for q, m := new(big.Int), new(big.Int); int64(exponent)+int64(n) < math.MaxInt32; n++ {
			if q.QuoRem(value, ten, m); m.Sign() != 0 {
				break
			}
			value.Set(q)
		}
		reduced := new(big.Int).SetUint64(got.words.hi)
		reduced.Lsh(reduced, 64).Add(reduced, new(big.Int).SetUint64(got.words.lo))
		if got.slow != nil || reduced.Cmp(value) != 0 || int64(got.exponent()) != int64(exponent)+int64(n) || got.negative() != d.negative() {
			t.Fatalf("Reduce(%v e=%d) = %v e=%d; oracle %v e=%d", d, exponent, got, got.exponent(), value, int64(exponent)+int64(n))
		}
		if h, ref, slow := digest(Hasher{}.Hash, d), digest(hashReference, d), digest(Hasher{}.Hash, asSlowBand(d)); h != ref || h != slow {
			t.Fatalf("Hash(%v e=%d) = %x; reference %x, limb carrier %x", d, exponent, h, ref, slow)
		}
		if h, same := digest(Hasher{}.Hash, d), digest(Hasher{}.Hash, got); h != same {
			t.Fatalf("Hash(%v e=%d) = %x; its reduced form hashes to %x", d, exponent, h, same)
		}
		if n == 0 {
			continue
		}
		stripped[n]++
		if fast, ok := inlineReduceWide(d); ok {
			if !sameRepresentation(fast, want) {
				t.Fatalf("inlineReduceWide(%v e=%d) = %v e=%d; general path %v e=%d", d, exponent, fast, fast.exponent(), want, want.exponent())
			}
			served++
		} else {
			deferred++
		}
		if int64(exponent)+int64(n) == math.MaxInt32 {
			ceiling++
		}
		if got.words.hi == 0 {
			oneWord++
		} else {
			twoWords++
		}
	}
	for n := 1; n <= 38; n++ {
		if stripped[n] < 20 {
			t.Fatalf("vacuous coverage: %d values with %d removable zeros", stripped[n], n)
		}
	}
	if served < 50000 || deferred < 5000 || ceiling < 1000 || oneWord < 10000 || twoWords < 10000 {
		t.Fatalf("vacuous coverage: %d served, %d deferred, %d at the ceiling, %d one-word and %d two-word results", served, deferred, ceiling, oneWord, twoWords)
	}
}

// TestRoundToMultipleBudgetedInlineMatchesGeneral pins budgeted
// RoundToMultiple calls served inline to the general path under the same
// budget: the same value, cohort, Conditions and error. Where the inline
// path serves a call under a budget its gate admits, the general path must
// not refuse for resources; the budgets include the gate's threshold and
// one below it on each axis.
func TestRoundToMultipleBudgetedInlineMatchesGeneral(t *testing.T) {
	r := randv2.New(randv2.NewPCG(51, 52))
	const op = "RoundToMultipleWithBudget"
	gate := limits{roundToMultipleInlineDigits, roundToMultipleInlineWork}
	budgets := []limits{{}, gate, {gate.MaxDigits, gate.MaxWork - 1}, {gate.MaxDigits - 1, gate.MaxWork}, {0, gate.MaxWork},
		{gate.MaxDigits, 0}, {1 << 20, 1 << 40}, {20, 120}, {39, 290}, {12, 60}, {78, 200}}
	steps := []string{"0.05", "0.25", "0.01", "5", "0.5", "1", "0.125", "25", "1E+2", "0.0005", "3", "0.07"}
	var served, threshold, zero, long, refusedBelow int
	for i := range 500000 {
		x := shortOperand(r, 12)
		m := MustParse(steps[r.IntN(len(steps))])
		switch i % 4 {
		case 0:
			m = shortOperand(r, 12).Abs()
		case 1:
			// A long step under a long quotient, toward the largest charges.
			m = shortOperand(r, 3).Abs()
			x = shortOperand(r, 3).withExponent(m.exponent() + int32(r.IntN(25)))
		}
		if i%9 == 0 && !m.isZero() {
			// exact multiples and exact ties
			k := New(int64(r.Uint64N(100000)), 0)
			x, _ = m.Mul(k)
			if i%2 == 0 {
				h, _ := m.Mul(New(5, -1))
				x, _ = x.Add(h)
			}
			if x.slow != nil {
				continue
			}
		}
		if i%101 == 0 {
			m = m.Neg()
		}
		mode := RoundingMode(r.IntN(int(Exact) + 1))
		if i%103 == 0 {
			mode = Exact + 1
		}
		inline, zeroQuotient, digits := false, false, uint64(0)
		if mode <= Exact && !m.negative() && inlineDivShape(x, m) {
			unit := m.withExponent(0)
			if q, _, refused, ok := inlineDivToExponent(x, unit, m.exponent(), mode); ok && !refused {
				zeroQuotient = q.isZero()
				product, fits := inlineMul(q.withExponent(0), unit)
				inline = zeroQuotient || fits
				if fits && !zeroQuotient {
					digits = inlineDigits(product.words)
				}
			}
		}
		for range 3 {
			b := budgets[r.IntN(len(budgets))]
			got, gc, gerr := x.roundToMultiple(m, mode, b, op)
			want, wc, werr := x.roundToMultipleLimbs(m, mode, b, op)
			samePathOutcome(t, "RoundToMultiple", got, gc, gerr, want, wc, werr)
			if !inline {
				continue
			}
			if !b.admits(gate.MaxDigits, gate.MaxWork) {
				if errors.Is(werr, ErrInsufficientStorage) {
					refusedBelow++
				}
				continue
			}
			if errors.Is(werr, ErrInsufficientStorage) {
				t.Fatalf("RoundToMultiple(%v, %v) mode %v budget %+v: the gate admits a call the general path refuses: %v", x, m, mode, b, werr)
			}
			if b == (limits{}) {
				continue
			}
			served++
			if b == gate {
				threshold++
			}
			if zeroQuotient {
				zero++
			}
			if digits >= 36 {
				long++
			}
		}
	}
	if served < 100000 || threshold < 10000 || zero < 1000 || long < 1000 || refusedBelow < 1000 {
		t.Fatalf("vacuous coverage: %d served, %d at the threshold, %d zero quotients, %d long products, %d refused below the gate", served, threshold, zero, long, refusedBelow)
	}
}

// TestFromBigIntBudgetedInlineMatchesGeneral pins the budgeted FromBigInt
// of a magnitude below 2^128 to the general conversion under the same
// budget: the same value and the same refusal, at the admission thresholds
// of each bit length (the estimate's input digits, digits and work) and one
// below each. The inline path serves exactly the budgets the general
// preflight admits.
func TestFromBigIntBudgetedInlineMatchesGeneral(t *testing.T) {
	r := randv2.New(randv2.NewPCG(53, 54))
	const op = "FromBigIntWithBudget"
	target := bigIntIngressRuntimeTarget()
	var served, refused, zero, twoWords, beyond int
	for i := range 200000 {
		v := new(big.Int).SetUint64(r.Uint64())
		v.Lsh(v, 64).Or(v, new(big.Int).SetUint64(r.Uint64()))
		switch i % 4 {
		case 0:
			v.Rsh(v, uint(r.IntN(129)))
		case 1: // around a power of two, some beyond 2^128
			v.Lsh(big.NewInt(1), uint(r.IntN(131))).Add(v, big.NewInt(int64(r.IntN(5)-2)))
		case 2:
			v.Rsh(v, uint(64+r.IntN(64)))
		}
		if r.IntN(2) == 0 {
			v.Neg(v)
		}
		_, inline := fromBigIntInline(v)
		budgets := []Budget{{}, {MaxInputDigits: uint64(1 + r.IntN(45)), MaxDigits: uint64(1 + r.IntN(45)), MaxWork: uint64(1 + r.IntN(150))},
			{MaxWork: uint64(1 + r.IntN(150))}, {MaxDigits: uint64(1 + r.IntN(45))}, {MaxInputDigits: uint64(1 + r.IntN(45))}}
		free, admitted := len(budgets), 0
		if inline && v.Sign() != 0 {
			c, err := EstimateFromBigInt(uint64(v.BitLen()))
			if err != nil {
				t.Fatalf("EstimateFromBigInt(%d): %v", v.BitLen(), err)
			}
			budgets = append(budgets, c.Budget(), Budget{MaxWork: c.WorkUnits}, Budget{MaxDigits: c.Digits}, Budget{MaxInputDigits: c.InputDigits})
			admitted = 4
			budgets = append(budgets, Budget{MaxWork: c.WorkUnits - 1})
			if c.Digits > 1 {
				budgets = append(budgets, Budget{MaxDigits: c.Digits - 1}, Budget{MaxInputDigits: c.InputDigits - 1})
			}
		}
		switch {
		case !inline:
			beyond++
		case v.Sign() == 0:
			zero++
		case v.BitLen() > 64:
			twoWords++
		}
		for j, b := range budgets {
			got, gerr := FromBigIntWithBudget(v, b)
			want, werr := fromBigIntOnTarget(v, b, op, target)
			samePathOutcome(t, op, got, 0, gerr, want, 0, werr)
			if j >= free && (werr == nil) != (j < free+admitted) {
				t.Fatalf("FromBigInt(%s) budget %+v: general path %v at threshold index %d", v, b, werr, j-free)
			}
			if !inline || b == (Budget{}) {
				continue
			}
			if v.Sign() != 0 {
				if _, ok := bigIntIngressPreflight(uint64(v.BitLen()), b, target); ok != (werr == nil) {
					t.Fatalf("FromBigInt(%s) budget %+v: preflight admits %v, general path %v", v, b, ok, werr)
				}
			}
			if werr == nil {
				served++
			} else {
				refused++
			}
		}
	}
	if served < 100000 || refused < 100000 || zero < 100 || twoWords < 10000 || beyond < 500 {
		t.Fatalf("vacuous coverage: %d served, %d refused, %d zero, %d two-word, %d beyond 128 bits", served, refused, zero, twoWords, beyond)
	}
}

// refusedForBudget reports a resource refusal, the only error a budget adds.
func refusedForBudget(err error) bool { return errors.Is(err, ErrInsufficientStorage) }

// budgetLadder measures the smallest work and digit caps under which an
// unbudgeted-admitted general call is admitted, and returns them with the
// budgets at and one below each threshold, followed by budgets unrelated to
// the call. measured is false when the call refuses without a budget.
func budgetLadder(r *randv2.Rand, general func(limits) error) (ladder []limits, least limits, measured bool) {
	ladder = []limits{{}, {1 << 20, 1 << 40}, {uint64(1 + r.IntN(45)), uint64(1 + r.IntN(400))}, {0, uint64(1 + r.IntN(400))}, {uint64(1 + r.IntN(45)), 0}}
	if refusedForBudget(general(limits{})) {
		return ladder, limits{}, false
	}
	least.MaxWork = smallestAdmitting(1<<24, func(w uint64) bool { return !refusedForBudget(general(limits{MaxWork: w})) })
	least.MaxDigits = smallestAdmitting(1<<12, func(n uint64) bool { return !refusedForBudget(general(limits{MaxDigits: n})) })
	ladder = append(ladder, least, limits{0, least.MaxWork}, limits{least.MaxDigits, 0}, limits{least.MaxDigits, least.MaxWork - 1}, limits{0, least.MaxWork - 1})
	if least.MaxDigits > 1 {
		ladder = append(ladder, limits{least.MaxDigits - 1, least.MaxWork}, limits{least.MaxDigits - 1, 0})
	}
	return ladder, least, true
}

// TestIntDivBudgetedInlineMatchesGeneral pins budgeted Quo, Rem and RemNear
// calls on inline operands to the general kernel under the same budget: the
// same value, cohort, Conditions and error. The inline path prices a call
// exactly as the kernel does, so it serves every budget the kernel admits,
// down to the smallest admitting caps, and defers every budget the kernel
// refuses.
func TestIntDivBudgetedInlineMatchesGeneral(t *testing.T) {
	r := randv2.New(randv2.NewPCG(61, 62))
	ctxs := shortContexts()
	const name = "RemWithContext"
	var served, threshold, refused [3]int
	paths := map[intDivPath]int{}
	for i := range 60000 {
		x, y := shortOperand(r, 8), shortOperand(r, 8)
		if i%3 == 0 {
			x = New(int64(r.Uint64N(pow10Words[1+r.IntN(18)])), int32(r.IntN(9)-6))
			y = New(int64(r.Uint64N(pow10Words[1+r.IntN(10)])), int32(r.IntN(9)-6))
		}
		if i%13 == 0 && !y.isZero() {
			k := New(int64(r.Uint64N(1000)), 0)
			x, _ = y.Mul(k)
			if i%2 == 0 {
				h, _ := y.Mul(New(5, -1))
				x, _ = x.Add(h)
			}
		}
		ctx := ctxs[r.IntN(len(ctxs))]
		if i%4 == 0 {
			ctx = Context{}
		}
		op := intDivOp(r.IntN(3))
		if i%5 == 1 && x.slow == nil && y.slow == nil {
			shift := int32(r.IntN(121) - 60)
			x, y = x.withExponent(x.exponent()+shift), y.withExponent(y.exponent()+shift)
		}
		var result Decimal
		inline := false
		if x.slow == nil && y.slow == nil && !x.isZero() && !y.isZero() {
			cc := ctx
			result, _, inline = inlineIntDivide(x, y, op, &cc)
		}
		var count quoRemCount
		_, _, _ = x.intDivide(y, op, ctx, limits{}, name, &count)
		ladder, least, measured := budgetLadder(r, func(b limits) error {
			_, _, err := x.intDivide(y, op, ctx, b, name, &quoRemCount{})
			return err
		})
		for _, b := range ladder {
			got, gc, gerr := x.intDivide(y, op, ctx, b, name, nil)
			want, wc, werr := x.intDivide(y, op, ctx, b, name, &quoRemCount{})
			samePathOutcome(t, name, got, gc, gerr, want, wc, werr)
			if !inline || b == (limits{}) {
				continue
			}
			ok := b.admits(inlineResultDigits, inlineIntDivWork) || intDivInlineAdmitted(x, y, op, result, b)
			if ok == refusedForBudget(werr) {
				t.Fatalf("%v op %d %v p=%d budget %+v: the inline path serves %v, the kernel returns %v", x, op, y, ctx.precision, b, ok, werr)
			}
			if exact := intDivInlineAdmitted(x, y, op, result, b); exact == refusedForBudget(werr) {
				t.Fatalf("%v op %d %v p=%d budget %+v: the kernel's charges admit %v, the kernel returns %v", x, op, y, ctx.precision, b, exact, werr)
			}
			switch {
			case !ok:
				refused[op]++
			case measured && b == least:
				threshold[op]++
				paths[count.taken]++
				fallthrough
			default:
				served[op]++
			}
		}
	}
	for op := range served {
		if served[op] < 20000 || threshold[op] < 5000 || refused[op] < 20000 {
			t.Fatalf("vacuous coverage: served %v, at the threshold %v, refused %v", served, threshold, refused)
		}
	}
	for _, path := range []intDivPath{intDivQZero, intDivQZeroNear, intDivQuotient, intDivSplit, intDivStream} {
		if paths[path] < 300 {
			t.Fatalf("vacuous coverage of the kernel's paths at the threshold: %v", paths)
		}
	}
}

// sqrtShortOperand returns a nonnegative inline operand: random, a perfect
// square, a neighbour of one, or a short integer.
func sqrtShortOperand(r *randv2.Rand, i int) Decimal {
	x := shortOperand(r, 40).Abs()
	switch i % 6 {
	case 0:
		s := New(int64(r.Uint64N(pow10Words[1+r.IntN(17)])), int32(r.IntN(21)-10))
		x, _ = s.Mul(s)
	case 1:
		s := New(int64(r.Uint64N(pow10Words[1+r.IntN(9)])), 0)
		x, _ = s.Mul(s)
		x, _ = x.Add(New(int64(r.IntN(3)-1), 0))
		x, _ = x.Add(s)
		x = x.Abs().withExponent(int32(r.IntN(21) - 10))
	case 2:
		x = New(int64(1+r.IntN(1000)), int32(r.IntN(9)-4))
	case 3:
		// A square of up to 19 digits, whose root at decimal128 precision
		// is a two-word coefficient ending in zeros.
		s := New(int64(1+r.Uint64N(pow10Words[1+r.IntN(9)])), 0)
		x, _ = s.Mul(s)
		x = x.withExponent(int32(r.IntN(21) - 10))
	}
	return x
}

// TestSqrtBudgetedInlineMatchesGeneral pins budgeted SqrtWithContext calls
// on inline operands to the general path under the same budget. The inline
// path admits a budget at the operation's estimate, W = B + 2p + 1 and N =
// p: it must serve that budget, the general path must admit every budget
// it serves, and a budget below the bound stays with the general path,
// which still admits a shorter result.
func TestSqrtBudgetedInlineMatchesGeneral(t *testing.T) {
	r := randv2.New(randv2.NewPCG(63, 64))
	ctxs := shortContexts()
	const op = "SqrtWithContext"
	var served, atEstimate, deferred, generalBelow, exactRoots int
	for i := range 60000 {
		x := sqrtShortOperand(r, i)
		ctx := ctxs[r.IntN(len(ctxs))]
		if x.slow != nil || x.isZero() || ctx.precision == 0 || ctx.precision > sqrtInlineMaxPrecision {
			continue
		}
		cc := ctx
		_, _, _, inline := x.sqrtContextInline(&cc, op)
		ladder, _, _ := budgetLadder(r, func(b limits) error {
			_, _, err := x.sqrtContext(ctx, b, op, &sqrtCount{})
			return err
		})
		estimate, err := EstimateSqrt(x.Shape(), ctx)
		if err != nil {
			t.Fatalf("EstimateSqrt(%v) p=%d: %v", x, ctx.precision, err)
		}
		at := limits{estimate.Digits, estimate.WorkUnits}
		ladder = append(ladder, at, limits{at.MaxDigits - 1, at.MaxWork}, limits{at.MaxDigits, at.MaxWork - 1}, limits{0, at.MaxWork}, limits{at.MaxDigits, 0})
		for _, b := range ladder {
			got, gc, gerr := x.sqrtContext(ctx, b, op, nil)
			want, wc, werr := x.sqrtContext(ctx, b, op, &sqrtCount{})
			samePathOutcome(t, op, got, gc, gerr, want, wc, werr)
			if !inline || b == (limits{}) {
				continue
			}
			// The word path serves a budget that admits the precharge and
			// then the finisher at p digits.
			charge, chargeOK := sqrtCharge(inlineDigits(x.words), uint64(ctx.precision)+1)
			ok := chargeOK && sqrtFinisherAdmitted(b, charge, uint64(ctx.precision))
			switch {
			case ok && refusedForBudget(werr):
				t.Fatalf("sqrt(%v) p=%d budget %+v: the inline path serves a budget the general path refuses", x, ctx.precision, b)
			case ok:
				served++
				if b == at {
					atEstimate++
				}
				if gc&Inexact == 0 && gerr == nil {
					exactRoots++
				}
			case b.admits(at.MaxDigits, at.MaxWork):
				t.Fatalf("sqrt(%v) p=%d budget %+v: the inline path defers a budget at the estimate %+v", x, ctx.precision, b, at)
			default:
				deferred++
				if !refusedForBudget(werr) {
					generalBelow++
				}
			}
		}
	}
	if served < 50000 || atEstimate < 10000 || deferred < 50000 || generalBelow < 500 || exactRoots < 5000 {
		t.Fatalf("vacuous coverage: %d served, %d at the estimate, %d deferred, %d of them admitted by the general path, %d exact roots", served, atEstimate, deferred, generalBelow, exactRoots)
	}
}

// TestSqrtExactInlineMatchesGeneral pins the exact Sqrt of an inline
// operand, unbudgeted and budgeted, to the general exact path: the same
// root and cohort for a perfect square, the same Inexact refusal with its
// remedy for every other operand, and the same resource refusals, the
// inline path serving exactly the budgets the general path admits.
func TestSqrtExactInlineMatchesGeneral(t *testing.T) {
	r := randv2.New(randv2.NewPCG(65, 66))
	const op = "Sqrt"
	var served, threshold, refused, inexact, odd, wide int
	for i := range 120000 {
		x := sqrtShortOperand(r, i)
		if i%6 == 4 {
			// A two-word square, and one whose odd exponent scales it by ten.
			s := MustParse(strconv.FormatUint(1+r.Uint64N(1<<62), 10))
			x, _ = s.Mul(s)
			if r.IntN(2) == 0 {
				ten, _ := x.Mul(New(10, 0))
				x = ten.withExponent(int32(2*r.IntN(9) - 9))
			}
		}
		if x.slow != nil || x.isZero() {
			continue
		}
		ladder, least, measured := budgetLadder(r, func(b limits) error {
			_, _, err := x.sqrtUnlimited(b, op, &sqrtCount{})
			return err
		})
		for _, b := range ladder {
			got, gc, gerr := x.sqrtUnlimited(b, op, nil)
			want, wc, werr := x.sqrtUnlimited(b, op, &sqrtCount{})
			samePathOutcome(t, op, got, gc, gerr, want, wc, werr)
			_, exact, ok := x.sqrtExactInline(x.exponent()>>1, b)
			if ok == refusedForBudget(werr) {
				t.Fatalf("Sqrt(%v) budget %+v: the inline path serves %v, the general path returns %v", x, b, ok, werr)
			}
			if !ok {
				refused++
				continue
			}
			if exact != (werr == nil) {
				t.Fatalf("Sqrt(%v) budget %+v: the inline root is exact %v, the general path returns %v", x, b, exact, werr)
			}
			if !exact {
				var refusal *Error
				if !errors.As(werr, &refusal) || refusal.Condition != Inexact || refusal.Remedy != sqrtRemedy {
					t.Fatalf("Sqrt(%v) budget %+v: the general path's refusal is %v", x, b, werr)
				}
				inexact++
				continue
			}
			if b == (limits{}) {
				continue
			}
			served++
			if measured && b == least {
				threshold++
			}
			if x.exponent()&1 != 0 {
				odd++
			}
			if x.words.hi != 0 {
				wide++
			}
		}
	}
	if served < 50000 || threshold < 10000 || refused < 50000 || inexact < 50000 || odd < 2000 || wide < 5000 {
		t.Fatalf("vacuous coverage: %d served, %d at the threshold, %d refused, %d inexact, %d odd exponents, %d two-word squares", served, threshold, refused, inexact, odd, wide)
	}
}

// TestDivExactBudgetedInlineMatchesGeneral pins the budgeted exact division
// (DivWithContext at Context{} with a budget) of inline operands to the
// general exact path under the same budget, the inline path serving
// exactly the budgets the general path admits.
func TestDivExactBudgetedInlineMatchesGeneral(t *testing.T) {
	r := randv2.New(randv2.NewPCG(67, 68))
	const op = "DivWithContext"
	divisors := []int64{1, 2, 4, 5, 8, 16, 25, 125, 625, 1024, 3125, 10, 100, 64, 1 << 20, 1 << 40, 1 << 62, 3, 7, 15625, 1220703125, 7450580596923828125}
	var served, threshold, refused, nonterminating, long int
	for i := range 80000 {
		x := shortOperand(r, 30)
		y := New(divisors[r.IntN(len(divisors))], int32(r.IntN(41)-20)).withNegative(r.IntN(2) == 0)
		if i%7 == 0 {
			y = shortOperand(r, 30)
		}
		if i%11 == 0 {
			x = x.withExponent(math.MaxInt32 - int32(r.IntN(40)))
			y = y.withExponent(-int32(r.IntN(40)))
		}
		var exact Decimal
		inline := false
		if inlineDivOperands(x, y) {
			exact, inline = inlineDivExact(x, y)
		}
		ladder, least, measured := budgetLadder(r, func(b limits) error {
			_, _, err := x.divUnlimitedLimbs(y, b, op)
			return err
		})
		for _, b := range ladder {
			got, gc, gerr := x.divUnlimited(y, b, op)
			want, wc, werr := x.divUnlimitedLimbs(y, b, op)
			samePathOutcome(t, op, got, gc, gerr, want, wc, werr)
			if !inline {
				if werr != nil && !refusedForBudget(werr) {
					nonterminating++
				}
				continue
			}
			if b == (limits{}) {
				continue
			}
			ok := divExactInlineAdmitted(x, y, exact, b)
			if ok == refusedForBudget(werr) {
				t.Fatalf("%v / %v budget %+v: the inline gate admits %v, the general path returns %v", x, y, b, ok, werr)
			}
			switch {
			case !ok:
				refused++
			case measured && b == least:
				threshold++
				fallthrough
			default:
				served++
				if got.exponent() < x.exponent()-y.exponent()-15 {
					long++
				}
			}
		}
	}
	if served < 50000 || threshold < 10000 || refused < 50000 || nonterminating < 5000 || long < 2000 {
		t.Fatalf("vacuous coverage: %d served, %d at the threshold, %d refused, %d nonterminating, %d long quotients", served, threshold, refused, nonterminating, long)
	}
}

// TestInlineStripWideMatchesBigInt checks the two-word zero strip against
// math/big over every count of trailing zeros and every limit.
func TestInlineStripWideMatchesBigInt(t *testing.T) {
	r := randv2.New(randv2.NewPCG(69, 70))
	ten := big.NewInt(10)
	counts := map[int64]int{}
	for range 200000 {
		zeros := r.IntN(39)
		v := new(big.Int).SetUint64(r.Uint64())
		if r.IntN(2) == 0 {
			v.Lsh(v, 64).Or(v, new(big.Int).SetUint64(r.Uint64()))
		}
		v.Rsh(v, uint(r.IntN(100)))
		v.Mul(v, new(big.Int).Exp(ten, big.NewInt(int64(zeros)), nil))
		if v.BitLen() <= 64 || v.BitLen() > 127 {
			continue
		}
		var q uint128
		q.lo = new(big.Int).And(v, new(big.Int).SetUint64(math.MaxUint64)).Uint64()
		q.hi = new(big.Int).Rsh(v, 64).Uint64()
		limit := int64(r.IntN(45))
		got, m := inlineStripWide(q, limit)
		want, n := new(big.Int).Set(v), int64(0)
		for rem := new(big.Int); n < limit && n < 19; n++ {
			quo, _ := new(big.Int).QuoRem(want, ten, rem)
			if rem.Sign() != 0 {
				break
			}
			want = quo
		}
		back := new(big.Int).Lsh(new(big.Int).SetUint64(got.hi), 64)
		back.Or(back, new(big.Int).SetUint64(got.lo))
		if m != n || back.Cmp(want) != 0 {
			t.Fatalf("inlineStripWide(%s, %d) = %s, %d; want %s, %d", v, limit, back, m, want, n)
		}
		counts[m]++
	}
	for m := int64(0); m <= 19; m++ {
		if counts[m] < 50 {
			t.Fatalf("vacuous coverage of %d stripped zeros: %v", m, counts)
		}
	}
}

// TestFinishContextInlineStripsTwoWords checks that the word finisher
// publishes an exact two-word coefficient with zeros to strip as the limb
// finisher does, at the exponent nearest the ideal.
func TestFinishContextInlineStripsTwoWords(t *testing.T) {
	r := randv2.New(randv2.NewPCG(71, 72))
	ctxs := shortContexts()
	var taken, wideResult, wordResult int
	for range 400000 {
		ctx := ctxs[r.IntN(len(ctxs))]
		if ctx.precision == 0 || ctx.precision > 38 {
			continue
		}
		zeros := r.IntN(int(ctx.precision))
		head := MustParse(strconv.FormatUint(1+r.Uint64N(pow10Words[1+r.IntN(19)]), 10))
		x, err := head.Mul(New(1, int32(zeros)))
		if err != nil {
			t.Fatal(err)
		}
		x, _, err = x.Quantize(0, Exact)
		if err != nil || x.slow != nil || x.words.hi == 0 || x.words.hi>>63 != 0 {
			continue
		}
		tPrime := int64(r.IntN(121) - 60)
		ideal := tPrime + int64(r.IntN(45)-4)
		// The finisher's exponent before the strip, when it drops nothing.
		before := tPrime + int64(inlineDigits(x.words)) - int64(ctx.precision)
		var etiny int64
		if ctx.guarded {
			etiny = int64(ctx.guards.Emin) - (int64(ctx.precision) - 1)
			before = max(before, etiny)
		}
		negative := r.IntN(2) == 0
		g, gc, gerr, ok := finishContextInline(x.words, divExactClass, tPrime, etiny, ideal, negative, &ctx, "DivWithContext")
		if !ok {
			continue
		}
		var buf [6]uint32
		n := 0
		for q := x.words; q != (uint128{}); n++ {
			var rem, digit uint64
			q.hi, rem = bits.Div64(0, q.hi, decimalLimbBase)
			q.lo, digit = bits.Div64(rem, q.lo, decimalLimbBase)
			buf[n] = uint32(digit)
		}
		w, wc, werr := finishContext(buf[:n], divExactClass, tPrime, etiny, ideal, negative, &ctx, 0, limits{}, "DivWithContext")
		if werr != nil && werr.Error() == "decimal: DivWithContext: insufficient storage" {
			continue // an unreachable state (t′ above t), which the kernel never produces
		}
		samePathOutcome(t, "finish", g, gc, gerr, w, wc, werr)
		if gerr == nil && before <= tPrime && g.exponent() > int32(tPrime) {
			taken++
			if g.words.hi != 0 {
				wideResult++
			} else {
				wordResult++
			}
		}
	}
	if taken < 20000 || wideResult < 2000 || wordResult < 2000 {
		t.Fatalf("vacuous coverage: %d strips, %d two-word results, %d one-word results", taken, wideResult, wordResult)
	}
}

// sameConversion compares two integer or rational conversions: the same
// error identity, or equal values.
func sameConversion(t *testing.T, what string, equal bool, gerr, werr error) {
	t.Helper()
	if (gerr == nil) != (werr == nil) || gerr != nil && gerr.Error() != werr.Error() {
		t.Fatalf("%s: error %v vs %v", what, gerr, werr)
	}
	if gerr == nil && !equal {
		t.Fatalf("%s: values differ", what)
	}
}

// conversionLadder measures the smallest input-digit, digit and work caps
// under which an integer conversion that succeeds unbudgeted is admitted,
// and returns the budgets at and one below each, after budgets unrelated
// to the call and the given bound.
func conversionLadder(r *randv2.Rand, bound Budget, general func(Budget) error) (ladder []Budget, least Budget, measured bool) {
	ladder = []Budget{{}, bound, {MaxInputDigits: uint64(1 + r.IntN(45)), MaxDigits: uint64(1 + r.IntN(45)), MaxWork: uint64(1 + r.IntN(150))},
		{MaxWork: uint64(1 + r.IntN(150))}, {MaxDigits: uint64(1 + r.IntN(45))}, {MaxInputDigits: uint64(1 + r.IntN(45))}}
	if general(Budget{}) != nil {
		return ladder, Budget{}, false
	}
	least.MaxWork = smallestAdmitting(1<<20, func(w uint64) bool { return general(Budget{MaxWork: w}) == nil })
	least.MaxDigits = smallestAdmitting(1<<10, func(n uint64) bool { return general(Budget{MaxDigits: n}) == nil })
	least.MaxInputDigits = smallestAdmitting(1<<10, func(n uint64) bool { return general(Budget{MaxInputDigits: n}) == nil })
	ladder = append(ladder, least, Budget{MaxWork: least.MaxWork}, Budget{MaxDigits: least.MaxDigits}, Budget{MaxInputDigits: least.MaxInputDigits})
	if least.MaxWork > 1 {
		ladder = append(ladder, Budget{MaxWork: least.MaxWork - 1})
	}
	if least.MaxDigits > 1 {
		ladder = append(ladder, Budget{MaxDigits: least.MaxDigits - 1})
	}
	if least.MaxInputDigits > 1 {
		ladder = append(ladder, Budget{MaxInputDigits: least.MaxInputDigits - 1})
	}
	return ladder, least, true
}

// TestBigIntBudgetedInlineMatchesGeneral pins the budgeted BigInt of an
// inline coefficient to the general conversion under the same budget: the
// same integer and the same refusal. The inline path serves exactly the
// budgets the general conversion admits, down to its smallest admitting
// caps on each axis.
func TestBigIntBudgetedInlineMatchesGeneral(t *testing.T) {
	r := randv2.New(randv2.NewPCG(73, 74))
	const op = "BigIntWithBudget"
	bound := Budget{MaxInputDigits: inlineResultDigits, MaxDigits: inlineResultDigits, MaxWork: inlineBigIntWork}
	var served, threshold, atBound, refused, other, scaled, divided int
	for i := range 80000 {
		x := shortOperand(r, 20)
		if i%3 == 0 {
			// An integral value written with fraction digits.
			k := int32(r.IntN(20))
			if scaledUp, ok := inlineScale(x.words, uint64(k)); ok {
				x = inlineDecimal(scaledUp, -k, x.negative())
			}
		}
		if x.isZero() || x.slow != nil {
			continue
		}
		_, inline := x.bigIntInline(nil)
		ladder, least, measured := conversionLadder(r, bound, func(b Budget) error {
			_, err := x.bigIntGeneral(nil, b, op)
			return err
		})
		for _, b := range ladder {
			got, gerr := x.bigIntWithBudget(nil, b, op)
			want, werr := x.bigIntGeneral(nil, b, op)
			sameConversion(t, op, gerr != nil || got.Cmp(want) == 0, gerr, werr)
			if !inline {
				other++
				continue
			}
			if b == (Budget{}) {
				continue
			}
			ok := x.bigIntInlineAdmitted(b)
			if ok != (werr == nil) {
				t.Fatalf("BigInt(%v) budget %+v: the inline path serves %v, the general path returns %v", x, b, ok, werr)
			}
			switch {
			case !ok:
				refused++
			case measured && b == least:
				threshold++
				fallthrough
			default:
				served++
				if b == bound {
					atBound++
				}
				if x.exponent() > 0 {
					scaled++
				} else if x.exponent() < 0 {
					divided++
				}
			}
		}
	}
	if served < 50000 || threshold < 10000 || atBound < 10000 || refused < 50000 || other < 20000 || scaled < 5000 || divided < 5000 {
		t.Fatalf("vacuous coverage: %d served, %d at the threshold, %d at the bound, %d refused, %d on the general path, %d scaled, %d divided",
			served, threshold, atBound, refused, other, scaled, divided)
	}
}

// TestBinaryBudgetedInlineMatchesGeneral pins the budgeted conversion of a
// binary coefficient of at most 16 bytes to the general conversion under
// the same budget, for both byte orders, two's complement and magnitudes,
// and every amount of sign padding. The inline path serves exactly the
// budgets whose envelope the general conversion admits.
func TestBinaryBudgetedInlineMatchesGeneral(t *testing.T) {
	r := randv2.New(randv2.NewPCG(75, 76))
	const op = "NewTwosComplementWithBudget"
	bound := Budget{MaxInputDigits: inlineBinaryDigits, MaxDigits: inlineBinaryDigits, MaxWork: inlineBinaryWork}
	var served, threshold, atBound, refused, longer, padded, negative, composes int
	for range 150000 {
		n := 1 + r.IntN(18)
		raw := make([]byte, n)
		for i := range raw {
			raw[i] = byte(r.IntN(256))
		}
		little, signed, flag := r.IntN(2) == 0, r.IntN(3) != 0, r.IntN(2) == 0
		if pad := r.IntN(n + 1); r.IntN(2) == 0 {
			// Sign padding at the most significant end.
			fill := byte(0)
			if r.IntN(2) == 0 {
				fill = 0xff
			}
			for i := range pad {
				if little {
					raw[n-1-i] = fill
				} else {
					raw[i] = fill
				}
			}
			padded++
		}
		exponent := int32(r.IntN(41) - 20)
		ladder, least, measured := conversionLadder(r, bound, func(b Budget) error {
			_, err := fromBinaryGeneral(raw, little, signed, flag, exponent, b, op)
			return err
		})
		for _, b := range ladder {
			got, gerr := fromBinary(raw, little, signed, flag, exponent, b, op)
			want, werr := fromBinaryGeneral(raw, little, signed, flag, exponent, b, op)
			samePathOutcome(t, op, got, 0, gerr, want, 0, werr)
			if !little && !signed {
				// ComposeWithBudget is the big-endian magnitude conversion.
				var composed Decimal
				cerr := composed.ComposeWithBudget(0, flag, raw, exponent, b)
				cwant, cwerr := fromBinaryGeneral(raw, false, false, flag, exponent, b, "ComposeWithBudget")
				samePathOutcome(t, "ComposeWithBudget", composed, 0, cerr, cwant, 0, cwerr)
				composes++
			}
			if n > 16 {
				longer++
				continue
			}
			if b == (Budget{}) {
				continue
			}
			ok := binaryInlineAdmitted(n, b)
			if ok != (werr == nil) {
				t.Fatalf("%d bytes budget %+v: the inline gate admits %v, the general path returns %v", n, b, ok, werr)
			}
			switch {
			case !ok:
				refused++
			case measured && b == least:
				threshold++
				fallthrough
			default:
				served++
				if b == bound {
					atBound++
				}
				if got.negative() {
					negative++
				}
			}
		}
	}
	if served < 100000 || threshold < 20000 || atBound < 20000 || refused < 100000 || longer < 20000 || padded < 20000 || negative < 20000 || composes < 100000 {
		t.Fatalf("vacuous coverage: %d served, %d at the threshold, %d at the bound, %d refused, %d longer, %d padded, %d negative, %d composed",
			served, threshold, atBound, refused, longer, padded, negative, composes)
	}
}

// TestRatBudgetedInlineMatchesGeneral pins the budgeted Rat of a one-word
// coefficient with fraction digits to the general conversion under the
// same budget: the same reduced fraction and the same refusal, the inline
// path serving exactly the budgets the general conversion admits.
func TestRatBudgetedInlineMatchesGeneral(t *testing.T) {
	r := randv2.New(randv2.NewPCG(77, 78))
	const op = "RatWithBudget"
	bound := Budget{MaxInputDigits: inlineRatEgressDigits, MaxDigits: inlineRatEgressDigits, MaxWork: inlineRatEgressWork}
	var served, threshold, atBound, refused, other, stripped, reduced int
	for i := range 60000 {
		x := New(int64(r.Uint64N(pow10Words[1+r.IntN(18)])), -int32(r.IntN(22)))
		switch i % 4 {
		case 0:
			x = shortOperand(r, 22)
		case 1: // trailing zeros and shared factors of two and five
			c := (1 + r.Uint64N(1<<20)) << uint(r.IntN(20))
			for range r.IntN(8) {
				if c < math.MaxUint64/5 {
					c *= 5
				}
			}
			x = inlineDecimal(uint128{lo: c}, -int32(1+r.IntN(19)), r.IntN(2) == 0)
		case 2:
			x = inlineDecimal(uint128{lo: r.Uint64() | 1<<63}, -int32(1+r.IntN(19)), r.IntN(2) == 0)
		}
		if x.isZero() {
			continue
		}
		_, inline := x.ratInline(nil)
		ladder, least, measured := conversionLadder(r, bound, func(b Budget) error {
			_, err := x.ratGeneral(nil, b, op)
			return err
		})
		for _, b := range ladder {
			got, gerr := x.ratWithBudget(nil, b, op)
			want, werr := x.ratGeneral(nil, b, op)
			sameConversion(t, op, gerr != nil || got.Cmp(want) == 0 && got.Num().Cmp(want.Num()) == 0 && got.Denom().Cmp(want.Denom()) == 0, gerr, werr)
			if !inline {
				other++
				continue
			}
			if b == (Budget{}) {
				continue
			}
			ok := x.ratInlineAdmitted(b)
			if ok != (werr == nil) {
				t.Fatalf("Rat(%v) budget %+v: the inline path serves %v, the general path returns %v", x, b, ok, werr)
			}
			switch {
			case !ok:
				refused++
			case measured && b == least:
				threshold++
				fallthrough
			default:
				served++
				if b == bound {
					atBound++
				}
				if x.words.lo%10 == 0 {
					stripped++
				}
				if got.Denom().BitLen() < 3*int(-x.exponent()) {
					reduced++
				}
			}
		}
	}
	if served < 50000 || threshold < 10000 || atBound < 10000 || refused < 50000 || other < 20000 || stripped < 5000 || reduced < 5000 {
		t.Fatalf("vacuous coverage: %d served, %d at the threshold, %d at the bound, %d refused, %d on the general path, %d stripped, %d reduced",
			served, threshold, atBound, refused, other, stripped, reduced)
	}
}

// shortRat returns a rational whose numerator and denominator usually fit
// one 64-bit word: random bit lengths, terminating denominators, integers
// and exact multiples, with a share of two-word numerators.
func shortRat(r *randv2.Rand, i int) *big.Rat {
	n := new(big.Int).SetUint64(r.Uint64() >> uint(r.IntN(64)))
	d := new(big.Int).SetUint64(1 + r.Uint64()>>uint(r.IntN(64)))
	switch i % 6 {
	case 0: // a terminating denominator 2^a·5^b
		d.SetUint64(1 << uint(r.IntN(30)))
		for range r.IntN(12) {
			d.Mul(d, big.NewInt(5))
		}
	case 1:
		d.SetUint64(1)
	case 2:
		n.Mul(d, big.NewInt(int64(r.IntN(1000))))
	case 3:
		n.Lsh(n, uint(r.IntN(40)))
	}
	if r.IntN(2) == 0 {
		n.Neg(n)
	}
	return new(big.Rat).SetFrac(n, d)
}

// TestFromRatToExponentBudgetedInlineMatchesGeneral pins the budgeted
// FromRatToExponent of a one-word numerator over a one-word denominator to
// the general path under the same budget, the inline path serving exactly
// the budgets the general path admits.
func TestFromRatToExponentBudgetedInlineMatchesGeneral(t *testing.T) {
	r := randv2.New(randv2.NewPCG(79, 80))
	const op = "FromRatToExponentWithBudget"
	bound := limits{inlineResultDigits, inlineRatWork}
	var served, threshold, atBound, refused, other, tiny, scaledDown int
	for i := range 60000 {
		q := shortRat(r, i)
		target := int32(r.IntN(66) - 40)
		mode := RoundingMode(r.IntN(int(Exact) + 1))
		n, d, shape := ratInlineOperands(q)
		var result Decimal
		inline := false
		if shape {
			var refusal, ok bool
			result, _, refusal, ok = inlineDivToExponent(n, d, target, mode)
			inline = ok && !refusal
		}
		ladder, least, measured := budgetLadder(r, func(b limits) error {
			_, _, err := fromRatToExponent(q, target, mode, b, op)
			return err
		})
		for _, b := range append(ladder, bound) {
			got, gc, gerr := FromRatToExponentWithBudget(q, target, mode, Budget{MaxDigits: b.MaxDigits, MaxWork: b.MaxWork})
			want, wc, werr := fromRatToExponent(q, target, mode, b, op)
			samePathOutcome(t, op, got, gc, gerr, want, wc, werr)
			if !inline {
				other++
				continue
			}
			if b == (limits{}) {
				continue
			}
			ok := b.admits(inlineResultDigits, inlineRatWork) || ratToExponentInlineAdmitted(n.words.lo, d.words.lo, target, result, b)
			if ok == refusedForBudget(werr) {
				t.Fatalf("%v -> %d budget %+v: the inline gate admits %v, the general path returns %v", q, target, b, ok, werr)
			}
			switch {
			case !ok:
				refused++
			case measured && b == least:
				threshold++
				fallthrough
			default:
				served++
				if b == bound {
					atBound++
				}
				if result.isZero() {
					tiny++
				}
				if target > 0 {
					scaledDown++
				}
			}
		}
	}
	if served < 50000 || threshold < 10000 || atBound < 10000 || refused < 50000 || other < 20000 || tiny < 2000 || scaledDown < 5000 {
		t.Fatalf("vacuous coverage: %d served, %d at the threshold, %d at the bound, %d refused, %d on the general path, %d zero results, %d scaled down",
			served, threshold, atBound, refused, other, tiny, scaledDown)
	}
}

// narrowContexts returns shortContexts and guarded contexts whose exponent
// range is a few decades wide, in which ordinary magnitudes are subnormal
// or overflow.
func narrowContexts() []Context {
	out := shortContexts()
	for _, p := range []uint32{3, 7, 16, 34} {
		for m := TiesToEven; m <= Exact; m++ {
			c, err := NewContext(p, m, &ExponentGuards{Emin: -4, Emax: 6}, 0)
			if err != nil {
				panic(err)
			}
			out = append(out, c)
		}
	}
	return out
}

// TestFromRatContextInlineMatchesGeneral pins FromRatWithContext of a
// one-word numerator over a one-word denominator to the general path,
// unbudgeted and budgeted: the same value, cohort, Conditions and error.
// The inline path admits a budget at the operation's estimate; the general
// path must admit every budget it serves, and a budget below the bound
// stays with the general path. At precision 0 the exact inline quotient
// equals the exact general conversion.
func TestFromRatContextInlineMatchesGeneral(t *testing.T) {
	r := randv2.New(randv2.NewPCG(81, 82))
	ctxs := narrowContexts()
	const op = "FromRatWithContext"
	var unbudgeted, exact, served, atEstimate, deferred, generalBelow, other, bare, bareServed, bareThreshold, bareRefused int
	for i := range 60000 {
		q := shortRat(r, i)
		ctx := ctxs[r.IntN(len(ctxs))]
		if i%9 == 0 {
			ctx = Context{}
		}
		n, d, shape := ratInlineOperands(q)
		if ctx.precision == 0 {
			// The exact quotient is served under exactly the budgets the
			// exact general conversion admits.
			var quotient Decimal
			terminates := false
			if shape {
				quotient, terminates = inlineDivExact(n, d)
			}
			ladder, least, measured := budgetLadder(r, func(b limits) error {
				_, _, err := fromRatExact(q, b, op)
				return err
			})
			for _, b := range ladder {
				got, gc, gerr := fromRatContext(q, ctx, b, op)
				want, wc, werr := fromRatExact(q, b, op)
				samePathOutcome(t, op, got, gc, gerr, want, wc, werr)
				if !terminates {
					continue
				}
				if b == (limits{}) {
					bare++
					continue
				}
				ok := ratExactInlineAdmitted(n.words.lo, d.words.lo, quotient, b)
				if ok == refusedForBudget(werr) {
					t.Fatalf("%v budget %+v: the exact inline path serves %v, the general path returns %v", q, b, ok, werr)
				}
				if ok {
					bareServed++
					if measured && b == least {
						bareThreshold++
					}
				} else {
					bareRefused++
				}
			}
			continue
		}
		inline := false
		if shape && ctx.precision <= inlineDivMaxPrecision {
			cc := ctx
			_, _, _, inline = inlineDivContext(n, d, &cc, op)
		}
		ladder, _, _ := budgetLadder(r, func(b limits) error {
			_, _, err := fromRatContextGeneral(q, ctx, b, op)
			return err
		})
		at := limits{}
		if q.Sign() != 0 {
			estimate, err := EstimateFromRat(uint64(q.Num().BitLen()), uint64(q.Denom().BitLen()), ctx)
			if err != nil {
				t.Fatalf("EstimateFromRat(%v) p=%d: %v", q, ctx.precision, err)
			}
			at = limits{estimate.Digits, estimate.WorkUnits}
			ladder = append(ladder, at, limits{at.MaxDigits - 1, at.MaxWork}, limits{at.MaxDigits, at.MaxWork - 1}, limits{0, at.MaxWork}, limits{at.MaxDigits, 0})
		}
		for _, b := range ladder {
			got, gc, gerr := fromRatContext(q, ctx, b, op)
			want, wc, werr := fromRatContextGeneral(q, ctx, b, op)
			samePathOutcome(t, op, got, gc, gerr, want, wc, werr)
			if !inline {
				other++
				continue
			}
			if b == (limits{}) {
				unbudgeted++
				if gc&Inexact == 0 && gerr == nil {
					exact++
				}
				continue
			}
			cc := ctx
			ok := ratContextInlineAdmitted(n.words.lo, d.words.lo, &cc, b)
			switch {
			case ok && refusedForBudget(werr):
				t.Fatalf("%v p=%d budget %+v: the inline path serves a budget the general path refuses", q, ctx.precision, b)
			case ok:
				served++
				if b == at {
					atEstimate++
				}
			case b.admits(at.MaxDigits, at.MaxWork):
				t.Fatalf("%v p=%d budget %+v: the inline path defers a budget at the estimate %+v", q, ctx.precision, b, at)
			default:
				deferred++
				if !refusedForBudget(werr) {
					generalBelow++
				}
			}
		}
	}
	if unbudgeted < 20000 || exact < 3000 || served < 50000 || atEstimate < 10000 || deferred < 50000 || generalBelow < 500 || other < 20000 || bare < 500 || bareServed < 5000 || bareThreshold < 500 || bareRefused < 5000 {
		t.Fatalf("vacuous coverage: %d unbudgeted, %d exact, %d served, %d at the estimate, %d deferred, %d of them admitted by the general path, %d on the general path, %d bare (%d served, %d at the threshold, %d refused)",
			unbudgeted, exact, served, atEstimate, deferred, generalBelow, other, bare, bareServed, bareThreshold, bareRefused)
	}
}

// TestFromFloat64ContextInlineMatchesGeneral pins FromFloat64WithContext of
// a fraction with a one-word denominator to the exact expansion path,
// unbudgeted and budgeted: the same value, cohort, Conditions and error.
// A result without an error is served under exactly the budgets the
// general path admits; a trapped result is left to the general path
// whenever a budget is set.
func TestFromFloat64ContextInlineMatchesGeneral(t *testing.T) {
	r := randv2.New(randv2.NewPCG(83, 84))
	ctxs := narrowContexts()
	const op = "FromFloat64WithContext"
	var unbudgeted, fits, served, threshold, refused, trapped, other int
	// The word division serves a one-word power-of-two denominator at the
	// precisions its kernel rounds to, and nothing else.
	for e := int64(-70); e <= 5; e++ {
		for _, p := range []uint32{0, 1, 16, 38, 39, 60} {
			if got, want := float64ContextInlineShape(e, p), e >= -63 && e <= -1 && p >= 1 && p <= 38; got != want {
				t.Fatalf("float64ContextInlineShape(%d, %d) = %v, want %v", e, p, got, want)
			}
		}
	}
	for range 100000 {
		var f float64
		switch r.IntN(6) {
		case 0:
			f = math.Float64frombits(r.Uint64())
		case 1:
			f = float64(r.Int64N(1e12)) / 100
		case 2:
			f = math.Ldexp(float64(r.Int64N(1<<53)), r.IntN(80)-70) // exact values and ties
		case 3:
			f = r.NormFloat64() * math.Pow(10, float64(r.IntN(24)-8))
		case 4:
			f = math.Ldexp(float64(1+r.IntN(1<<16)), -r.IntN(40)) // short fractions that fit the precision
		default:
			f = math.Ldexp(1+r.Float64(), -r.IntN(70))
		}
		if r.IntN(2) == 0 {
			f = -f
		}
		ctx := ctxs[r.IntN(len(ctxs))]
		negative, m, e := binary64Parts(f)
		shape := !float64Nonfinite(f) && m != 0 && float64ContextInlineShape(e, ctx.precision)
		var inlineEvents Conditions
		var inlineErr error
		inline := false
		if shape {
			cc := ctx
			_, inlineEvents, inlineErr, inline = float64ContextInline(negative, m, e, &cc, limits{}, op)
		}
		ladder, least, measured := budgetLadder(r, func(b limits) error {
			_, _, err := fromFloat64Context(f, ctx, b, op, true)
			return err
		})
		for _, b := range ladder {
			got, gc, gerr := FromFloat64WithContext(f, ctx.withLimits(b))
			want, wc, werr := fromFloat64Context(f, ctx, b, op, true)
			samePathOutcome(t, op, got, gc, gerr, want, wc, werr)
			if !inline {
				other++
				continue
			}
			if b == (limits{}) {
				unbudgeted++
				if inlineEvents == 0 && inlineErr == nil {
					fits++
				}
				continue
			}
			cc := ctx
			_, _, _, ok := float64ContextInline(negative, m, e, &cc, b, op)
			if inlineErr != nil {
				if ok {
					t.Fatalf("%v p=%d budget %+v: the inline path serves a trapped result under a budget", f, ctx.precision, b)
				}
				trapped++
				continue
			}
			if ok == refusedForBudget(werr) {
				t.Fatalf("%v p=%d budget %+v: the inline path serves %v, the general path returns %v", f, ctx.precision, b, ok, werr)
			}
			switch {
			case !ok:
				refused++
			case measured && b == least:
				threshold++
				fallthrough
			default:
				served++
			}
		}
	}
	if unbudgeted < 20000 || fits < 2000 || served < 50000 || threshold < 10000 || refused < 50000 || trapped < 500 || other < 50000 {
		t.Fatalf("vacuous coverage: %d unbudgeted, %d fitting the precision, %d served, %d at the threshold, %d refused, %d trapped, %d on the general path",
			unbudgeted, fits, served, threshold, refused, trapped, other)
	}
}

// TestRoundToPrecisionInlineMatchesGeneral pins RoundToPrecision of an
// inline value to the context addition of a zero at the value's exponent,
// which defines it, on the general path and under the same budget: the
// exact inline sum of that addition is the value itself, returned when it
// fits and rounded once otherwise.
func TestRoundToPrecisionInlineMatchesGeneral(t *testing.T) {
	r := randv2.New(randv2.NewPCG(85, 86))
	ctxs := shortContexts()
	const op = "RoundToPrecisionWithContext"
	budgets := []limits{{}, {inlineResultDigits, inlineContextAddSubWork}, {inlineResultDigits, inlineContextAddSubWork - 1}, {inlineResultDigits - 1, inlineContextAddSubWork},
		{1 << 20, 1 << 40}, {16, 100}, {20, 60}, {0, 40}, {7, 0}}
	var fits, rounded, deferred, budgeted, identity int
	for i := range 400000 {
		x := shortOperand(r, 45)
		if i%7 == 0 {
			x = x.withExponent(math.MaxInt32 - int32(r.IntN(40)))
		}
		ctx := ctxs[r.IntN(len(ctxs))]
		b := budgets[r.IntN(len(budgets))]
		zero := zeroDecimal(x.exponent())
		if sum, ok := inlineAddSub(x, zero, false); !ok || !sameRepresentation(sum, x) {
			t.Fatalf("%v + 0 is %v (%v) on the inline path", x, sum, ok)
		}
		if i%13 == 0 {
			// Precision 0 is the identity, the exact sum.
			got, gc, gerr := x.roundToPrecision(Context{rounding: ctx.rounding, arith: b}, op)
			want, werr := x.addSubLimbs(zero, b, op, false)
			samePathOutcome(t, op, got, gc, gerr, want, 0, werr)
			identity++
			continue
		}
		bc := ctx.withLimits(b)
		got, gc, gerr := x.roundToPrecision(bc, op)
		want, wc, werr := x.contextAddSubGeneral(zero, bc, op, false, true, nil)
		samePathOutcome(t, op, got, gc, gerr, want, wc, werr)
		if !b.admits(inlineResultDigits, inlineContextAddSubWork) {
			continue
		}
		if b != (limits{}) {
			budgeted++
		}
		if contextExactFits(x, ctx) {
			fits++
		} else if _, _, ok := contextRoundInline(x, ctx); ok {
			rounded++
		} else {
			deferred++
		}
	}
	if fits < 30000 || rounded < 30000 || deferred < 3000 || budgeted < 30000 || identity < 20000 {
		t.Fatalf("vacuous coverage: %d returned as they are, %d rounded, %d deferred, %d under an admitted budget, %d at precision 0", fits, rounded, deferred, budgeted, identity)
	}
}

// wideToBig returns the value of a 256-bit intermediate.
func wideToBig(w wide256) *big.Int {
	v := new(big.Int)
	for i := len(w) - 1; i >= 0; i-- {
		v.Lsh(v, 64).Or(v, new(big.Int).SetUint64(w[i]))
	}
	return v
}

// TestWideMulWordsMatchesBigInt checks the 256-by-128-bit product and its
// overflow report against math/big, around the 2^256 boundary.
func TestWideMulWordsMatchesBigInt(t *testing.T) {
	r := randv2.New(randv2.NewPCG(87, 88))
	limit := new(big.Int).Lsh(big.NewInt(1), 256)
	check := func(z wide256, m uint128) (ok bool, bitLength int) {
		want := new(big.Int).Mul(wideToBig(z), wideToBig(wide256{m.lo, m.hi}))
		got := z
		ok = got.mulWords(m)
		if ok != (want.Cmp(limit) < 0) || ok && wideToBig(got).Cmp(want) != 0 {
			t.Fatalf("%v * %v: ok %v, product %s, want %s", z, m, ok, wideToBig(got), want)
		}
		return ok, want.BitLen()
	}
	var fit, overflow, edge int
	for i := range 300000 {
		var z wide256
		for j := range z {
			z[j] = r.Uint64()
		}
		zBits := r.IntN(257)
		for j := range z {
			switch keep := zBits - 64*j; {
			case keep <= 0:
				z[j] = 0
			case keep < 64:
				z[j] >>= uint(64 - keep)
			}
		}
		m := uint128{r.Uint64(), r.Uint64()}
		switch mBits := r.IntN(129); {
		case i%3 == 0 && zBits < 256:
			// A product within a few bits of 2^256.
			mBits = min(128, 256-zBits+r.IntN(3)-1)
			fallthrough
		default:
			switch {
			case mBits <= 0:
				m = uint128{}
			case mBits <= 64:
				m = uint128{lo: m.lo >> uint(64-mBits)}
			default:
				m.hi >>= uint(128 - mBits)
			}
		}
		ok, bitLength := check(z, m)
		if ok {
			fit++
			if bitLength > 250 {
				edge++
			}
		} else {
			overflow++
			if bitLength < 260 {
				edge++
			}
		}
	}
	if fit < 50000 || overflow < 50000 || edge < 10000 {
		t.Fatalf("vacuous coverage: %d products, %d overflows, %d near 2^256", fit, overflow, edge)
	}
	// Overflows that exactly one signal reports: the carry out of the low
	// product, the carry out of the high product, the top word of the high
	// product, and the carry of their sum.
	for _, c := range []struct {
		z wide256
		m uint128
	}{
		{wide256{0, 0, 0, 1 << 63}, uint128{lo: 2}},
		{wide256{0, 0, 0, 1 << 63}, uint128{hi: 2}},
		{wide256{0, 0, 0, 1}, uint128{hi: 1}},
		{wide256{0, 0, math.MaxUint64, 0}, uint128{lo: math.MaxUint64, hi: 1}},
	} {
		if ok, _ := check(c.z, c.m); ok {
			t.Fatalf("%v * %v reported below 2^256", c.z, c.m)
		}
	}
}

// TestPowWideOddMatchesGeneral pins the odd powers whose last partial
// square leaves two words but whose exact value fits 256 bits to the
// general PowWithContext path, and their coefficients to math/big.
func TestPowWideOddMatchesGeneral(t *testing.T) {
	r := randv2.New(randv2.NewPCG(89, 90))
	ctxs := shortContexts()
	const op = "PowWithContext"
	served := map[int32]int{}
	var declined, total int
	for i := range 200000 {
		n := int32(3 + 2*r.IntN(8))
		if i%20 == 0 {
			n = int32(17 + 2*r.IntN(30))
		}
		// Coefficients whose n-th power has about 77 digits, the most that
		// fits 256 bits.
		text := make([]byte, max(1, 78/int(n)-r.IntN(3)+1))
		for j := range text {
			text[j] = byte('0' + r.IntN(10))
		}
		text[0] = byte('1' + r.IntN(9))
		x := MustParse(string(text)).withExponent(int32(r.IntN(13) - 6)).withNegative(r.IntN(2) == 0)
		if x.slow != nil || x.isZero() {
			continue
		}
		ctx := ctxs[r.IntN(len(ctxs))]
		if ctx.precision == 0 {
			continue
		}
		if _, _, ok := powWideOdd(x, n-1); ok {
			t.Fatalf("powWideOdd(%v, %d) serves an even exponent", x, n-1)
		}
		if _, _, factors := powInlineFactors(x, n); !factors {
			power, exponent, ok := powWideOdd(x, n)
			want := new(big.Int).Exp(wideToBig(wide256{x.words.lo, x.words.hi}), big.NewInt(int64(n)), nil)
			if ok != (want.BitLen() <= 256) {
				t.Fatalf("powWideOdd(%v, %d) ok %v for a power of %d bits", x, n, ok, want.BitLen())
			}
			if ok {
				if wideToBig(power).Cmp(want) != 0 || exponent != int64(n)*int64(x.exponent()) {
					t.Fatalf("powWideOdd(%v, %d) = %s e%d, want %s", x, n, wideToBig(power), exponent, want)
				}
				if _, _, rounded := contextRoundWide(power, exponent, x.negative(), ctx); rounded {
					served[n]++
					total++
				}
			} else {
				declined++
			}
		}
		g, gc, gerr := x.powContext(n, ctx, limits{}, op, nil)
		w, wc, werr := x.powContext(n, ctx, limits{}, op, &powCount{})
		samePathOutcome(t, op, g, gc, gerr, w, wc, werr)
	}
	if total < 20000 || declined < 5000 || served[3] < 1000 || served[5] < 1000 || served[7] < 1000 || served[9] < 500 {
		t.Fatalf("vacuous coverage: %d served, by exponent %v, %d declined", total, served, declined)
	}
}

// TestInlineConversionBoundsAtExtremes measures the general conversions'
// smallest admitting caps on the dearest shape each constant conversion
// gate serves: the BigInt, binary, Rat and FromRatToExponent bounds are
// attained, and so are the exact Div and integer-division bounds.
func TestInlineConversionBoundsAtExtremes(t *testing.T) {
	leastWork := func(call func(Budget) error) uint64 {
		return smallestAdmitting(1<<20, func(w uint64) bool { return call(Budget{MaxWork: w}) == nil })
	}
	leastDigits := func(call func(Budget) error) uint64 {
		return smallestAdmitting(1<<10, func(n uint64) bool { return call(Budget{MaxDigits: n}) == nil })
	}
	leastInput := func(call func(Budget) error) uint64 {
		return smallestAdmitting(1<<10, func(n uint64) bool { return call(Budget{MaxInputDigits: n}) == nil })
	}

	// A 39-digit integer below 2^128.
	wide := MustParse("3" + strings.Repeat("0", 37) + "7")
	if _, ok := wide.bigIntInline(nil); !ok {
		t.Fatal("the integer left the inline BigInt path")
	}
	bigInt := func(b Budget) error {
		_, err := wide.bigIntGeneral(nil, b, "BigInt")
		return err
	}
	if w, n, in := leastWork(bigInt), leastDigits(bigInt), leastInput(bigInt); w != inlineBigIntWork || n != inlineResultDigits || in != inlineResultDigits {
		t.Fatalf("BigInt admits from %d work, %d digits and %d input digits; bounds %d and %d", w, n, in, inlineBigIntWork, inlineResultDigits)
	}

	// Sixteen bytes: the envelope reads the raw length alone.
	raw := []byte{0x7f, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}
	binary := func(b Budget) error {
		_, err := fromBinaryGeneral(raw, false, true, false, 0, b, "NewTwosComplement")
		return err
	}
	if w, n, in := leastWork(binary), leastDigits(binary), leastInput(binary); w != inlineBinaryWork || n != inlineBinaryDigits || in != inlineBinaryDigits {
		t.Fatalf("NewTwosComplement admits from %d work, %d digits and %d input digits; bounds %d and %d", w, n, in, inlineBinaryWork, inlineBinaryDigits)
	}

	// A 20-digit coefficient with no factor of ten at 19 fraction digits.
	fraction := inlineDecimal(uint128{lo: math.MaxUint64 - 2}, -19, false)
	if _, ok := fraction.ratInline(nil); !ok {
		t.Fatal("the fraction left the inline Rat path")
	}
	rat := func(b Budget) error {
		_, err := fraction.ratGeneral(nil, b, "Rat")
		return err
	}
	if w, n, in := leastWork(rat), leastDigits(rat), leastInput(rat); w != inlineRatEgressWork || n != inlineRatEgressDigits || in != inlineRatEgressDigits {
		t.Fatalf("Rat admits from %d work, %d digits and %d input digits; bounds %d and %d", w, n, in, inlineRatEgressWork, inlineRatEgressDigits)
	}

	least := func(call func(limits) error) uint64 {
		return smallestAdmitting(1<<20, func(w uint64) bool { return call(limits{MaxWork: w}) == nil })
	}

	// 3/1 at 38 fraction digits: a 39-digit result from a three-word
	// scaled numerator.
	three := big.NewRat(3, 1)
	n, d, ok := ratInlineOperands(three)
	if _, _, refused, served := inlineDivToExponent(n, d, -38, TiesToEven); !ok || !served || refused {
		t.Fatal("the rational left the inline FromRatToExponent path")
	}
	if got := least(func(b limits) error {
		_, _, err := fromRatToExponent(three, -38, TiesToEven, b, "FromRatToExponent")
		return err
	}); got != inlineRatWork {
		t.Fatalf("FromRatToExponent admits from %d, bound %d", got, inlineRatWork)
	}

	// A 39-digit dividend over 10^19: 67 planned fraction digits and a
	// 39-digit quotient.
	ten19 := MustParse("1" + strings.Repeat("0", 19))
	if q, ok := inlineDivExact(wide, ten19); !ok || q.CoefficientDigits() != inlineResultDigits {
		t.Fatalf("the exact quotient left the inline path: %v %v", q, ok)
	}
	if got := least(func(b limits) error {
		_, _, err := wide.divUnlimitedLimbs(ten19, b, "Div")
		return err
	}); got != inlineDivExactWork {
		t.Fatalf("exact Div admits from %d, bound %d", got, inlineDivExactWork)
	}

	// RemNear of a 38-digit dividend one place above a 39-digit divisor
	// that exceeds twice the dividend: a zero quotient, the comparison
	// path, and the padded dividend as the 39-digit result.
	dividend := MustParse("1" + strings.Repeat("0", 36) + "1E+1")
	if _, _, ok := inlineIntDivide(dividend, wide, intDivRemNear, &Context{}); !ok {
		t.Fatal("the remainder left the inline path")
	}
	var count quoRemCount
	if got := least(func(b limits) error {
		count = quoRemCount{}
		_, _, err := dividend.intDivide(wide, intDivRemNear, Context{}, b, "RemNear", &count)
		return err
	}); got != inlineIntDivWork || count.taken != intDivQZeroNear {
		t.Fatalf("RemNear admits from %d on path %d, bound %d", got, count.taken, inlineIntDivWork)
	}
}

// TestIntDivInlineBoundCoversPlanner prices every shape the inline integer
// division serves with the kernel's planner: coefficients of up to 39
// digits that align within 39 digits, each quotient class the shape
// allows, and the largest result. No charge exceeds inlineIntDivWork, and
// RemNear attains it.
func TestIntDivInlineBoundCoversPlanner(t *testing.T) {
	var most [3]uint64
	for op := intDivQuo; op <= intDivRemNear; op++ {
		for dx := uint64(1); dx <= 39; dx++ {
			for dy := uint64(1); dy <= 39; dy++ {
				for k := int64(-38); k <= 38; k++ {
					if k >= 0 && dx+uint64(k) > 39 || k < 0 && dy+uint64(-k) > 39 {
						continue
					}
					s := intDivShape{dx: dx, dy: dy, ex: int32(k)}
					b, _ := intDivPrecharge(dx, dy, false)
					price := func(qZero bool, q uint64) {
						plan := planIntDiv(op, s, qZero, q, intDivForceNone)
						w, ok := intDivWork(b, plan.c, min(plan.nEnv, inlineResultDigits))
						if !plan.ok || !ok {
							t.Fatalf("op %d dx=%d dy=%d k=%d: no plan", op, dx, dy, k)
						}
						most[op] = max(most[op], w)
					}
					switch delta := s.delta(); {
					case delta < 0:
						price(true, 1)
					case delta == 0:
						price(true, 1)
						price(false, 1)
					default:
						price(false, uint64(delta))
						if delta < inlineResultDigits {
							price(false, uint64(delta)+1)
						}
					}
				}
			}
		}
	}
	if most[intDivQuo] > inlineIntDivWork || most[intDivRem] > inlineIntDivWork || most[intDivRemNear] != inlineIntDivWork {
		t.Fatalf("largest planned charges %v, bound %d", most, inlineIntDivWork)
	}
}

// TestRoundToMultipleShapeBudgetInlineMatchesGeneral pins RoundToMultiple
// under budgets below the constant bounds of its inline path to the
// general path: the inline path prices the call as the general path does,
// so it serves every budget the general path admits, down to the smallest
// admitting caps, and defers every budget it refuses.
func TestRoundToMultipleShapeBudgetInlineMatchesGeneral(t *testing.T) {
	r := randv2.New(randv2.NewPCG(93, 94))
	const op = "RoundToMultipleWithBudget"
	steps := []string{"0.05", "0.25", "0.01", "5", "0.5", "1", "0.125", "25", "1E+2", "0.0005", "3", "0.07"}
	var served, threshold, belowBound, refused, zero int
	for i := range 60000 {
		x := shortOperand(r, 12)
		m := MustParse(steps[r.IntN(len(steps))])
		switch i % 4 {
		case 0:
			m = shortOperand(r, 12).Abs()
		case 1:
			m = shortOperand(r, 3).Abs()
			x = shortOperand(r, 3).withExponent(m.exponent() + int32(r.IntN(25)))
		case 2:
			x = New(int64(r.Uint64N(pow10Words[1+r.IntN(12)])), -int32(r.IntN(8)))
		}
		mode := RoundingMode(r.IntN(int(Exact) + 1))
		var quotient Decimal
		inline := false
		if !m.negative() && inlineDivShape(x, m) {
			unit := m.withExponent(0)
			if q, _, refusal, ok := inlineDivToExponent(x, unit, m.exponent(), mode); ok && !refusal {
				_, fits := inlineMul(q.withExponent(0), unit)
				quotient, inline = q, q.isZero() || fits
			}
		}
		ladder, least, measured := budgetLadder(r, func(b limits) error {
			_, _, err := x.roundToMultipleLimbs(m, mode, b, op)
			return err
		})
		for _, b := range ladder {
			got, gc, gerr := x.roundToMultiple(m, mode, b, op)
			want, wc, werr := x.roundToMultipleLimbs(m, mode, b, op)
			samePathOutcome(t, op, got, gc, gerr, want, wc, werr)
			if !inline || b == (limits{}) {
				continue
			}
			ok := b.admits(roundToMultipleInlineDigits, roundToMultipleInlineWork) || roundToMultipleInlineAdmitted(x, m, quotient, b)
			if ok == refusedForBudget(werr) {
				t.Fatalf("RoundToMultiple(%v, %v) mode %v budget %+v: the inline gate admits %v, the general path returns %v", x, m, mode, b, ok, werr)
			}
			switch {
			case !ok:
				refused++
			case measured && b == least:
				threshold++
				fallthrough
			default:
				served++
				if !b.admits(roundToMultipleInlineDigits, roundToMultipleInlineWork) {
					belowBound++
				}
				if quotient.isZero() {
					zero++
				}
			}
		}
	}
	if served < 50000 || threshold < 10000 || belowBound < 20000 || refused < 50000 || zero < 2000 {
		t.Fatalf("vacuous coverage: %d served, %d at the threshold, %d below the constant bounds, %d refused, %d zero quotients", served, threshold, belowBound, refused, zero)
	}
}

// TestParseContextBudgetedWordsMatchesSource pins budgeted ParseWithContext
// of a literal of up to 38 bytes to the rounding source under the same
// budget: the same value, cohort, Conditions and error. The word path
// serves exactly the budgets the source admits: the input bytes, and the
// retained digits min(D, p), at each threshold and one below.
func TestParseContextBudgetedWordsMatchesSource(t *testing.T) {
	r := randv2.New(randv2.NewPCG(95, 96))
	ctxs := shortContexts()
	const op = "ParseWithContext"
	var served, threshold, refusedDigits, refusedBytes, rounded int
	for range 200000 {
		s := roundingLiteral(r)
		ctx := ctxs[r.IntN(len(ctxs))]
		if ctx.precision == 0 {
			continue
		}
		inline, rounds, digits := false, false, uint64(0)
		var exact Decimal
		if len(s) <= parseRoundInlineMax {
			var ok bool
			if exact, ok = parseExactWords(s); ok && !exact.isZero() {
				digits = min(exact.CoefficientDigits(), uint64(ctx.precision))
				if contextExactFits(exact, ctx) {
					inline = true
				} else if _, _, ok := contextRoundInline(exact, ctx); ok {
					inline, rounds = true, true
				}
			}
		}
		budgets := []textLimits{{MaxDigits: uint64(1 + r.IntN(40))}, {MaxInputBytes: uint64(1 + r.IntN(45))},
			{MaxDigits: uint64(1 + r.IntN(40)), MaxInputBytes: uint64(1 + r.IntN(45))}, {MaxDigits: 1 << 20, MaxInputBytes: 1 << 20}}
		at := textLimits{MaxDigits: digits, MaxInputBytes: uint64(len(s))}
		if inline {
			budgets = append(budgets, at, textLimits{MaxDigits: digits}, textLimits{MaxInputBytes: uint64(len(s))})
			if digits > 1 {
				budgets = append(budgets, textLimits{MaxDigits: digits - 1})
			}
			if len(s) > 1 {
				budgets = append(budgets, textLimits{MaxInputBytes: uint64(len(s) - 1)})
			}
		}
		for _, b := range budgets {
			got, gc, gerr := parseWithContext(s, ctx, b, op)
			want, wc, werr := parseRounded(s, ctx, b, op)
			if (gerr == nil) != (werr == nil) || gerr != nil && gerr.Error() != werr.Error() {
				t.Fatalf("parse %q p=%d budget %+v: error %v vs %v", s, ctx.precision, b, gerr, werr)
			}
			if gerr == nil {
				samePathOutcome(t, "parse "+s, got, gc, gerr, want, wc, werr)
			}
			if !inline {
				continue
			}
			bytesAdmitted := b.MaxInputBytes == 0 || uint64(len(s)) <= b.MaxInputBytes
			admitted := bytesAdmitted && parseRoundDigitsAdmitted(exact, ctx.precision, b.MaxDigits)
			if admitted == refusedForBudget(werr) {
				t.Fatalf("parse %q p=%d budget %+v: the word path admits %v, the source returns %v", s, ctx.precision, b, admitted, werr)
			}
			switch {
			case !bytesAdmitted:
				refusedBytes++
			case !admitted:
				refusedDigits++
			default:
				served++
				if b == at {
					threshold++
				}
				if rounds {
					rounded++
				}
			}
		}
	}
	if served < 100000 || threshold < 20000 || refusedDigits < 20000 || refusedBytes < 20000 || rounded < 20000 {
		t.Fatalf("vacuous coverage: %d served, %d at the threshold, %d refused for digits, %d refused for bytes, %d rounded", served, threshold, refusedDigits, refusedBytes, rounded)
	}
}

// TestFMAWideProductInlineMatchesGeneral pins FMAWithContext of factors
// whose product leaves two words to the product-term path, and the 256-bit
// sum it rounds to math/big: the sum is served exactly when the addend is
// a nonzero inline value within 38 places of the product, the aligned
// product and the sum stay below 2^256, and the sum is not zero.
func TestFMAWideProductInlineMatchesGeneral(t *testing.T) {
	r := randv2.New(randv2.NewPCG(97, 98))
	ctxs := shortContexts()
	limit := new(big.Int).Lsh(big.NewInt(1), 256)
	ten := big.NewInt(10)
	var served, scaledProduct, scaledAddend, cancelled, overflow, exact, far int
	for i := range 300000 {
		x, y, z := shortOperand(r, 15), shortOperand(r, 15), shortOperand(r, 15)
		e := int64(x.exponent()) + int64(y.exponent())
		z = z.withExponent(int32(e) + int32(r.IntN(85)-42))
		switch i % 8 {
		case 0:
			// An addend that cancels the product's leading digits.
			if p, err := x.Mul(y); err == nil {
				if head, _, err := p.RoundToPrecision(uint32(10+r.IntN(29)), TowardZero); err == nil && head.slow == nil {
					z = head.Neg()
				}
			}
		case 1:
			// Factors and an addend at the top of two words, toward 2^256.
			x = MustParse("340282366920938463463374607431768211455").withExponent(x.exponent()).withNegative(x.negative())
			y = MustParse("3402823669209384634633746074317682114" + strconv.Itoa(10+r.IntN(46))).withExponent(y.exponent()).withNegative(y.negative())
			z = z.withExponent(int32(e) - int32(r.IntN(3)))
		case 2:
			// Round factors, whose sum with a short addend can fit the precision.
			x = New(int64(1+r.IntN(9)), int32(10+r.IntN(20)))
			x, _, _ = x.Quantize(0, Exact)
			y = New(int64(1+r.IntN(99)), int32(10+r.IntN(9)))
			y, _, _ = y.Quantize(0, Exact)
			z = New(int64(1+r.IntN(999)), int32(15+r.IntN(20)))
			e = 0
		}
		ctx := ctxs[r.IntN(len(ctxs))]
		if ctx.precision == 0 {
			continue
		}
		if _, short := inlineMul(x, y); !short && x.slow == nil && y.slow == nil && e >= math.MinInt32 && e <= math.MaxInt32 {
			sum, exponent, negative, ok := wideFMASum(x, y, z, e)
			product := new(big.Int).Mul(wideToBig(wide256{x.words.lo, x.words.hi}), wideToBig(wide256{y.words.lo, y.words.hi}))
			addend := wideToBig(wide256{z.words.lo, z.words.hi})
			gap := e - int64(z.exponent())
			switch {
			case gap > 0:
				product.Mul(product, new(big.Int).Exp(ten, big.NewInt(gap), nil))
			case gap < 0:
				addend.Mul(addend, new(big.Int).Exp(ten, big.NewInt(-gap), nil))
			}
			fits := product.Cmp(limit) < 0
			if x.negative() != y.negative() {
				product.Neg(product)
			}
			if z.negative() {
				addend.Neg(addend)
			}
			total := new(big.Int).Add(product, addend)
			want := z.slow == nil && !z.isZero() && gap >= -38 && gap <= 38 && fits && total.Sign() != 0 && new(big.Int).Abs(total).Cmp(limit) < 0
			if ok != want {
				t.Fatalf("wideFMASum(%v, %v, %v) ok %v, want %v", x, y, z, ok, want)
			}
			switch {
			case ok:
				if wideToBig(sum).CmpAbs(total) != 0 || negative != (total.Sign() < 0) || exponent != min(e, int64(z.exponent())) {
					t.Fatalf("wideFMASum(%v, %v, %v) = %s (negative %v) e%d, want %s", x, y, z, wideToBig(sum), negative, exponent, total)
				}
				if rounded, events, done := contextRoundWide(sum, exponent, negative, ctx); done {
					served++
					switch {
					case gap > 0:
						scaledProduct++
					case gap < 0:
						scaledAddend++
					}
					if product.Sign() != addend.Sign() && total.BitLen() < product.BitLen()-20 {
						cancelled++
					}
					if events&Inexact == 0 && !rounded.isZero() {
						exact++
					}
				}
			case gap < -38 || gap > 38:
				far++
			case !fits || new(big.Int).Abs(total).Cmp(limit) >= 0:
				overflow++
			}
		}
		got, gc, gerr := x.FMAWithContext(y, z, ctx.withLimits(limits{}))
		want, wc, werr := x.fmaGeneral(y, z, ctx.withLimits(limits{}))
		samePathOutcome(t, "FMA wide product", got, gc, gerr, want, wc, werr)
	}
	if served < 30000 || scaledProduct < 5000 || scaledAddend < 5000 || cancelled < 1000 || overflow < 1000 || exact < 300 || far < 1000 {
		t.Fatalf("vacuous coverage: %d served, %d with a scaled product, %d with a scaled addend, %d cancelled, %d overflows, %d exact, %d too far",
			served, scaledProduct, scaledAddend, cancelled, overflow, exact, far)
	}
}

// sumInlineBound restates the charges of the dearest inline Sum of k
// operands: an envelope of 19+39 digits plus the carry digits of k, and W =
// k + 39k + 2·t(L).
func sumInlineBound(k int) limits {
	carries := uint64(0)
	for n := 1; n < k; n *= 10 {
		carries++
	}
	envelope := 19 + 39 + carries
	return limits{envelope, uint64(k) + 39*uint64(k) + 2*(1+(envelope-1)/9)}
}

// TestSumBudgetedInlineMatchesPlanned pins the budgeted Sum that skips the
// header scan to the planned path under the same budget: the same sum and
// the same refusal. The skip is taken exactly at and above the charges of
// the dearest inline shape of the operand count, where the planned path
// never refuses; below them the planned path decides.
func TestSumBudgetedInlineMatchesPlanned(t *testing.T) {
	r := randv2.New(randv2.NewPCG(99, 100))
	const op = "SumWithBudget"
	var served, atBound, below, belowAdmitted, outside, zeros, many int
	for i := range 40000 {
		k := 1 + r.IntN(12)
		if i%40 == 3 {
			k = 90 + r.IntN(1200)
		}
		values := make([]Decimal, k)
		base, span := int32(r.IntN(41)-20), 20
		if i%5 == 0 {
			span = 40 // beyond the inline window
		}
		for j := range values {
			values[j] = shortOperand(r, 0).withExponent(base + int32(r.IntN(span)))
			if i%7 == 0 && r.IntN(2) == 0 {
				values[j] = zeroDecimal(values[j].exponent())
			}
		}
		if i%11 == 0 {
			values[r.IntN(k)] = MustParse("1" + strings.Repeat("0", 45)).withExponent(base)
		}
		_, nonzero, shape := sumInlineShape(values)
		bound := sumInlineBound(k)
		ladder, _, _ := budgetLadder(r, func(b limits) error {
			_, err := sumPlanned(values, b, op)
			return err
		})
		ladder = append(ladder, bound, limits{bound.MaxDigits - 1, bound.MaxWork}, limits{bound.MaxDigits, bound.MaxWork - 1}, limits{0, bound.MaxWork}, limits{bound.MaxDigits, 0})
		for _, b := range ladder {
			got, gerr := sumValues(values, b, op)
			want, werr := sumPlanned(values, b, op)
			samePathOutcome(t, op, got, 0, gerr, want, 0, werr)
			if !shape {
				outside++
				continue
			}
			if b == (limits{}) {
				continue
			}
			quick := sumInlineBoundAdmitted(k, b)
			if quick != b.admits(bound.MaxDigits, bound.MaxWork) {
				t.Fatalf("%d operands budget %+v: the bound admits %v, restated bound %+v", k, b, quick, bound)
			}
			switch {
			case quick && refusedForBudget(werr):
				t.Fatalf("%d operands budget %+v: the bound admits a call the planned path refuses", k, b)
			case quick:
				served++
				if b == bound {
					atBound++
				}
				if !nonzero {
					zeros++
				}
				if k >= 90 {
					many++
				}
			default:
				below++
				if !refusedForBudget(werr) {
					belowAdmitted++
				}
			}
		}
	}
	if served < 50000 || atBound < 20000 || below < 50000 || belowAdmitted < 20000 || outside < 20000 || zeros < 50 || many < 1000 {
		t.Fatalf("vacuous coverage: %d served, %d at the bound, %d below it, %d of them admitted by the planned path, %d outside the inline shape, %d zero sums, %d long lists",
			served, atBound, below, belowAdmitted, outside, zeros, many)
	}
}

// TestSumInlineBoundAtExtremes measures the planned Sum's smallest
// admitting caps on the dearest inline shape, 39-digit coefficients
// spanning 19 exponent places: both are the bound the header-scan skip
// uses, for one operand, for eight and across a carry digit.
func TestSumInlineBoundAtExtremes(t *testing.T) {
	const op = "SumWithBudget"
	wide := MustParse("3" + strings.Repeat("0", 37) + "7")
	for _, k := range []int{1, 2, 8, 10, 11, 101} {
		values := make([]Decimal, k)
		for j := range values {
			values[j] = wide
		}
		values[k-1] = wide.withExponent(19)
		if k == 1 {
			// One operand spans its own digits: the bound is not attained.
			values[0] = wide
		}
		if _, _, ok := sumInlineShape(values); !ok {
			t.Fatal("the operands left the inline shape")
		}
		work := smallestAdmitting(1<<24, func(w uint64) bool { _, err := sumPlanned(values, limits{MaxWork: w}, op); return err == nil })
		digits := smallestAdmitting(1<<12, func(n uint64) bool { _, err := sumPlanned(values, limits{MaxDigits: n}, op); return err == nil })
		bound := sumInlineBound(k)
		if k == 1 {
			if work > bound.MaxWork || digits > bound.MaxDigits {
				t.Fatalf("one operand admits from %d work and %d digits, bound %+v", work, digits, bound)
			}
			continue
		}
		if work != bound.MaxWork || digits != bound.MaxDigits {
			t.Fatalf("%d operands admit from %d work and %d digits, bound %+v", k, work, digits, bound)
		}
		if !sumInlineBoundAdmitted(k, bound) || sumInlineBoundAdmitted(k, limits{bound.MaxDigits, bound.MaxWork - 1}) || sumInlineBoundAdmitted(k, limits{bound.MaxDigits - 1, bound.MaxWork}) {
			t.Fatalf("%d operands: the skip is not taken exactly from %+v", k, bound)
		}
	}
}

// TestScanBigSourcesMatchGeneral pins Scan of math/big sources that fit
// machine words to the general conversions under the same budget.
func TestScanBigSourcesMatchGeneral(t *testing.T) {
	r := randv2.New(randv2.NewPCG(91, 92))
	budgets := []Budget{{}, {MaxDigits: 39, MaxWork: 1 << 20}, {MaxDigits: 3}, {MaxWork: 30}, {MaxDigits: 20, MaxWork: 200}, {MaxInputBytes: 3}}
	word := func() uint64 { return r.Uint64() >> uint(r.IntN(64)) }
	served, refused, inexact := 0, 0, 0
	for range 100000 {
		b := budgets[r.IntN(len(budgets))]
		arith := Budget{MaxInputDigits: b.MaxDigits, MaxDigits: b.MaxDigits, MaxWork: b.MaxWork}

		x := new(big.Int).SetUint64(word())
		if r.IntN(3) == 0 {
			x.Lsh(x, uint(r.IntN(66)))
		}
		if r.IntN(2) == 0 {
			x.Neg(x)
		}
		got, gerr := scanValue(x, b, "Scan")
		want, werr := fromBigIntOnTarget(x, arith, "Scan", bigIntIngressRuntimeTarget())
		if bits := uint64(x.BitLen()); b.MaxInputBytes != 0 && (bits+7)/8 > b.MaxInputBytes {
			if gerr == nil {
				t.Fatalf("Scan(%v) passed the input-byte cap", x)
			}
		} else {
			samePathOutcome(t, "Scan big.Int", got, 0, gerr, want, 0, werr)
		}

		q := new(big.Rat).SetFrac(new(big.Int).SetUint64(word()), new(big.Int).SetUint64(1+word()))
		if r.IntN(2) == 0 {
			// A terminating quotient: a denominator of twos and fives.
			q.SetFrac(q.Num(), new(big.Int).SetUint64(1<<uint(r.IntN(20))*pow10Words[r.IntN(8)]))
		}
		if r.IntN(2) == 0 {
			q.Neg(q)
		}
		got, gerr = scanValue(q, b, "Scan")
		want, _, werr = fromRatExact(q, arith.arith(), "Scan")
		if bn, bd := uint64(q.Num().BitLen()), uint64(q.Denom().BitLen()); b.MaxInputBytes != 0 && (bn+7)/8+(bd+7)/8 > b.MaxInputBytes {
			if gerr == nil {
				t.Fatalf("Scan(%v) passed the input-byte cap", q)
			}
			continue
		}
		if (gerr == nil) != (werr == nil) {
			t.Fatalf("Scan(%v) under %+v: %v, general %v", q, b, gerr, werr)
		}
		switch e, _ := gerr.(*Error); {
		case gerr == nil:
			samePathOutcome(t, "Scan big.Rat", got, 0, nil, want, 0, nil)
			served++
		case e != nil && e.Condition == Inexact:
			inexact++
		default:
			refused++
		}
	}
	if served < 15000 || refused < 1000 || inexact < 10000 {
		t.Fatalf("vacuous coverage: served %d, refused %d, inexact %d", served, refused, inexact)
	}
}
