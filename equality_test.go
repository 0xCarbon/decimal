// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"bytes"
	"encoding/binary"
	"errors"
	"fmt"
	"go/ast"
	"go/token"
	"hash/maphash"
	"math"
	"math/big"
	"math/bits"
	"math/rand"
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"runtime"
	"slices"
	"strconv"
	"strings"
	"testing"
)

func TestEqualityNumericCohortsAndOrder(t *testing.T) {
	pairs := []struct {
		a, b string
		want int
	}{
		{"1", "1.00", 0},
		{"1.0", "1.00", 0},
		{"-0.00", "0E+9", 0},
		{"-2.0", "-1.5", -1},
		{"-1", "0", -1},
		{"0", "1E-2147483648", -1},
		{"1E+2147483647", "9E+2147483646", 1},
		{"1E-2147483648", "9E-2147483648", -1},
		{"340282366920938463463374607431768211455", "340282366920938463463374607431768211456", -1},
		{"100000E+2147483647", "1000000E+2147483646", 0},
	}
	for _, tc := range pairs {
		a, b := MustParse(tc.a), MustParse(tc.b)
		if got := a.Compare(b); got != tc.want {
			t.Errorf("Compare(%s,%s)=%d, want %d", tc.a, tc.b, got, tc.want)
		}
		if got := b.Compare(a); got != -tc.want {
			t.Errorf("reverse Compare(%s,%s)=%d, want %d", tc.b, tc.a, got, -tc.want)
		}
		if got := a.Equal(b); got != (tc.want == 0) {
			t.Errorf("Equal(%s,%s)=%v", tc.a, tc.b, got)
		}
		if got := (Hasher{}).Equal(a, b); got != a.Equal(b) {
			t.Errorf("Hasher.Equal(%s,%s)=%v", tc.a, tc.b, got)
		}
	}
}

func TestCoefficientViewWordBoundariesAndTotalOrder(t *testing.T) {
	values := []string{
		"-340282366920938463463374607431768211456",
		"-18446744073709551616",
		"-18446744073709551615",
		"-1000000000",
		"-1",
		"0",
		"1",
		"999999999",
		"1000000000",
		"18446744073709551615",
		"18446744073709551616",
		"340282366920938463463374607431768211455",
		"340282366920938463463374607431768211456",
	}
	parsed := make([]Decimal, len(values))
	for i, s := range values {
		parsed[i] = MustParse(s)
		if i != 0 && parsed[i-1].Compare(parsed[i]) >= 0 {
			t.Fatalf("not ascending: %s, %s", values[i-1], s)
		}
		if i == 0 || i == len(values)-1 {
			if parsed[i].slow == nil {
				t.Fatalf("expected slow band at %s", s)
			}
		}
		if s == "340282366920938463463374607431768211455" && parsed[i].slow != nil {
			t.Fatal("2^128-1 must be inline")
		}
		v := coefficientViewOf(parsed[i])
		if s == "0" {
			if v.count != 0 {
				t.Fatalf("zero has %d limbs", v.count)
			}
			continue
		}
		var rebuilt big.Int
		base := big.NewInt(1_000_000_000)
		for j := v.count - 1; j >= 0; j-- {
			rebuilt.Mul(&rebuilt, base)
			rebuilt.Add(&rebuilt, new(big.Int).SetUint64(uint64(v.limb(j))))
		}
		if rebuilt.String() != strings.TrimPrefix(s, "-") {
			t.Fatalf("limb view for %s rebuilds as %s", s, &rebuilt)
		}
	}
	for i := range parsed {
		for j := range parsed {
			want := 0
			if i < j {
				want = -1
			} else if i > j {
				want = 1
			}
			if got := parsed[i].Compare(parsed[j]); got != want {
				t.Fatalf("Compare(%s,%s)=%d, want %d", values[i], values[j], got, want)
			}
		}
	}
}

func TestReduceDomainBoundAndCohortText(t *testing.T) {
	for _, tc := range []struct{ input, want string }{
		{"1.2300", "1.23"},
		{"0.00", "0"},
		{"100000E+2147483647", "1.00000E+2147483652"},
		{"1000000E+2147483646", "1.00000E+2147483652"},
		{"1000000000000000000000000000000000000000E-2147483648", "1E-2147483609"},
	} {
		d := MustParse(tc.input)
		before := d.String()
		copyOfD := d
		r := d.Reduce()
		if got := r.String(); got != tc.want {
			t.Errorf("Reduce(%s)=%s, want %s", tc.input, got, tc.want)
		}
		if !d.Equal(r) || !r.Equal(r.Reduce()) {
			t.Errorf("Reduce numeric/idempotence failure for %s", tc.input)
		}
		if d.String() != before || copyOfD.String() != before {
			t.Errorf("Reduce mutated source/copy of %s", tc.input)
		}
	}
}

func TestHasherCanonicalEncodingAndBands(t *testing.T) {
	seed := maphash.MakeSeed()
	for _, tc := range []struct {
		literal  string
		preimage []byte
	}{
		{"0.00", []byte{0}},
		{"1.00", expectedHashPreimage(1, 0, 1)},
		{"-1.00", expectedHashPreimage(2, 0, 1)},
		{"100000E+2147483647", expectedHashPreimage(1, math.MaxInt32, 100000)},
		{"1000000E+2147483646", expectedHashPreimage(1, math.MaxInt32, 100000)},
	} {
		var got, want maphash.Hash
		got.SetSeed(seed)
		want.SetSeed(seed)
		(Hasher{}).Hash(&got, MustParse(tc.literal))
		_, _ = want.Write(tc.preimage)
		if got.Sum64() != want.Sum64() {
			t.Errorf("Hash preimage mismatch for %s", tc.literal)
		}
	}
	for _, literal := range []string{"1.00", "340282366920938463463374607431768211455", "-123456789012345678900000000000000000000"} {
		a := MustParse(literal)
		b := forceSlowBandForTest(t, a)
		if !a.Equal(b) || a.Compare(b) != 0 || a.Reduce().Compare(b.Reduce()) != 0 {
			t.Errorf("band semantics diverge for %s", literal)
		}
		var x, y maphash.Hash
		x.SetSeed(seed)
		y.SetSeed(seed)
		(Hasher{}).Hash(&x, a)
		(Hasher{}).Hash(&y, b)
		if x.Sum64() != y.Sum64() {
			t.Errorf("band hash diverges for %s", literal)
		}
		before := b.String()
		copyOfB := b
		_ = b.Reduce()
		if b.String() != before || copyOfB.String() != before {
			t.Errorf("slow Reduce mutated shared source for %s", literal)
		}
	}
}

func TestHasherLimbCountVarintBoundary(t *testing.T) {
	seed := maphash.MakeSeed()
	for _, tc := range []struct {
		limbs    int
		negative bool
		count    []byte
	}{
		{127, false, []byte{0x7f}},
		{128, true, []byte{0x80, 0x01}},
	} {
		// 10^(9*(limbs-1))+1 has exactly the requested base-10^9 limb
		// count, with first and last limbs equal to one and no trailing zero.
		coefficient := "1" + strings.Repeat("0", 9*(tc.limbs-1)-1) + "1"
		d := decimalFromParts(t, coefficient, 0, tc.negative)
		if d.slow == nil || len(d.slow.limbs) != tc.limbs {
			t.Fatalf("coefficient with %d digits stored as %d limbs", len(coefficient), tc.limbs)
		}
		tag := byte(1)
		if tc.negative {
			tag = 2
		}
		// Build the framing directly from the hand-chosen limb pattern;
		// no production reduction or cursor is used for the expected bytes.
		preimage := []byte{tag, 0, 0, 0, 0}
		preimage = append(preimage, tc.count...)
		for i := range tc.limbs {
			var block [4]byte
			if i == 0 || i == tc.limbs-1 {
				block[3] = 1
			}
			preimage = append(preimage, block[:]...)
		}
		if len(preimage) != 5+len(tc.count)+4*tc.limbs {
			t.Fatal("incorrect independent preimage length")
		}
		var got, want maphash.Hash
		got.SetSeed(seed)
		want.SetSeed(seed)
		_, _ = got.WriteString("prefix")
		_, _ = want.WriteString("prefix")
		(Hasher{}).Hash(&got, d)
		_, _ = want.Write(preimage)
		if got.Sum64() != want.Sum64() {
			t.Errorf("%d-limb hash framing differs from independent preimage", tc.limbs)
		}
	}
}

func TestCompareIndependentBoundedRatOracle(t *testing.T) {
	rng := rand.New(rand.NewSource(20260922))
	for i := range 500 {
		ac := strconv.FormatUint(rng.Uint64()%1_000_000_000_000_000_000+1, 10)
		bc := strconv.FormatUint(rng.Uint64()%1_000_000_000_000_000_000+1, 10)
		ae, be := rng.Intn(41)-20, rng.Intn(41)-20
		an, bn := rng.Intn(2) == 0, rng.Intn(2) == 0
		a := decimalFromParts(t, ac, ae, an)
		b := decimalFromParts(t, bc, be, bn)
		want := ratFromParts(t, ac, ae, an).Cmp(ratFromParts(t, bc, be, bn))
		if got := a.Compare(b); got != want {
			t.Fatalf("oracle mismatch at %d: %s e%d vs %s e%d: got %d want %d", i, ac, ae, bc, be, got, want)
		}
	}
}

func TestCompareEqualAdjustedExponentAcrossLimbBoundary(t *testing.T) {
	// Each pair has the same adjusted exponent. The 9/10 and 18/19 digit
	// transitions force comparison between one and multiple base-10^9 limbs.
	for _, tc := range []struct {
		ac, bc     string
		ae, be     int32
		negative   bool
		want       int
		boundedRat bool
	}{
		{"100000001", "1000000001", 0, -1, false, 1, true},
		{"100000000", "1000000001", 0, -1, false, -1, true},
		{"100000001", "1000000001", 0, -1, true, -1, true},
		{"100000000000000001", "1000000000000000001", 0, -1, false, 1, true},
		// At MaxInt32, compare 100000001 with 100000000.1 after
		// factoring out 10^MaxInt32. At MinInt32, compare 1000000000
		// with 1000000001 after factoring out 10^MinInt32.
		{"100000001", "1000000001", math.MaxInt32, math.MaxInt32 - 1, false, 1, false},
		{"100000000", "1000000001", math.MinInt32 + 1, math.MinInt32, false, -1, false},
	} {
		aAdjusted := int64(tc.ae) + int64(len(tc.ac)) - 1
		bAdjusted := int64(tc.be) + int64(len(tc.bc)) - 1
		if aAdjusted != bAdjusted {
			t.Fatalf("bad directed pair %s e%d, %s e%d: adjusted exponents %d and %d", tc.ac, tc.ae, tc.bc, tc.be, aAdjusted, bAdjusted)
		}
		a := decimalFromParts(t, tc.ac, int(tc.ae), tc.negative)
		b := decimalFromParts(t, tc.bc, int(tc.be), tc.negative)
		if tc.boundedRat {
			oracle := ratFromParts(t, tc.ac, int(tc.ae), tc.negative).Cmp(ratFromParts(t, tc.bc, int(tc.be), tc.negative))
			if oracle != tc.want {
				t.Fatalf("bad bounded oracle vector %s e%d, %s e%d: %d, want %d", tc.ac, tc.ae, tc.bc, tc.be, oracle, tc.want)
			}
		}
		if got := a.Compare(b); got != tc.want {
			t.Errorf("Compare(%s e%d,%s e%d)=%d, want %d", tc.ac, tc.ae, tc.bc, tc.be, got, tc.want)
		}
		if got := b.Compare(a); got != -tc.want {
			t.Errorf("reverse Compare(%s e%d,%s e%d)=%d, want %d", tc.bc, tc.be, tc.ac, tc.ae, got, -tc.want)
		}
		if a.Equal(b) || (Hasher{}).Equal(a, b) {
			t.Errorf("unequal pair compared equal: %s e%d, %s e%d", tc.ac, tc.ae, tc.bc, tc.be)
		}
	}
}

func TestSaturatedZeroLimbCount(t *testing.T) {
	for _, exp := range []int32{math.MinInt32, math.MaxInt32} {
		distance := uint64(int64(math.MaxInt32) - int64(exp))
		if got := saturatedZeroLimbDigits(uint64(math.MaxInt), distance); got != distance {
			t.Errorf("huge span at exponent %d: got %d want %d", exp, got, distance)
		}
		for _, n := range []uint64{0, 1, 2, 100} {
			want := min(n*9, distance)
			if got := saturatedZeroLimbDigits(n, distance); got != want {
				t.Errorf("span %d at exponent %d: got %d want %d", n, exp, got, want)
			}
		}
	}
}

func TestReduceAndHashIndependentMultiLimbOracle(t *testing.T) {
	rng := rand.New(rand.NewSource(20260923))
	seed := maphash.MakeSeed()
	for i := range 700 {
		length := 1 + rng.Intn(115)
		var digits strings.Builder
		digits.WriteByte(byte('1' + rng.Intn(9)))
		for j := 1; j < length; j++ {
			digits.WriteByte(byte('0' + rng.Intn(10)))
		}
		zeros := rng.Intn(35)
		coefficient := digits.String() + strings.Repeat("0", zeros)
		exponent := int32(rng.Intn(81) - 40)
		if i%47 == 0 {
			exponent = math.MaxInt32 - int32(rng.Intn(5))
		}
		if i%53 == 0 {
			exponent = math.MinInt32 + int32(rng.Intn(5))
		}
		negative := i%3 == 0
		d := decimalFromParts(t, coefficient, int(exponent), negative)
		if i%2 == 0 {
			d = forceSlowBandForTest(t, d)
		}
		original := d.String()
		wantCoefficient, ok := new(big.Int).SetString(coefficient, 10)
		if !ok {
			t.Fatal("bad oracle coefficient")
		}
		k := int64(len(coefficient) - len(strings.TrimRight(coefficient, "0")))
		distance := int64(math.MaxInt32) - int64(exponent)
		if k > distance {
			k = distance
		}
		wantCoefficient.Quo(wantCoefficient, new(big.Int).Exp(big.NewInt(10), big.NewInt(k), nil))
		wantExponent := int32(int64(exponent) + k)
		r := d.Reduce()
		if r.exponent() != wantExponent || r.coefficientDigits() != wantCoefficient.String() || r.negative() != negative {
			t.Fatalf("reduce oracle mismatch at %d: coeff %s e%d -> got %s e%d, want %s e%d", i, coefficient, exponent, r.coefficientDigits(), r.exponent(), wantCoefficient, wantExponent)
		}
		if d.String() != original || !d.Equal(r) || !r.Equal(r.Reduce()) {
			t.Fatalf("reduce mutation/equality/idempotence at %d", i)
		}
		wantBytes := oracleHashPreimage(t, wantCoefficient, wantExponent, negative)
		var got, want maphash.Hash
		got.SetSeed(seed)
		want.SetSeed(seed)
		(Hasher{}).Hash(&got, d)
		_, _ = want.Write(wantBytes)
		if got.Sum64() != want.Sum64() {
			t.Fatalf("hash preimage oracle mismatch at %d: coeff %s e%d", i, coefficient, exponent)
		}
	}
}

func TestDecimalCannotBeBuiltinMapKey(t *testing.T) {
	if runtime.GOOS == "js" || runtime.GOARCH == "wasm" {
		t.Skip("compile-negative consumer subprocess runs on native targets")
	}
	if _, err := exec.LookPath("go"); err != nil {
		t.Skipf("the go command is not available on this host (%v): the compile-negative consumer build needs it", err)
	}
	root, err := os.Getwd()
	if err != nil {
		t.Fatal(err)
	}
	dir := t.TempDir()
	mod := "module decimalcompileban\n\ngo 1.27\n\nrequire github.com/0xCarbon/decimal v0.0.0\nreplace github.com/0xCarbon/decimal => " + root + "\n"
	if err := os.WriteFile(filepath.Join(dir, "go.mod"), []byte(mod), 0o600); err != nil {
		t.Fatal(err)
	}
	src := "package p\nimport d \"github.com/0xCarbon/decimal\"\nvar _ = d.One() == d.Zero()\nvar _ map[d.Decimal]int\n"
	if err := os.WriteFile(filepath.Join(dir, "ban_test.go"), []byte(src), 0o600); err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command("go", "test", "-mod=mod", "./...")
	cmd.Dir = dir
	cmd.Env = append(os.Environ(), "CGO_ENABLED=0")
	out, err := cmd.CombinedOutput()
	if err == nil || !strings.Contains(string(out), "cannot be compared") || !strings.Contains(string(out), "invalid map key type") {
		t.Fatalf("expected both consumer compile bans, err=%v: %s", err, out)
	}
}

func FuzzEqualityScaleInvariant(f *testing.F) {
	for _, seed := range [][]byte{
		{0, 0, 0, 0, 1, 9, 9, 9, 0},
		{0x7f, 0xff, 0xff, 0xff, 9, 0, 0, 0, 9},
		{0x80, 0, 0, 0, 1, 0, 1, 0, 3},
		{0xff, 0xff, 0xff, 0xff, 3, 9, 0, 0, 7},
	} {
		f.Add(seed)
	}
	f.Fuzz(func(t *testing.T, data []byte) {
		if len(data) < 5 {
			return
		}
		exponent := int32(binary.BigEndian.Uint32(data[:4]))
		var coeff strings.Builder
		coeff.WriteByte('1' + data[4]%9)
		for i := 5; i < len(data) && i < 68; i++ {
			coeff.WriteByte('0' + data[i]%10)
		}
		shift := int64(data[len(data)-1] % 10)
		if int64(exponent)-shift < math.MinInt32 {
			shift = int64(exponent) - math.MinInt32
		}
		a := decimalFromParts(t, coeff.String(), int(exponent), false)
		b := decimalFromParts(t, coeff.String()+strings.Repeat("0", int(shift)), int(int64(exponent)-shift), false)
		if !a.validRepresentation() || !b.validRepresentation() || !a.Reduce().validRepresentation() || !b.Reduce().validRepresentation() {
			t.Fatalf("invalid representation before forced slow carrier")
		}
		if len(data)%2 == 0 {
			b = forceSlowBandForTest(t, b)
		}
		if !a.Equal(b) || a.Compare(b) != 0 || a.Reduce().Compare(b.Reduce()) != 0 {
			t.Fatalf("scale transform changed numeric value: %s e%d, shift %d", coeff.String(), exponent, shift)
		}
		seed := maphash.MakeSeed()
		var ah, bh maphash.Hash
		ah.SetSeed(seed)
		bh.SetSeed(seed)
		(Hasher{}).Hash(&ah, a)
		(Hasher{}).Hash(&bh, b)
		if ah.Sum64() != bh.Sum64() {
			t.Fatalf("scale transform changed hash: %s e%d, shift %d", coeff.String(), exponent, shift)
		}
	})
}

func oracleHashPreimage(t *testing.T, coefficient *big.Int, exponent int32, negative bool) []byte {
	t.Helper()
	if coefficient.Sign() == 0 {
		return []byte{0}
	}
	tag := byte(1)
	if negative {
		tag = 2
	}
	var limbs []uint32
	n := new(big.Int).Set(coefficient)
	base := big.NewInt(1_000_000_000)
	for n.Sign() != 0 {
		q, rem := new(big.Int), new(big.Int)
		q.QuoRem(n, base, rem)
		limbs = append(limbs, uint32(rem.Uint64()))
		n = q
	}
	b := make([]byte, 5)
	b[0] = tag
	binary.BigEndian.PutUint32(b[1:], uint32(exponent))
	var count [10]byte
	used := binary.PutUvarint(count[:], uint64(len(limbs)))
	b = append(b, count[:used]...)
	for _, limb := range slices.Backward(limbs) {
		var block [4]byte
		binary.BigEndian.PutUint32(block[:], limb)
		b = append(b, block[:]...)
	}
	return b
}

func expectedHashPreimage(tag byte, exp int32, limb uint32) []byte {
	b := []byte{tag, 0, 0, 0, 0, 1, 0, 0, 0, 0}
	binary.BigEndian.PutUint32(b[1:5], uint32(exp))
	binary.BigEndian.PutUint32(b[6:10], limb)
	return b
}

func forceSlowBandForTest(t *testing.T, d Decimal) Decimal {
	t.Helper()
	n := new(big.Int)
	if _, ok := n.SetString(d.coefficientDigits(), 10); !ok {
		t.Fatal("bad coefficient")
	}
	base := big.NewInt(1_000_000_000)
	var limbs []uint32
	for n.Sign() != 0 {
		q, r := new(big.Int), new(big.Int)
		q.QuoRem(n, base, r)
		limbs = append(limbs, uint32(r.Uint64()))
		n = q
	}
	return slowDecimal(&slowCoefficient{limbs: limbs}, d.exponent(), d.negative())
}

func decimalFromParts(t *testing.T, coeff string, exp int, negative bool) Decimal {
	t.Helper()
	s := coeff + "e" + strconv.Itoa(exp)
	if negative {
		s = "-" + s
	}
	d, err := Parse(s)
	if err != nil {
		t.Fatal(err)
	}
	return d
}

func ratFromParts(t *testing.T, coeff string, exp int, negative bool) *big.Rat {
	t.Helper()
	n, ok := new(big.Int).SetString(coeff, 10)
	if !ok {
		t.Fatal("bad oracle coefficient")
	}
	if negative {
		n.Neg(n)
	}
	r := new(big.Rat).SetInt(n)
	pow := new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(absInt(exp))), nil)
	if exp < 0 {
		r.Quo(r, new(big.Rat).SetInt(pow))
	} else {
		r.Mul(r, new(big.Rat).SetInt(pow))
	}
	return r
}

func absInt(x int) int {
	if x < 0 {
		return -x
	}
	return x
}

// TestLimbDigitsMatchesDivisionLoop pins the branch-light limbDigits
// to a division loop, at every power-of-ten boundary, at
// every power of two, over random limbs and across the full uint32 range
// edges.
func TestLimbDigitsMatchesDivisionLoop(t *testing.T) {
	reference := func(limb uint32) uint32 {
		n := uint32(1)
		for limb >= 10 {
			limb /= 10
			n++
		}
		return n
	}
	var inputs []uint32
	for p := uint64(1); p <= math.MaxUint32; p *= 10 {
		inputs = append(inputs, uint32(p-1), uint32(p), uint32(p+1))
	}
	for b := range 32 {
		v := uint32(1) << b
		inputs = append(inputs, v-1, v, v+1)
	}
	inputs = append(inputs, 0, math.MaxUint32, uint32(decimalLimbBase-1), uint32(decimalLimbBase))
	r := rand.New(rand.NewSource(52))
	for range 200000 {
		inputs = append(inputs, r.Uint32()>>uint(r.Intn(32)))
	}
	for _, v := range inputs {
		if got, want := limbDigits(v), reference(v); got != want {
			t.Fatalf("limbDigits(%d) = %d, want %d", v, got, want)
		}
	}
}

// cohortGroups is the representation-freezing cohort matrix: each group holds
// one numeric value built along every construction path (parse variants,
// constructors, arithmetic at the preferred scales, explicit quantize), plus a
// forced slow-band copy of each nonzero member so every group straddles the
// inline/slow representation boundary. Distinct groups are distinct values.
func cohortGroups(t *testing.T) [][]Decimal {
	t.Helper()
	must := func(d Decimal, err error) Decimal {
		t.Helper()
		if err != nil {
			t.Fatal(err)
		}
		return d
	}
	quantized := func(d Decimal, exponent int32) Decimal {
		t.Helper()
		q, _, err := d.Quantize(exponent, TiesToEven)
		if err != nil {
			t.Fatal(err)
		}
		return q
	}
	p := func(s string) Decimal { return MustParse(s) }
	decoded := func(raw string) Decimal {
		t.Helper()
		var d Decimal
		if err := d.UnmarshalJSON([]byte(raw)); err != nil {
			t.Fatal(err)
		}
		return d
	}
	scanned := func(src any) Decimal {
		t.Helper()
		var d Decimal
		if err := d.Scan(src); err != nil {
			t.Fatal(err)
		}
		return d
	}
	bigOne := must(FromBigInt(big.NewInt(1)))
	wide := new(big.Int).Lsh(big.NewInt(1), 128) // 2^128, one past the inline words
	groups := [][]Decimal{
		{p("1"), p("1.0"), p("1.00"), p("1e0"), p("0.1e1"), p("100E-2"), New(1, 0), New(100, -2),
			FromInt64(1), FromUint64(1), NewInt128(0, 1, 0), bigOne, must(FromFloat64(1)), must(FromRat(big.NewRat(3, 3))),
			decoded("1.0"), decoded(`"1.000"`), scanned("1.00"), scanned(int64(1)),
			must(p("0.5").Add(p("0.5"))), must(p("0.25").Mul(p("4"))), must(p("3").Sub(p("2.000"))),
			must(p("3.0").Div(p("3"))), must(p("1.00").Sqrt()), must(p("1.0").Pow(2)),
			quantized(p("1"), -3), quantized(p("1.000"), 0)},
		{p("-2.5"), p("-2.50"), p("-25E-1"), New(-250, -2), must(p("0").Sub(p("2.5"))),
			must(p("-0.5").Mul(p("5"))), quantized(p("-2.5"), -4)},
		{Decimal{}, p("0"), p("0.0"), p("0.00"), p("0E+9"), p("-0"), New(0, 7), FromInt64(0),
			must(p("1.5").Sub(p("1.50"))), must(p("0").Mul(p("-1E+5"))), quantized(p("0.004"), -2)},
		{p("99999999999999999999999999999999999999"), p("999999999999999999999999999999999999990E-1"),
			p("9.9999999999999999999999999999999999999E+37"),
			must(p("99999999999999999999999999999999999998").Add(p("1")))},
		{must(FromBigInt(wide)), p(wide.String()), p(wide.String() + "0E-1"),
			must(p("340282366920938463463374607431768211455").Add(p("1.0")))},
		{p("1.000000000000000000000000000000000000001"), p("10.00000000000000000000000000000000000001E-1")},
		{p("1E+100"), p("1" + strings.Repeat("0", 100)), p("10000E+96"), must(p("1E+50").Mul(p("1.0E+50")))},
		{p("100000E+2147483647"), p("1000000E+2147483646"), p("10000000E+2147483645")},
	}
	for i, group := range groups {
		for _, d := range group[:len(group):len(group)] {
			if !d.IsZero() { // no construction path publishes a slow zero
				groups[i] = append(groups[i], forceSlowBandForTest(t, d))
			}
		}
	}
	return groups
}

// cohortViolations checks the representation-freezing invariants over the
// cohort matrix with the given equality, comparison and hash: every pair in
// a group is equal, compares 0 and hashes identically under one seed, and
// members of different groups are unequal with a consistent nonzero order.
func cohortViolations(groups [][]Decimal, equal func(a, b Decimal) bool, compare func(a, b Decimal) int, hash func(*maphash.Hash, Decimal)) []string {
	seed := maphash.MakeSeed()
	digest := func(d Decimal) uint64 {
		var h maphash.Hash
		h.SetSeed(seed)
		hash(&h, d)
		return h.Sum64()
	}
	var bad []string
	for gi, group := range groups {
		for i, a := range group {
			for j, b := range group {
				if !equal(a, b) || compare(a, b) != 0 || digest(a) != digest(b) {
					bad = append(bad, "group "+strconv.Itoa(gi)+" members "+strconv.Itoa(i)+","+strconv.Itoa(j)+" ("+a.String()+", "+b.String()+")")
				}
			}
		}
		for hi, other := range groups {
			if hi == gi {
				continue
			}
			for _, a := range group {
				for _, b := range other {
					if equal(a, b) || compare(a, b) == 0 || compare(a, b) != -compare(b, a) {
						bad = append(bad, "groups "+strconv.Itoa(gi)+","+strconv.Itoa(hi)+" ("+a.String()+", "+b.String()+")")
					}
				}
			}
		}
	}
	return bad
}

// TestCohortMatrixEquality is the representation-freezing test over the cohort
// matrix, every construction path and both storage bands: every construction
// path of one value, in both storage bands, is pairwise Equal, compares 0 and
// hashes identically, and distinct values stay distinct. The groups are
// hand-derived numeric identities.
func TestCohortMatrixEquality(t *testing.T) {
	groups := cohortGroups(t)
	pairs := 0
	for _, g := range groups {
		pairs += len(g) * len(g)
	}
	if pairs < 400 {
		t.Fatalf("cohort matrix holds %d same-value pairs; want at least 400", pairs)
	}
	for _, equal := range []func(a, b Decimal) bool{Decimal.Equal, Hasher{}.Equal} {
		if bad := cohortViolations(groups, equal, Decimal.Compare, Hasher{}.Hash); len(bad) != 0 {
			t.Fatalf("%d freezing violations, first %s", len(bad), bad[0])
		}
	}
}

// TestHasherMethodSet pins the exact Hasher method set: Hasher{} is
// an empty struct satisfying maphash.Hasher[Decimal] through exactly the
// value-receiver methods Hash(*maphash.Hash, Decimal) and Equal(Decimal,
// Decimal) bool, Equal agrees with Decimal.Equal on hand cohort pairs, and
// no Cmp, unseeded digest or Decimal.Hash alias exists.
func TestHasherMethodSet(t *testing.T) {
	var _ maphash.Hasher[Decimal] = Hasher{}
	typ := reflect.TypeFor[Hasher]()
	if typ.Kind() != reflect.Struct || typ.NumField() != 0 || typ.Size() != 0 {
		t.Fatalf("Hasher is %v with %d fields, size %d; want an empty struct", typ.Kind(), typ.NumField(), typ.Size())
	}
	want := map[string]reflect.Type{
		"Equal": reflect.TypeFor[func(Hasher, Decimal, Decimal) bool](),
		"Hash":  reflect.TypeFor[func(Hasher, *maphash.Hash, Decimal)](),
	}
	for _, set := range []reflect.Type{typ, reflect.PointerTo(typ)} {
		if set.NumMethod() != len(want) {
			t.Fatalf("%v has %d methods, want exactly Equal and Hash", set, set.NumMethod())
		}
	}
	for name, sig := range want {
		m, ok := typ.MethodByName(name)
		if !ok || m.Type != sig {
			t.Fatalf("Hasher.%s = %v (present %v), want %v", name, m.Type, ok, sig)
		}
	}
	// Reflect an actual value: TypeFor[Decimal] triggers Go 1.27.1 linker
	// crashes in a comparable variant of the type.
	var value Decimal
	decimalType := reflect.TypeOf(value)
	for _, name := range []string{"Hash", "Cmp", "Sum64", "Digest", "HashCode", "Fingerprint"} {
		if _, ok := decimalType.MethodByName(name); ok {
			t.Errorf("Decimal exports %s", name)
		}
	}
	for _, tc := range []struct {
		a, b string
		want bool
	}{{"1.0", "1.00", true}, {"0", "0E+9", true}, {"1.0", "1.01", false}, {"-2", "2", false}} {
		a, b := MustParse(tc.a), MustParse(tc.b)
		if got := (Hasher{}).Equal(a, b); got != tc.want || got != a.Equal(b) {
			t.Errorf("Hasher.Equal(%s, %s) = %v, want %v", tc.a, tc.b, got, tc.want)
		}
	}
}

// TestCohortMatrixNegativeControl is the representation-freezing negative control:
// representation-dependent equalities, orders and hashes injected in place
// of the shipped ones must each fail the freezing check, so the check
// detects the invariant breaks it exists to freeze. Four injections each
// break a single leg (within-group Equal, Compare and hash, and the
// cross-group distinctness leg), so every leg is proven necessary.
func TestCohortMatrixNegativeControl(t *testing.T) {
	groups := cohortGroups(t)
	structural := func(a, b Decimal) bool { return reflect.DeepEqual(a, b) }
	structuralCompare := func(a, b Decimal) int {
		if structural(a, b) {
			return 0
		}
		return a.Compare(b) | 1
	}
	bandEqual := func(a, b Decimal) bool { return a.Equal(b) && (a.slow == nil) == (b.slow == nil) }
	bandCompare := func(a, b Decimal) int {
		if c := a.Compare(b); c != 0 || bandEqual(a, b) {
			return c
		}
		if a.slow == nil {
			return -1
		}
		return 1
	}
	textHash := func(h *maphash.Hash, d Decimal) { _, _ = h.WriteString(d.String()) }
	for _, tc := range []struct {
		name    string
		equal   func(a, b Decimal) bool
		compare func(a, b Decimal) int
		hash    func(*maphash.Hash, Decimal)
	}{
		{"structural equality and order", structural, structuralCompare, Hasher{}.Hash},
		{"band-dependent equality", bandEqual, bandCompare, Hasher{}.Hash},
		// Each of the next four breaks exactly one leg of the check, so
		// dropping any leg from cohortViolations fails this test.
		{"structural equality only (within-group Equal leg)", structural, Decimal.Compare, Hasher{}.Hash},
		{"structural order only (within-group Compare leg)", Decimal.Equal, structuralCompare, Hasher{}.Hash},
		{"cohort text hash (within-group hash leg)", Decimal.Equal, Decimal.Compare, textHash},
		{"everything equal (cross-group leg)", func(a, b Decimal) bool { return true }, Decimal.Compare, Hasher{}.Hash},
	} {
		if bad := cohortViolations(groups, tc.equal, tc.compare, tc.hash); len(bad) == 0 {
			t.Errorf("%s passed the freezing check; the check cannot detect it", tc.name)
		}
	}
}

// TestReduceExamples checks the documented Reduce examples: Reduce maps 2.1 to 2.1 (exponent -1), 1.200 to 1.2 (exponent
// -1) and 0.00 to 0 at exponent 0, the hand-derived GDA reduce results, in
// both storage bands, leaving the source cohort unchanged.
func TestReduceExamples(t *testing.T) {
	for _, tc := range []struct {
		in, want string
		exponent int32
	}{{"2.1", "2.1", -1}, {"1.200", "1.2", -1}, {"0.00", "0", 0}, {"-1.200", "-1.2", -1}, {"1200", "1.2E+3", 2}} {
		variants := []Decimal{MustParse(tc.in)}
		if !variants[0].IsZero() { // no construction path publishes a slow zero
			variants = append(variants, forceSlowBandForTest(t, variants[0]))
		}
		for _, d := range variants {
			got := d.Reduce()
			if got.String() != tc.want || got.Exponent() != tc.exponent || d.String() != tc.in {
				t.Errorf("Reduce(%s) = %s at %d (source now %s); want %s at %d", tc.in, got, got.Exponent(), d, tc.want, tc.exponent)
			}
		}
	}
}

// textSeamValue routes Reduce().Text through the checked text seam at a
// chosen address limit. At math.MaxInt it is Decimal.Reduce().Text, since
// Text is exactly d.text(maxBytes, math.MaxInt) (requireTextDelegation).
type textSeamValue struct {
	d            Decimal
	addressLimit uint64
}

func (v textSeamValue) Reduce() textSeamValue { return textSeamValue{v.d.Reduce(), v.addressLimit} }
func (v textSeamValue) Text(maxBytes uint64) (string, error) {
	return v.d.text(maxBytes, v.addressLimit)
}

// mapKeysRecipe is the loop of ExampleDecimal_mapKeys over seam values; its
// range body is required to be token-for-token the example's
// (checkMapKeysRecipe), so the example and this test cannot drift.
func mapKeysRecipe(entries map[string]int, values []textSeamValue) {
	for i, value := range values {
		key, err := value.Reduce().Text(0)
		if err != nil {
			panic(err) // handle refusal before inserting or querying a key
		}
		entries[key] = i
	}
}

// checkMapKeysRecipe requires the first range loop of ExampleDecimal_mapKeys
// in example to have the same key, value and body (comments aside) as the
// loop of mapKeysRecipe in recipe.
func checkMapKeysRecipe(example, recipe []byte) error {
	fset := token.NewFileSet()
	loop := func(src []byte, name string) (string, error) {
		fn, err := funcNode(fset, src, name)
		if err != nil {
			return "", err
		}
		var found *ast.RangeStmt
		ast.Inspect(fn.Body, func(n ast.Node) bool {
			if r, ok := n.(*ast.RangeStmt); ok && found == nil {
				found = r
			}
			return found == nil
		})
		if found == nil {
			return "", fmt.Errorf("%s has no range loop", name)
		}
		var parts []string
		for _, node := range []ast.Node{found.Key, found.Value, found.Body} {
			if node == nil {
				return "", fmt.Errorf("%s loop lacks a key or value", name)
			}
			text, err := nodeText(fset, node)
			if err != nil {
				return "", err
			}
			parts = append(parts, text)
		}
		return strings.Join(parts, "\n"), nil
	}
	want, err := loop(example, "ExampleDecimal_mapKeys")
	if err != nil {
		return err
	}
	got, err := loop(recipe, "mapKeysRecipe")
	if err != nil {
		return err
	}
	if got != want {
		return fmt.Errorf("mapKeysRecipe loop\n%s\ndiffers from ExampleDecimal_mapKeys loop\n%s", got, want)
	}
	return nil
}

// runMapKeysRecipe runs mapKeysRecipe and returns the error its refusal
// branch panics with, if any.
func runMapKeysRecipe(entries map[string]int, values []textSeamValue) (err error) {
	defer func() {
		if r := recover(); r != nil {
			e, ok := r.(error)
			if !ok {
				panic(r)
			}
			err = e
		}
	}()
	mapKeysRecipe(entries, values)
	return nil
}

// TestTextKeyRefusesBeforeMapUse checks that a checked text key refuses
// before map use. It runs the ExampleDecimal_mapKeys
// recipe itself: checkMapKeysRecipe proves mapKeysRecipe's loop is the
// example's, and requireTextDelegation proves the seam at math.MaxInt is
// Text. When v.Reduce().Text(0) reports the checked resource refusal
// (reached through the seam's address limit), the refusal is "" with
// ErrInsufficientStorage identity, the recipe returns through its error
// branch before its only map operation, the map is unchanged, and the
// %!decimal(resource limit) String diagnostic is never a key. The success
// control keys the cohort 1.2300/1.23 and a 45-digit slow value by their
// hand-derived reduced texts, equal to the public Reduce().Text(0).
func TestTextKeyRefusesBeforeMapUse(t *testing.T) {
	requireTextDelegation(t)
	example, err := os.ReadFile("example_test.go")
	if err != nil {
		t.Fatal(err)
	}
	recipe, err := os.ReadFile("equality_test.go")
	if err != nil {
		t.Fatal(err)
	}
	if err := checkMapKeysRecipe(example, recipe); err != nil {
		t.Fatal(err)
	}
	drifted := bytes.Replace(example, []byte("entries[key] = i"), []byte("entries[value.String()] = i"), 1)
	if bytes.Equal(drifted, example) || checkMapKeysRecipe(drifted, recipe) == nil {
		t.Fatal("recipe check accepted a drifted example")
	}

	const digits = "123456789012345678901234567890123456789012345" // 45 digits: slow band
	wide := MustParse(digits + ".000")                             // reduces to 45 bytes of text
	if wide.slow == nil || wide.Reduce().slow == nil || wide.Reduce().exponent() != 0 {
		t.Fatal("reduced value left the slow band; the checked refusal would not be reached")
	}
	values := []Decimal{MustParse("1.2300"), MustParse("1.23"), wide}
	var seam []textSeamValue
	for _, v := range values {
		seam = append(seam, textSeamValue{v, math.MaxInt})
		public, err := v.Reduce().Text(0)
		if got, seamErr := seam[len(seam)-1].Reduce().Text(0); got != public || seamErr != err {
			t.Fatalf("seam at math.MaxInt = %q, %v; public Reduce().Text(0) = %q, %v", got, seamErr, public, err)
		}
	}
	entries := map[string]int{}
	if err := runMapKeysRecipe(entries, seam); err != nil {
		t.Fatalf("recipe at the public limit: %v", err)
	}
	if want := map[string]int{"1.23": 1, digits: 2}; !reflect.DeepEqual(entries, want) {
		t.Fatalf("successful keys = %v, want %v", entries, want)
	}

	refused := textSeamValue{wide, uint64(len(digits)) - 1}
	key, err := refused.Reduce().Text(0)
	if key != "" || !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("reduced text = %q, %v; want \"\" with ErrInsufficientStorage", key, err)
	}
	if diagnostic := diagnoseText(key, err); diagnostic != "%!decimal(resource limit)" || diagnostic == key {
		t.Fatalf("String mapping = %q; the refusal key must not be the diagnostic", diagnostic)
	}
	untouched := map[string]int{"1.23": 1}
	if err := runMapKeysRecipe(untouched, []textSeamValue{refused}); !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("recipe error = %v, want ErrInsufficientStorage", err)
	}
	if want := map[string]int{"1.23": 1}; !reflect.DeepEqual(untouched, want) {
		t.Fatalf("refused key touched the map: %v", untouched)
	}
	if _, ok := untouched["%!decimal(resource limit)"]; ok {
		t.Fatal("diagnostic was substituted as a key")
	}
}

// inlineReduceLoop strips one trailing zero per step: the reference for
// inlineReduce's constant-divisor stages.
func inlineReduceLoop(d Decimal) Decimal {
	w, e := d.words.lo, int64(d.exponent())
	for _, k := range [...]int{16, 8, 4, 2, 1} {
		for e+int64(k) <= math.MaxInt32 && w%pow10Words[k] == 0 {
			w /= pow10Words[k]
			e += int64(k)
		}
	}
	return inlineDecimal(uint128{lo: w}, int32(e), d.negative())
}

// bigReduceOracle strips trailing zeros with big.Int DivMod while the
// exponent stays at most MaxInt32.
func bigReduceOracle(coefficient *big.Int, exponent int64) (*big.Int, int64) {
	c := new(big.Int).Set(coefficient)
	ten := big.NewInt(10)
	q, r := new(big.Int), new(big.Int)
	for exponent < math.MaxInt32 {
		q.DivMod(c, ten, r)
		if r.Sign() != 0 {
			break
		}
		c.Set(q)
		exponent++
	}
	return c, exponent
}

func uint128Big(w uint128) *big.Int {
	x := new(big.Int).Lsh(new(big.Int).SetUint64(w.hi), 64)
	return x.Or(x, new(big.Int).SetUint64(w.lo))
}

// TestInlineReduceMatchesGeneralPath pins the constant-divisor
// inlineReduce and Reduce's two-word last-digit return to the one-digit
// reference loop,
// the general limb path and an independent big.Int DivMod oracle over
// w = d*10^k (k = 0..19), exponents near MaxInt32, random words and
// two-word coefficients. Equal and Hasher must agree with the slow-band
// carrier of the same value. Path counters guard against vacuous passes.
func TestInlineReduceMatchesGeneralPath(t *testing.T) {
	seed := maphash.MakeSeed()
	digest := func(d Decimal) uint64 {
		var h maphash.Hash
		h.SetSeed(seed)
		Hasher{}.Hash(&h, d)
		return h.Sum64()
	}
	exponents := []int32{math.MinInt32, math.MinInt32 + 19, -400, -2, 0, 7, math.MaxInt32 - 1000}
	for e := int32(math.MaxInt32 - 40); ; e++ {
		exponents = append(exponents, e)
		if e == math.MaxInt32 {
			break
		}
	}
	rng := rand.New(rand.NewSource(82))
	var words []uint128
	for _, base := range []uint64{1, 3, 7, 9, 12, 25, 99, 101, 1844, 123456789, 999999999999999999, math.MaxUint64} {
		for k := range 20 {
			if hi, lo := bits.Mul64(base, pow10Words[k]); hi == 0 {
				words = append(words, uint128{lo: lo})
			}
		}
	}
	for range 400 {
		k := rng.Intn(20)
		words = append(words, uint128{lo: rng.Uint64()}, uint128{lo: (rng.Uint64() % (math.MaxUint64 / pow10Words[k])) * pow10Words[k]})
	}
	// Two-word coefficients below 10^38: random, with and without trailing zeros.
	limit := new(big.Int).Exp(big.NewInt(10), big.NewInt(38), nil)
	twoWord := func(x *big.Int) (uint128, bool) {
		if x.Sign() <= 0 || x.Cmp(limit) >= 0 || x.BitLen() <= 64 {
			return uint128{}, false
		}
		return uint128{lo: new(big.Int).And(x, new(big.Int).SetUint64(math.MaxUint64)).Uint64(), hi: new(big.Int).Rsh(x, 64).Uint64()}, true
	}
	for i := range 2000 {
		x := new(big.Int).Rand(rng, limit)
		if i%2 == 1 {
			k := int64(rng.Intn(25))
			x.Div(x, new(big.Int).Exp(big.NewInt(10), big.NewInt(k), nil))
			x.Mul(x, new(big.Int).Exp(big.NewInt(10), big.NewInt(k), nil))
		}
		if w, ok := twoWord(x); ok {
			words = append(words, w)
		}
	}
	for _, s := range []string{"18446744073709551616", "18446744073709551620", "184467440737095516160", "99999999999999999999999999999999999990", "10000000000000000000000000000000000000"} {
		x, _ := new(big.Int).SetString(s, 10)
		if w, ok := twoWord(x); ok {
			words = append(words, w)
		}
	}
	var unchanged, stripped, ceiling, wideReturn, wideDeferred int
	for _, w := range words {
		if w == (uint128{}) {
			continue
		}
		coefficient := uint128Big(w)
		lastDigitZero := new(big.Int).Mod(coefficient, big.NewInt(10)).Sign() == 0
		for _, e := range exponents {
			for _, negative := range []bool{false, true} {
				d := inlineDecimal(w, e, negative)
				got := d.Reduce()
				general := reduceGeneral(d)
				wantC, wantE := bigReduceOracle(coefficient, int64(e))
				if !sameRepresentation(got, general) || got.slow != nil || got.negative() != negative ||
					int64(got.exponent()) != wantE || uint128Big(got.words).Cmp(wantC) != 0 {
					t.Fatalf("Reduce(%v e%d neg=%v) = %+v, general %+v, oracle %s e%d", w, e, negative, got, general, wantC, wantE)
				}
				if w.hi == 0 {
					if loop := inlineReduceLoop(d); !sameRepresentation(inlineReduce(d), loop) {
						t.Fatalf("inlineReduce(%d e%d) = %+v, loop %+v", w.lo, e, inlineReduce(d), loop)
					}
					switch {
					case !lastDigitZero:
						unchanged++
					case new(big.Int).Mod(wantC, big.NewInt(10)).Sign() == 0:
						ceiling++ // the exponent ceiling stopped the stripping
					default:
						stripped++
					}
				} else if !lastDigitZero {
					wideReturn++
				} else {
					wideDeferred++
				}
				slow := asSlowBand(d)
				if !d.Equal(got) || !got.Equal(slow) || digest(d) != digest(got) || digest(d) != digest(slow) {
					t.Fatalf("Equal/Hasher inconsistency for %v e%d neg=%v", w, e, negative)
				}
			}
		}
	}
	t.Logf("one-word unchanged %d, stripped %d, ceiling-limited %d; two-word early return %d, deferred %d", unchanged, stripped, ceiling, wideReturn, wideDeferred)
	if unchanged < 1000 || stripped < 1000 || ceiling < 100 || wideReturn < 1000 || wideDeferred < 1000 {
		t.Fatalf("vacuous path coverage: %d %d %d %d %d", unchanged, stripped, ceiling, wideReturn, wideDeferred)
	}
}

// wordLimbsReference is a per-limb 128-bit division loop, the differential
// reference of wordLimbs.
func wordLimbsReference(hi, lo uint64) ([5]uint32, int) {
	var out [5]uint32
	n := 0
	for ; hi|lo != 0; n++ {
		var rem, digit uint64
		hi, rem = bits.Div64(0, hi, decimalLimbBase)
		lo, digit = bits.Div64(rem, lo, decimalLimbBase)
		out[n] = uint32(digit)
	}
	return out, n
}

// TestWordLimbsMatchesReferenceAndBigOracle pins the constant-divisor
// limb split to the per-limb Div64 loop and to math/big base-10^9 digits
// over boundaries (zero, 10^k±1, 2^64±1, hi near and above 10^18, the
// 128-bit maximum) and random values of every bit length, with a vacuity
// guard that the one-word and both two-word branches served.
func TestWordLimbsMatchesReferenceAndBigOracle(t *testing.T) {
	var cases [][2]uint64
	for _, v := range []uint64{0, 1, 9, 10, 999_999_999, 1_000_000_000, 1_000_000_001,
		999_999_999_999_999_999, 1_000_000_000_000_000_000, 9_999_999_999_999_999_999,
		10_000_000_000_000_000_000, math.MaxUint64 - 1, math.MaxUint64} {
		for _, h := range []uint64{0, 1, 2, 17, 999_999_999, 1_000_000_000, 999_999_999_999_999_999,
			1_000_000_000_000_000_000, 1_000_000_000_000_000_001, 18_000_000_000_000_000_000, math.MaxUint64} {
			cases = append(cases, [2]uint64{h, v})
		}
	}
	// Powers of ten and their neighbours across the whole 128-bit range.
	mask := new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), 64), big.NewInt(1))
	p := big.NewInt(1)
	for range 40 {
		for _, d := range []int64{-1, 0, 1} {
			x := new(big.Int).Add(p, big.NewInt(d))
			if x.Sign() >= 0 && x.BitLen() <= 128 {
				hi := new(big.Int).Rsh(x, 64).Uint64()
				lo := new(big.Int).And(x, mask).Uint64()
				cases = append(cases, [2]uint64{hi, lo})
			}
		}
		p.Mul(p, big.NewInt(10))
	}
	rng := rand.New(rand.NewSource(20261030))
	for range 200_000 {
		width := rng.Intn(129)
		var hi, lo uint64
		switch {
		case width > 64:
			hi, lo = rng.Uint64()>>(128-width), rng.Uint64()
		case width > 0:
			lo = rng.Uint64() >> (64 - width)
		}
		cases = append(cases, [2]uint64{hi, lo})
	}
	var oneWord, twoWordSmall, twoWordLarge int
	base := big.NewInt(1_000_000_000)
	for _, c := range cases {
		hi, lo := c[0], c[1]
		switch {
		case hi == 0:
			oneWord++
		case hi < 1_000_000_000_000_000_000:
			twoWordSmall++
		default:
			twoWordLarge++
		}
		var got [5]uint32
		n := wordLimbs(&got, hi, lo)
		want, wn := wordLimbsReference(hi, lo)
		if n != wn || got != want {
			t.Fatalf("wordLimbs(%#x,%#x) = %v/%d, reference %v/%d", hi, lo, got, n, want, wn)
		}
		x := new(big.Int).Lsh(new(big.Int).SetUint64(hi), 64)
		x.Or(x, new(big.Int).SetUint64(lo))
		for i := range n {
			r := new(big.Int)
			x.QuoRem(x, base, r)
			if uint32(r.Uint64()) != got[i] {
				t.Fatalf("wordLimbs(%#x,%#x) limb %d = %d, oracle %d", hi, lo, i, got[i], r.Uint64())
			}
		}
		if x.Sign() != 0 || (n > 0 && got[n-1] == 0) {
			t.Fatalf("wordLimbs(%#x,%#x) count %d is not the minimal limb count", hi, lo, n)
		}
	}
	if oneWord < 50_000 || twoWordSmall < 50_000 || twoWordLarge < 300 {
		t.Fatalf("vacuous branch coverage: one-word %d, hi<10^18 %d, hi>=10^18 %d", oneWord, twoWordSmall, twoWordLarge)
	}
}

// hashReference writes Hasher.Hash's encoding unbatched: one maphash write
// per header field and per limb.
func hashReference(h *maphash.Hash, value Decimal) {
	if value.isZero() {
		_ = h.WriteByte(0)
		return
	}
	if value.slow == nil && value.words.hi == 0 {
		hashWord(h, inlineReduce(value))
		return
	}
	v := coefficientViewOf(value)
	k := removableZeros(&v, value.exponent())
	q, r := int(k/9), uint32(k%9)
	count := reducedLimbCount(&v, q, r)
	if value.negative() {
		_ = h.WriteByte(2)
	} else {
		_ = h.WriteByte(1)
	}
	var fixed [4]byte
	binary.BigEndian.PutUint32(fixed[:], uint32(int64(value.exponent())+int64(k)))
	_, _ = h.Write(fixed[:])
	var variable [10]byte
	n := binary.PutUvarint(variable[:], uint64(count))
	_, _ = h.Write(variable[:n])
	cursor := newReducedCursor(&v, q, r)
	for range count {
		limb, _ := cursor.next()
		binary.BigEndian.PutUint32(fixed[:], limb)
		_, _ = h.Write(fixed[:])
	}
}

// TestHasherBatchedWritesMatchPerLimbReference pins the buffered
// Hash to the per-limb reference and to the math/big preimage over random
// inline, two-word and slow values (coefficients long enough to flush the
// stack buffer several times, trailing zeros, both signs, exponents at the
// int32 limits), and checks that cohort members and both storage bands
// hash equally. The guard requires the batched path to serve two-word and
// multi-chunk slow values.
func TestHasherBatchedWritesMatchPerLimbReference(t *testing.T) {
	rng := rand.New(rand.NewSource(20261031))
	seed := maphash.MakeSeed()
	sum := func(f func(*maphash.Hash, Decimal), d Decimal) uint64 {
		var h maphash.Hash
		h.SetSeed(seed)
		_, _ = h.WriteString("prefix")
		f(&h, d)
		return h.Sum64()
	}
	hasher := func(h *maphash.Hash, d Decimal) { (Hasher{}).Hash(h, d) }
	var twoWord, slow, multiChunk int
	for i := range 6000 {
		var length int
		switch i % 4 {
		case 0:
			length = 1 + rng.Intn(19)
		case 1:
			length = 20 + rng.Intn(20)
		case 2:
			length = 40 + rng.Intn(80)
		default:
			length = 300 + rng.Intn(700)
		}
		var digits strings.Builder
		digits.WriteByte(byte('1' + rng.Intn(9)))
		for j := 1; j < length; j++ {
			digits.WriteByte(byte('0' + rng.Intn(10)))
		}
		coefficient := digits.String() + strings.Repeat("0", rng.Intn(30))
		exponent := rng.Intn(81) - 40
		switch i % 29 {
		case 0:
			exponent = math.MaxInt32 - rng.Intn(5)
		case 1:
			exponent = math.MinInt32 + rng.Intn(5)
		}
		negative := rng.Intn(2) == 0
		d := decimalFromParts(t, coefficient, exponent, negative)
		switch {
		case d.slow == nil && d.words.hi != 0:
			twoWord++
		case d.slow != nil:
			slow++
			if 15+4*len(d.slow.limbs) > hashChunk {
				multiChunk++
			}
		}
		got := sum(hasher, d)
		if want := sum(hashReference, d); got != want {
			t.Fatalf("batched hash differs from per-limb reference for %s", d)
		}
		reduced, _ := new(big.Int).SetString(coefficient, 10)
		k := int64(len(coefficient) - len(strings.TrimRight(coefficient, "0")))
		k = min(k, int64(math.MaxInt32)-int64(exponent))
		reduced.Quo(reduced, new(big.Int).Exp(big.NewInt(10), big.NewInt(k), nil))
		var oracle maphash.Hash
		oracle.SetSeed(seed)
		_, _ = oracle.WriteString("prefix")
		_, _ = oracle.Write(oracleHashPreimage(t, reduced, int32(int64(exponent)+k), negative))
		if got != oracle.Sum64() {
			t.Fatalf("batched hash differs from the math/big preimage for %s", d)
		}
		if got != sum(hasher, forceSlowBandForTest(t, d)) || got != sum(hasher, d.Reduce()) {
			t.Fatalf("band or cohort hash diverges for %s", d)
		}
		if exponent > math.MinInt32+20 {
			shift := 1 + rng.Intn(19)
			wider := decimalFromParts(t, coefficient+strings.Repeat("0", shift), exponent-shift, negative)
			if got != sum(hasher, wider) {
				t.Fatalf("cohort member %s hashes differently from %s", wider, d)
			}
		}
	}
	if twoWord < 300 || slow < 3000 || multiChunk < 1000 {
		t.Fatalf("vacuous coverage: two-word %d, slow %d, multi-chunk %d", twoWord, slow, multiChunk)
	}
}

// TestCompareEqualMetaMatchesGeneralPath pins the Compare fast path,
// two inline operands with one sign and exponent, to compareGeneral and to
// a math/big order over random and boundary operands, including zeros,
// the one-word and two-word boundaries, limb operands and the int32
// exponent bands. A vacuity guard requires the fast path to serve a
// substantial share of the pairs and the general path the rest.
func TestCompareEqualMetaMatchesGeneralPath(t *testing.T) {
	r := rand.New(rand.NewSource(20261031))
	var fast, general int
	const trials = 100_000
	for range trials {
		base := dispatchBase(r)
		a, ca := dispatchSample(r, base)
		b, cb := dispatchSample(r, base)
		if r.Intn(2) == 0 && b.slow == nil && !b.isZero() {
			// Share a's exponent and, for a nonzero a, its sign.
			b = b.withExponent(a.exponent()).withNegative(a.negative())
			cb.Abs(cb)
			if b.negative() {
				cb.Neg(cb)
			}
		}
		e := min(a.exponent(), b.exponent())
		x := new(big.Int).Mul(ca, new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(a.exponent())-int64(e)), nil))
		y := new(big.Int).Mul(cb, new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(b.exponent())-int64(e)), nil))
		want := x.Cmp(y)
		got := a.Compare(b)
		if got != want || got != a.compareGeneral(b) || a.Equal(b) != (want == 0) {
			t.Fatalf("Compare(%#v, %#v) = %d; general %d, math/big %d", a, b, got, a.compareGeneral(b), want)
		}
		if a.meta == b.meta && a.slow == nil && b.slow == nil {
			fast++
		} else {
			general++
		}
	}
	if fast < trials/4 || general < trials/4 {
		t.Fatalf("vacuous Compare classes: fast %d general %d", fast, general)
	}
	t.Logf("Compare fast %d general %d", fast, general)
}
