// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"bytes"
	"database/sql"
	"database/sql/driver"
	"encoding/binary"
	"errors"
	"io"
	"math"
	"math/big"
	"math/rand/v2"
	"slices"
	"strconv"
	"strings"
	"testing"
)

// twosOracle encodes v as width two's-complement bytes (big-endian), or
// reports that it does not fit, using math/big only.
func twosOracle(v *big.Int, width int) ([]byte, bool) {
	limit := new(big.Int).Lsh(big.NewInt(1), uint(8*width-1))
	if v.Cmp(limit) >= 0 || v.Cmp(new(big.Int).Neg(limit)) < 0 {
		return nil, false
	}
	x := new(big.Int).Set(v)
	if x.Sign() < 0 {
		x.Add(x, new(big.Int).Lsh(big.NewInt(1), uint(8*width)))
	}
	out := make([]byte, width)
	x.FillBytes(out)
	return out, true
}

func reversed(b []byte) []byte {
	out := make([]byte, len(b))
	for i := range b {
		out[len(b)-1-i] = b[i]
	}
	return out
}

func coefficientOracle(t *testing.T, d Decimal) *big.Int {
	t.Helper()
	r := divRat(t, d)
	scaled := new(big.Rat).Mul(r, pow10Rat(-int64(d.Exponent())))
	if !scaled.IsInt() {
		t.Fatalf("%v: coefficient not integral", d)
	}
	return new(big.Int).Set(scaled.Num())
}

// TestInt128CoefficientLanes checks 128-bit coefficient interchange: the
// full Int128 range converts both ways exactly, keeps the exponent, and a
// coefficient outside [−2^127, 2^127−1] reports ok=false.
func TestInt128CoefficientLanes(t *testing.T) {
	rng := rand.New(rand.NewPCG(49, 1))
	cases := []uint128{{0, 0}, {1, 0}, {math.MaxUint64, math.MaxUint64}, {0, 1 << 63}, {math.MaxUint64, 1<<63 - 1}, {math.MaxUint64, 0}}
	for range 2000 {
		cases = append(cases, uint128{rng.Uint64(), rng.Uint64()})
	}
	for _, c := range cases {
		lo, hi := c.lo, int64(c.hi)
		want := new(big.Int).Lsh(big.NewInt(hi), 64)
		want.Add(want, new(big.Int).SetUint64(lo))
		d := NewInt128(hi, lo, -7)
		if got := coefficientOracle(t, d); got.Cmp(want) != 0 || d.Exponent() != -7 {
			t.Fatalf("NewInt128(%d,%d) = %v, want %s", hi, lo, d, want)
		}
		gh, gl, ok := d.CoefficientInt128()
		if !ok || gh != hi || gl != lo {
			t.Fatalf("CoefficientInt128 of %v = (%d,%d,%t), want (%d,%d)", d, gh, gl, ok, hi, lo)
		}
	}
	for _, text := range []string{"170141183460469231731687303715884105728", "-170141183460469231731687303715884105729", "1" + strings.Repeat("0", 60)} {
		if hi, lo, ok := MustParse(text).CoefficientInt128(); ok || hi != 0 || lo != 0 {
			t.Fatalf("%s: (%d,%d,%t), want not-fit", text, hi, lo, ok)
		}
	}
	// Invariant behind the slow-band shortcut: every slow value exceeds 2^127.
	for _, text := range []string{"340282366920938463463374607431768211456", strings.Repeat("9", 45)} {
		d := MustParse(text)
		if d.slow == nil || coefficientOracle(t, d).BitLen() <= 127 {
			t.Fatalf("%s: slow-band invariant broken", text)
		}
	}
}

var coefficientOrders = []struct {
	name   string
	order  binary.ByteOrder
	little bool
}{
	{"big", binary.BigEndian, false},
	{"little", binary.LittleEndian, true},
	{"native", binary.NativeEndian, nativeLittle()},
}

func nativeLittle() bool {
	var probe [2]byte
	binary.NativeEndian.PutUint16(probe[:], 1)
	return probe[0] == 1
}

// TestTwosComplementLanes checks two's-complement coefficient
// interchange: every width 1..32 in both byte orders round-trips the extremes,
// −1, 0, padded encodings and random values against math/big; the exact
// bounds report ErrIntegerRange with dst unchanged.
func TestTwosComplementLanes(t *testing.T) {
	rng := rand.New(rand.NewPCG(49, 2))
	for width := 1; width <= 32; width++ {
		limit := new(big.Int).Lsh(big.NewInt(1), uint(8*width-1))
		values := []*big.Int{new(big.Int).Neg(limit), new(big.Int).Sub(limit, big.NewInt(1)), big.NewInt(-1), big.NewInt(0)}
		for range 40 {
			raw := make([]byte, width)
			for i := range raw {
				raw[i] = byte(rng.Uint32())
			}
			v := new(big.Int).SetBytes(raw)
			values = append(values, v.Sub(v, limit))
		}
		for _, o := range coefficientOrders {
			for _, v := range values {
				enc, _ := twosOracle(v, width)
				if o.little {
					enc = reversed(enc)
				}
				d, err := NewTwosComplement(enc, o.order, -3)
				if err != nil || coefficientOracle(t, d).Cmp(v) != 0 || d.Exponent() != -3 {
					t.Fatalf("w=%d %s decode %x: (%v, %v), want %s", width, o.name, enc, d, err, v)
				}
				prefix := []byte{0xAA}
				out, err := d.AppendTwosComplement(prefix, width, o.order)
				if err != nil || string(out[:1]) != "\xaa" || string(out[1:]) != string(enc) {
					t.Fatalf("w=%d %s encode %s: (%x, %v), want %x", width, o.name, v, out, err, enc)
				}
			}
			for _, v := range []*big.Int{limit, new(big.Int).Sub(new(big.Int).Neg(limit), big.NewInt(1))} {
				d := MustParse(v.String())
				dst := []byte{1, 2}
				out, err := d.AppendTwosComplement(dst, width, o.order)
				var oe *Error
				if !errors.Is(err, ErrIntegerRange) || !errors.As(err, &oe) || oe.Op != "AppendTwosComplement" || len(out) != 2 || out[0] != 1 {
					t.Fatalf("w=%d %s: %s should not fit: (%x, %v)", width, o.name, v, out, err)
				}
			}
		}
	}
	// Padded encodings decode to the same value.
	for _, tc := range []struct {
		enc  []byte
		want int64
	}{
		{[]byte{0xFF, 0xFF, 0x85}, -123}, {[]byte{0xFF, 0x80, 0x00}, -32768}, {[]byte{0x00, 0x00, 0x85}, 133},
		{[]byte{0xFF, 0x7F}, -129}, {append(make([]byte, 30), 1, 0x6E), 366}, {[]byte{0xFF, 0xFF, 0xFF, 0xFF}, -1},
	} {
		d, err := NewTwosComplement(tc.enc, binary.BigEndian, 0)
		if err != nil || coefficientOracle(t, d).Int64() != tc.want {
			t.Fatalf("%x: (%v, %v), want %d", tc.enc, d, err, tc.want)
		}
	}
}

// userOrder is a caller-defined ByteOrder whose methods panic, so a refusal
// test also proves the library never calls them.
type userOrder struct{ binary.ByteOrder }

func (userOrder) Uint16([]byte) uint16     { panic("user ByteOrder called") }
func (userOrder) Uint32([]byte) uint32     { panic("user ByteOrder called") }
func (userOrder) Uint64([]byte) uint64     { panic("user ByteOrder called") }
func (userOrder) PutUint16([]byte, uint16) { panic("user ByteOrder called") }
func (userOrder) PutUint32([]byte, uint32) { panic("user ByteOrder called") }
func (userOrder) PutUint64([]byte, uint64) { panic("user ByteOrder called") }
func (userOrder) String() string           { return "user" }

// TestCoefficientLaneRefusals checks the refusal order: an unknown
// ByteOrder (never called), width < 1, a width beyond the address window,
// and empty input, each with its exact carrier and dst unchanged.
func TestCoefficientLaneRefusals(t *testing.T) {
	check := func(err error, op string, code ErrorCode, condition Conditions) {
		t.Helper()
		var oe *Error
		if !errors.Is(err, code) || !errors.As(err, &oe) || oe.Op != op || oe.Condition != condition {
			t.Fatalf("got %v, want %s %v %v", err, op, code, condition)
		}
	}
	_, err := NewTwosComplement([]byte{1}, userOrder{binary.BigEndian}, 0)
	check(err, "NewTwosComplement", ErrInvalidOperation, InvalidOperation)
	_, err = NewTwosComplement(nil, binary.LittleEndian, 0)
	check(err, "NewTwosComplement", ErrConversionSyntax, ConversionSyntax)
	dst := []byte{9}
	for _, tc := range []struct {
		width int
		order binary.ByteOrder
		code  ErrorCode
		cond  Conditions
	}{
		{0, binary.BigEndian, ErrInvalidOperation, InvalidOperation},
		{4, userOrder{binary.BigEndian}, ErrInvalidOperation, InvalidOperation},
		{math.MaxInt, binary.BigEndian, ErrInsufficientStorage, InsufficientStorage},
	} {
		out, err := One().AppendTwosComplement(dst, tc.width, tc.order)
		check(err, "AppendTwosComplement", tc.code, tc.cond)
		if len(out) != 1 || out[0] != 9 {
			t.Fatalf("dst changed on refusal: %x", out)
		}
	}
	// On 64-bit targets a width whose bit count overflows is beyond every
	// address window; on 32-bit targets MaxInt/8+1 bytes is addressable.
	if strconv.IntSize == 64 {
		out, err := One().AppendTwosComplement(dst, math.MaxInt/8+1, binary.LittleEndian)
		check(err, "AppendTwosComplement", ErrInsufficientStorage, InsufficientStorage)
		if len(out) != 1 {
			t.Fatalf("dst changed on refusal: %x", out)
		}
	}
	// NativeEndian is recognized and equals the host order.
	var probe [2]byte
	binary.NativeEndian.PutUint16(probe[:], 0x0102)
	d, err := NewTwosComplement(probe[:], binary.NativeEndian, 0)
	if err != nil || coefficientOracle(t, d).Int64() != 0x0102 {
		t.Fatalf("native order: (%v, %v)", d, err)
	}
}

// TestParquetDecimalVectors checks the Parquet decimal shapes: INT32
// DECIMAL(9,2), INT64 DECIMAL(18,4) and FIXED_LEN_BYTE_ARRAY(16)
// DECIMAL(38,s) at ±(10^38−1), each followed by the precision check.
func TestParquetDecimalVectors(t *testing.T) {
	if d := New(int64(int32(-123456789)), -2); d.String() != "-1234567.89" || d.CoefficientDigits() > 9 {
		t.Fatalf("INT32 DECIMAL(9,2): %v", d)
	}
	if d := New(int64(999999999999999999), -4); d.String() != "99999999999999.9999" || d.CoefficientDigits() > 18 {
		t.Fatalf("INT64 DECIMAL(18,4): %v", d)
	}
	max38 := new(big.Int).Sub(new(big.Int).Exp(big.NewInt(10), big.NewInt(38), nil), big.NewInt(1))
	for _, v := range []*big.Int{max38, new(big.Int).Neg(max38)} {
		enc, _ := twosOracle(v, 16)
		d, err := NewTwosComplement(enc, binary.BigEndian, -10)
		if err != nil || coefficientOracle(t, d).Cmp(v) != 0 || d.CoefficientDigits() != 38 || d.Exponent() != -10 {
			t.Fatalf("FLBA(16) %s: (%v, %v)", v, d, err)
		}
	}
}

// TestComposeDecomposeConvention checks exact coefficient transfer with
// preserved scale over SQL DECIMAL vectors through SQLDecimal.Decompose
// and *Decimal.Compose, plus Compose's refusals, atomicity, non-aliasing,
// budget boundaries and Decompose into a buffer with len > 0.
func TestComposeDecomposeConvention(t *testing.T) {
	for _, text := range []string{"1.10", "0.00", "-0", "-12345678901234567890123456789012345678E-38", "340282366920938463463374607431768211457E-5", "-" + strings.Repeat("7", 90) + "E+11"} {
		d := MustParse(text)
		form, negative, coefficient, exponent := SQLDecimal{d}.Decompose(make([]byte, 3, 64))
		if form != 0 || exponent != d.Exponent() || negative != (d.Sign() < 0) {
			t.Fatalf("%s: form=%d negative=%t exponent=%d", text, form, negative, exponent)
		}
		want := coefficientOracle(t, d)
		if new(big.Int).SetBytes(coefficient).Cmp(new(big.Int).Abs(want)) != 0 || len(coefficient) > 0 && coefficient[0] == 0 {
			t.Fatalf("%s: magnitude %x not minimal %s", text, coefficient, want)
		}
		var back Decimal
		if err := back.Compose(form, negative, coefficient, exponent); err != nil || back.String() != d.String() || back.Exponent() != d.Exponent() {
			t.Fatalf("%s: Compose -> (%v, %v)", text, back, err)
		}
		if len(coefficient) > 0 {
			coefficient[0] ^= 0xFF
			if back.String() != d.String() {
				t.Fatal("Compose aliased the caller's coefficient")
			}
		}
	}
	original := MustParse("4.2")
	for _, form := range []byte{1, 2, 7} {
		d := original
		err := d.Compose(form, false, []byte{1}, 0)
		var oe *Error
		if !errors.Is(err, ErrConversionSyntax) || !errors.As(err, &oe) || oe.Condition != ConversionSyntax || oe.Op != "Compose" || !d.Equal(original) || d.Exponent() != original.Exponent() {
			t.Fatalf("form %d: (%v, %v)", form, d, err)
		}
	}
	var nilDecimal *Decimal
	if err := nilDecimal.Compose(0, false, []byte{1}, 0); !errors.Is(err, ErrInvalidOperation) {
		t.Fatalf("nil receiver: %v", err)
	}
	// Budget envelope of a padded 3-byte magnitude: n=24 bits.
	u, w, _ := binaryEnvelope(24)
	coefficient := []byte{0, 0, 7}
	for _, tc := range []struct {
		budget Budget
		ok     bool
	}{
		{Budget{MaxInputDigits: u - 1}, false}, {Budget{MaxInputDigits: u}, true},
		{Budget{MaxDigits: u - 1}, false}, {Budget{MaxDigits: u}, true},
		{Budget{MaxWork: w - 1}, false},
		{Budget{MaxWork: w}, true},
	} {
		d := original
		err := d.ComposeWithBudget(0, false, coefficient, 0, tc.budget)
		if tc.ok != (err == nil) || !tc.ok && (!errors.Is(err, ErrInsufficientStorage) || !d.Equal(original)) {
			t.Fatalf("ComposeWithBudget %+v: (%v, %v)", tc.budget, d, err)
		}
		_, err = NewTwosComplementWithBudget([]byte{0xFF, 0xFF, 0x85}, binary.BigEndian, 0, tc.budget)
		if tc.ok != (err == nil) {
			t.Fatalf("NewTwosComplementWithBudget %+v: %v", tc.budget, err)
		}
	}
}

// fakeDecimalDriver is a stdlib-only driver whose rows yield a foreign
// decompose-only value and whose checker records bound argument types.
type fakeDecimalDriver struct{ seen *[]any }

type foreignDecimal struct {
	negative bool
	mag      []byte
	exponent int32
}

func (f foreignDecimal) Decompose(buf []byte) (byte, bool, []byte, int32) {
	return 0, f.negative, append(buf[:0], f.mag...), f.exponent
}

func (d fakeDecimalDriver) Open(string) (driver.Conn, error) { return fakeConn(d), nil }

type fakeConn fakeDecimalDriver

func (c fakeConn) Prepare(string) (driver.Stmt, error) { return fakeStmt(c), nil }
func (c fakeConn) Close() error                        { return nil }
func (c fakeConn) Begin() (driver.Tx, error)           { return nil, errors.New("no tx") }

type fakeStmt fakeConn

func (s fakeStmt) Close() error  { return nil }
func (s fakeStmt) NumInput() int { return -1 }
func (s fakeStmt) Exec(args []driver.Value) (driver.Result, error) {
	for _, a := range args {
		*s.seen = append(*s.seen, a)
	}
	return driver.RowsAffected(0), nil
}
func (s fakeStmt) Query([]driver.Value) (driver.Rows, error) { return &fakeRows{}, nil }

type fakeRows struct{ done bool }

func (r *fakeRows) Columns() []string { return []string{"v"} }
func (r *fakeRows) Close() error      { return nil }
func (r *fakeRows) Next(dest []driver.Value) error {
	if r.done {
		return io.EOF
	}
	r.done = true
	dest[0] = foreignDecimal{negative: true, mag: []byte{0x01, 0x2C}, exponent: -2} // -3.00
	return nil
}

// TestDatabaseSQLDecimalBinding checks binding through database/sql's
// real converters: a bare Decimal binds as canonical text (Valuer), the
// SQLDecimal adapter binds through the decompose convention, and Scan from
// a foreign decompose-only value reaches *Decimal.Compose exactly.
func TestDatabaseSQLDecimalBinding(t *testing.T) {
	var seen []any
	sql.Register("decimal-fake-coefficient", fakeDecimalDriver{seen: &seen})
	db, err := sql.Open("decimal-fake-coefficient", "")
	if err != nil {
		t.Fatal(err)
	}
	defer db.Close()
	d := MustParse("1.10")
	if _, err := db.Exec("x", d, &d, SQLDecimal{d}); err != nil {
		t.Fatal(err)
	}
	if len(seen) != 3 || seen[0] != "1.10" || seen[1] != "1.10" {
		t.Fatalf("bare Decimal must bind as text: %#v", seen)
	}
	if _, ok := seen[2].(SQLDecimal); !ok {
		t.Fatalf("SQLDecimal must reach the driver through the decompose convention: %#v", seen[2])
	}
	var scanned Decimal
	if err := db.QueryRow("y").Scan(&scanned); err != nil || scanned.String() != "-3.00" || scanned.Exponent() != -2 {
		t.Fatalf("Scan via Compose: (%v, %v)", scanned, err)
	}
}

var coefficientSink []byte

// TestCoefficientLanesDoNotAllocate checks that coefficient interchange does
// not allocate on the inline band.
func TestCoefficientLanesDoNotAllocate(t *testing.T) {
	d := MustParse("-12345678901234567890123456789012345678E-38")
	enc := make([]byte, 16)
	buf := make([]byte, 0, 32)
	for name, f := range map[string]func(){
		"NewInt128":         func() { _ = NewInt128(-5, 7, -2) },
		"CoefficientInt128": func() { _, _, _ = d.CoefficientInt128() },
		"decode16":          func() { _, _ = NewTwosComplement(enc, binary.LittleEndian, -2) },
		"decode32-padded":   func() { _, _ = NewTwosComplement(make32, binary.BigEndian, -2) },
		"encode16":          func() { coefficientSink, _ = d.AppendTwosComplement(buf[:0], 16, binary.BigEndian) },
		"encode32":          func() { coefficientSink, _ = d.AppendTwosComplement(buf[:0], 32, binary.LittleEndian) },
		"decompose":         func() { _, _, coefficientSink, _ = SQLDecimal{d}.Decompose(buf[:0]) },
	} {
		if allocs := testing.AllocsPerRun(50, f); allocs != 0 {
			t.Errorf("%s: %g allocations", name, allocs)
		}
	}
}

var make32 = append(make([]byte, 30), 0x00, 0x6E)

// TestTwosComplementInlinePathMatchesGeneral pins the 128-bit decoder for at
// most 16 bytes to the general Horner conversion (a fast path never owns
// semantics) over random and boundary inputs, signed and unsigned, in both
// byte orders. The unbudgeted call skips planning and stripping; an unlimited
// budget takes the planned path, which strips padding first.
func TestTwosComplementInlinePathMatchesGeneral(t *testing.T) {
	rng := rand.New(rand.NewPCG(49, 3))
	planned := Budget{MaxInputDigits: math.MaxUint64, MaxDigits: math.MaxUint64, MaxWork: math.MaxUint64}
	var stripped, wide int
	for sample := range 20000 {
		n := 1 + rng.IntN(16)
		b := make([]byte, n)
		for i := range b {
			b[i] = byte(rng.Uint32())
		}
		switch rng.IntN(8) {
		case 0: // sign padding of a random length
			pad := []byte{0x00, 0xFF}[rng.IntN(2)]
			for i := range rng.IntN(n + 1) {
				b[i] = pad
			}
		case 1:
			b[0] = []byte{0x00, 0xFF, 0x80, 0x7F}[rng.IntN(4)]
		case 2: // the extreme of the width
			clear(b)
			b[0] = 0x80
		}
		if sample < 64 {
			n = 1 + sample/4
			b = bytes.Repeat([]byte{[]byte{0x00, 0xFF, 0x80, 0x7F}[sample%4]}, n)
		}
		reversed := slices.Clone(b)
		slices.Reverse(reversed)
		for _, signed := range []bool{true, false} {
			// The flag is the sign of a magnitude; two's complement ignores it.
			flag := sample%2 != 0
			negative := b[0]&0x80 != 0
			if !signed {
				negative = flag
			}
			general := binaryHorner(binaryReader{b: b}, 0, signed && negative, negative, 3)
			for _, little := range []bool{false, true} {
				in := b
				if little {
					in = reversed
				}
				for _, budget := range []Budget{{}, planned} {
					got, err := fromBinary(in, little, signed, flag, 3, budget, "t")
					if err != nil {
						t.Fatal(err)
					}
					if !got.Equal(general) || got.Exponent() != general.Exponent() || got.slow != nil || !got.validRepresentation() {
						t.Fatalf("%x signed=%t little=%t flag=%t budget=%+v: %#v, general %v", in, signed, little, flag, budget, got, general)
					}
				}
			}
		}
		if n >= 8 {
			wide++
		}
		if b[0] == 0x00 || b[0] == 0xFF {
			stripped++
		}
	}
	if stripped < 1000 || wide < 1000 || wide > 19000 {
		t.Fatalf("vacuous path coverage: padded %d, at least 8 bytes %d", stripped, wide)
	}
}

// TestTwosComplementDigitBoundOverflow checks that the optional digit pre-check
// of AppendTwosComplement does not wrap for huge widths, where a wrapped
// bound would refuse fitting values with ErrIntegerRange; beyond uint64 it
// yields no bound and the exact check decides.
func TestTwosComplementDigitBoundOverflow(t *testing.T) {
	// On 64-bit targets MaxInt/40138 ≈ 2.3e14 bytes: 8w·30103 overflows
	// uint64 there, so the bound must be absent, never wrapped small.
	huge := math.MaxInt / 40138
	if bound, ok := twosComplementDigitBound(huge); ok && bound < uint64(huge)*2 {
		t.Fatalf("bound(%d) = %d: wrapped", huge, bound)
	}
	if strconv.IntSize == 64 {
		if _, ok := twosComplementDigitBound(math.MaxInt); ok {
			t.Fatal("bound for MaxInt should overflow")
		}
	}
	for w := 1; w <= 64; w++ {
		bound, ok := twosComplementDigitBound(w)
		limit := new(big.Int).Lsh(big.NewInt(1), uint(8*w-1))
		if !ok || uint64(len(limit.String())) > bound {
			t.Fatalf("width %d: bound %d below the digits of 2^(8w-1)", w, bound)
		}
	}
}

// TestLimbsToBytesMatchesBigInt pins the slow-band binary conversion used by
// AppendTwosComplement and Decompose against math/big.
func TestLimbsToBytesMatchesBigInt(t *testing.T) {
	rng := rand.New(rand.NewPCG(49, 4))
	for range 2000 {
		var b strings.Builder
		b.WriteByte(byte('1' + rng.IntN(9)))
		for range 38 + rng.IntN(200) {
			b.WriteByte(byte('0' + rng.IntN(10)))
		}
		d := MustParse(b.String())
		v := coefficientViewOf(d)
		little := limbsToBytes(nil, &v)
		want, _ := new(big.Int).SetString(b.String(), 10)
		if new(big.Int).SetBytes(reversed(little)).Cmp(want) != 0 {
			t.Fatalf("%s: limbsToBytes mismatch", b.String())
		}
	}
}

// magnitudeWithBytes returns an inline Decimal whose coefficient has an
// n-byte minimal magnitude (1 <= n <= 16): top byte 0x9c, low byte 0x01.
func magnitudeWithBytes(n int) Decimal {
	var be [16]byte
	be[16-n] = 0x9c
	be[15] |= 0x01
	return inlineDecimal(uint128{lo: binary.BigEndian.Uint64(be[8:]), hi: binary.BigEndian.Uint64(be[:8])}, -2, n%2 == 1)
}

// totalAllocOver reports runtime TotalAlloc growth over count calls of f:
// the least of three readings taken with the collector off, since TotalAlloc
// is process-wide and another goroutine's allocation can only add to a
// reading.
func totalAllocOver(count int, f func()) uint64 {
	return allocatedBytes(func() {
		for range count {
			f()
		}
	})
}

// TestDecomposeAllocatesExactBytes checks that Decompose(nil) of
// a coefficient with an n-byte magnitude (n = 1..16) returns a slice with
// cap == len == n from one allocation, and its TotalAlloc over many calls
// equals that of make([]byte, n) measured in the same test (within one
// 16-byte tiny-allocator block of start-up slack).
func TestDecomposeAllocatesExactBytes(t *testing.T) {
	const calls = 4096
	for n := 1; n <= 16; n++ {
		v := SQLDecimal{magnitudeWithBytes(n)}
		_, _, coefficient, _ := v.Decompose(nil)
		if len(coefficient) != n || cap(coefficient) != n {
			t.Errorf("Decompose(nil) of a %d-byte magnitude: len %d cap %d, want %d %d", n, len(coefficient), cap(coefficient), n, n)
		}
		if allocs := testing.AllocsPerRun(100, func() { _, _, coefficientSink, _ = v.Decompose(nil) }); allocs != 1 {
			t.Errorf("Decompose(nil) of a %d-byte magnitude: %v allocations, want 1", n, allocs)
		}
		got := totalAllocOver(calls, func() { _, _, coefficientSink, _ = v.Decompose(nil) })
		want := totalAllocOver(calls, func() { coefficientSink = make([]byte, n) })
		if got > want+16 || want > got+16 {
			t.Errorf("Decompose(nil) of a %d-byte magnitude: TotalAlloc %d over %d calls, make([]byte, %d) %d", n, got, calls, n, want)
		}
	}
}

// TestAppendMagnitudeMatchesBigInt pins the exact-capacity
// appendMagnitude to big.Int.Bytes over boundary, random and slow
// coefficients (including slow carriers of small values and magnitudes
// beyond the 64-byte scratch), with dst nil, short with a prefix, and
// exactly sized (the result then aliases dst, and a slow magnitude within
// the stack scratch allocates nothing, a larger one only its exact scratch). Path counters guard against vacuous
// passes.
func TestAppendMagnitudeMatchesBigInt(t *testing.T) {
	pow := func(base, exp int64) *big.Int { return new(big.Int).Exp(big.NewInt(base), big.NewInt(exp), nil) }
	minus1 := func(x *big.Int) *big.Int { return new(big.Int).Sub(x, big.NewInt(1)) }
	values := []*big.Int{big.NewInt(0), big.NewInt(1), big.NewInt(255), big.NewInt(256), minus1(pow(2, 64)), pow(2, 64),
		minus1(pow(2, 128)), pow(2, 128), pow(10, 38), pow(10, 40), minus1(pow(10, 154)), pow(10, 155), pow(10, 200), minus1(pow(2, 4096))}
	rng := rand.New(rand.NewPCG(83, 83))
	for i := range 600 {
		bitsLen := 1 + rng.IntN(1200)
		if i%2 == 0 {
			bitsLen = 1 + rng.IntN(128)
		}
		x := new(big.Int)
		for range (bitsLen + 63) / 64 {
			x.Lsh(x, 64).Or(x, new(big.Int).SetUint64(rng.Uint64()))
		}
		values = append(values, x.Rsh(x, uint(x.BitLen()-min(x.BitLen(), bitsLen))))
	}
	var inline, slowScratch, slowHeap, zeroAllocChecks, oneAllocChecks int
	for _, x := range values {
		want := x.Bytes()
		d := MustParse(x.String())
		carriers := []Decimal{d}
		if d.slow == nil && !d.isZero() {
			carriers = append(carriers, asSlowBand(d))
		}
		for _, c := range carriers {
			switch {
			case c.slow == nil:
				inline++
			case len(want) <= 64:
				slowScratch++
			default:
				slowHeap++
			}
			got := appendMagnitude(nil, c)
			if !bytes.Equal(got, want) || cap(got) != len(want) {
				t.Fatalf("appendMagnitude(nil, %s) = %x (cap %d), want %x", x, got, cap(got), want)
			}
			prefix := []byte{0xaa, 0xbb}
			got = appendMagnitude(prefix, c)
			if !bytes.Equal(got, append([]byte{0xaa, 0xbb}, want...)) || (len(want) > 0 && cap(got) != len(got)) {
				t.Fatalf("appendMagnitude(short, %s) = %x (cap %d)", x, got, cap(got))
			}
			buf := make([]byte, 1, 1+len(want))
			got = appendMagnitude(buf, c)
			if !bytes.Equal(got[1:], want) || len(got) != 1+len(want) || &got[0] != &buf[0] {
				t.Fatalf("appendMagnitude(exact, %s) = %x, want %x aliasing dst", x, got[1:], want)
			}
			// A slow magnitude of at most 56 bytes (15 limbs) converts in the
			// 64-byte stack scratch: into an exactly sized dst it allocates
			// nothing (the scratch bound is never too small to hold it).
			if c.slow != nil && len(want) <= 56 && slowScratch%8 == 0 {
				if allocs := testing.AllocsPerRun(10, func() { coefficientSink = appendMagnitude(buf[:1], c) }); allocs != 0 {
					t.Fatalf("appendMagnitude(exact, slow %s): %v allocations, want 0", x, allocs)
				}
				zeroAllocChecks++
			}
			// A larger slow magnitude needs one heap scratch of the exact
			// bound and no growth beyond it.
			if c.slow != nil && len(want) > 64 && slowHeap%4 == 0 {
				sized := make([]byte, 1, 1+len(want))
				if allocs := testing.AllocsPerRun(10, func() { coefficientSink = appendMagnitude(sized[:1], c) }); allocs != 1 {
					t.Fatalf("appendMagnitude(exact, slow %s): %v allocations, want 1", x, allocs)
				}
				oneAllocChecks++
			}
		}
	}
	t.Logf("inline %d, slow scratch %d, slow heap %d", inline, slowScratch, slowHeap)
	if zeroAllocChecks < 20 || oneAllocChecks < 20 {
		t.Fatalf("vacuous allocation coverage: %d zero- and %d one-allocation checks", zeroAllocChecks, oneAllocChecks)
	}
	if inline < 100 || slowScratch < 100 || slowHeap < 100 {
		t.Fatalf("vacuous path coverage: inline %d, slow scratch %d, slow heap %d", inline, slowScratch, slowHeap)
	}
}

// TestComposeInlineMatchesGeneral pins Compose's path for at most 16 bytes,
// and the shared converter's (ComposeWithBudget without a budget), to
// math/big and to the planned general conversion, which an unlimited budget
// selects: every byte width across the inline boundary, padded magnitudes,
// both signs and the extreme exponents.
func TestComposeInlineMatchesGeneral(t *testing.T) {
	rng := rand.New(rand.NewPCG(0x53514c, 1))
	planned := Budget{MaxInputDigits: math.MaxUint64, MaxDigits: math.MaxUint64, MaxWork: math.MaxUint64}
	original := MustParse("12345678901234567890123456789012345678901234567890.00")
	exponents := []int32{math.MinInt32, -7, 0, math.MaxInt32}
	for width := 0; width <= 32; width++ {
		for sample := range 64 {
			coefficient := make([]byte, width)
			for i := range coefficient {
				if sample > 1 {
					coefficient[i] = byte(rng.Uint32())
				}
				if sample == 2 || sample == 3 {
					coefficient[i] = 0xff
				}
			}
			if width > 0 && sample%4 == 0 {
				coefficient[0] = 0 // non-minimal magnitudes remain valid
			}
			want := new(big.Int).SetBytes(coefficient)
			negative := sample%2 != 0
			exponent := exponents[(sample/2)%len(exponents)]
			got, shared, general := original, original, original
			if err := got.Compose(0, negative, coefficient, exponent); err != nil {
				t.Fatal(err)
			}
			if err := shared.ComposeWithBudget(0, negative, coefficient, exponent, Budget{}); err != nil {
				t.Fatal(err)
			}
			if err := general.ComposeWithBudget(0, negative, coefficient, exponent, planned); err != nil {
				t.Fatal(err)
			}
			for _, d := range []Decimal{got, shared} {
				if !d.Equal(general) || d.Exponent() != general.Exponent() || (d.slow == nil) != (general.slow == nil) ||
					d.coefficientDigits() != want.String() || d.negative() != (negative && want.Sign() != 0) ||
					d.Exponent() != exponent || !d.validRepresentation() {
					t.Fatalf("width %d sample %d: Compose(%x, %t, %d) = %#v, general %#v, coefficient %s", width, sample, coefficient, negative, exponent, d, general, want)
				}
			}
			if width > 0 {
				coefficient[width-1] ^= 0xff
				if got.coefficientDigits() != want.String() {
					t.Fatal("Compose retained its input")
				}
			}
		}
	}
	for width := 0; width <= 17; width++ {
		coefficient := bytes.Repeat([]byte{0xff}, width)
		for _, form := range []byte{0, 1, 2, 255} {
			var nilReceiver *Decimal
			var detail *Error
			if err := nilReceiver.Compose(form, true, coefficient, math.MinInt32); !errors.Is(err, ErrInvalidOperation) || !errors.As(err, &detail) || detail.Op != "Compose" {
				t.Fatalf("nil receiver, form %d width %d: %v", form, width, err)
			}
			if form != 0 {
				got := original
				err := got.Compose(form, true, coefficient, math.MaxInt32)
				if !errors.Is(err, ErrConversionSyntax) || !errors.As(err, &detail) || detail.Op != "Compose" || detail.Condition != ConversionSyntax ||
					!got.Equal(original) || got.Exponent() != original.Exponent() {
					t.Fatalf("form %d width %d: (%v, %v)", form, width, got, err)
				}
			}
		}
	}
}

// TestAppendTwosComplementInlineMatchesBigInt pins the two-word encoder of
// an inline coefficient to math/big: every width from 1 to 40 bytes in both
// byte orders, coefficients on each side of the width's range and at the
// 64- and 128-bit boundaries, the range refusal and an untouched prefix.
func TestAppendTwosComplementInlineMatchesBigInt(t *testing.T) {
	rng := rand.New(rand.NewPCG(0x7477, 5))
	one := big.NewInt(1)
	inlineLimit := new(big.Int).Lsh(one, 128)
	var fits, refused int
	for width := 1; width <= 40; width++ {
		edge := new(big.Int).Lsh(one, uint(8*width-1))
		values := []*big.Int{new(big.Int)}
		for _, base := range []*big.Int{edge, new(big.Int).Lsh(one, 63), new(big.Int).Lsh(one, 64), new(big.Int).Lsh(one, 127), inlineLimit} {
			for delta := int64(-2); delta <= 2; delta++ {
				v := new(big.Int).Add(base, big.NewInt(delta))
				values = append(values, v, new(big.Int).Neg(v))
			}
		}
		for range 200 {
			v := new(big.Int).SetUint64(rng.Uint64())
			v.Lsh(v, 64).Or(v, new(big.Int).SetUint64(rng.Uint64()))
			v.Rsh(v, uint(rng.IntN(128)))
			if rng.IntN(2) == 0 {
				v.Neg(v)
			}
			values = append(values, v)
		}
		for _, v := range values {
			if new(big.Int).Abs(v).Cmp(inlineLimit) >= 0 {
				continue
			}
			d, err := FromBigInt(v)
			if err != nil || d.slow != nil {
				t.Fatalf("FromBigInt(%s): %v, slow %t", v, err, d.slow != nil)
			}
			want, ok := twosOracle(v, width)
			for _, order := range []binary.ByteOrder{binary.BigEndian, binary.LittleEndian} {
				out, err := d.withExponent(-3).AppendTwosComplement([]byte{0xA5, 0x5A}, width, order)
				if !ok {
					var detail *Error
					if !errors.Is(err, ErrIntegerRange) || !errors.As(err, &detail) || detail.Op != "AppendTwosComplement" || !bytes.Equal(out, []byte{0xA5, 0x5A}) {
						t.Fatalf("%s at %d bytes: (%x, %v), want the range refusal", v, width, out, err)
					}
					refused++
					continue
				}
				expected := slices.Clone(want)
				if order == binary.LittleEndian {
					slices.Reverse(expected)
				}
				if err != nil || !bytes.Equal(out, append([]byte{0xA5, 0x5A}, expected...)) {
					t.Fatalf("%s at %d bytes %v: (%x, %v), math/big %x", v, width, order, out, err, expected)
				}
				fits++
			}
		}
	}
	if fits < 5000 || refused < 1000 {
		t.Fatalf("vacuous path coverage: %d encoded, %d refused", fits, refused)
	}
}

// TestInlineConversionsDoNotAllocate checks that the one-word conversion
// paths allocate nothing beyond a result the caller did not supply.
func TestInlineConversionsDoNotAllocate(t *testing.T) {
	whole := big.NewRat(100, 1)
	money := big.NewRat(123457, 100)
	third := big.NewRat(1, 3)
	integer := big.NewInt(1234567890123456789)
	d := New(1234567, -2)
	z := new(big.Int)
	zr := new(big.Rat)
	dst := make([]byte, 0, 64)
	for name, f := range map[string]func(){
		"FromRat(integer)":         func() { _, _ = FromRat(whole) },
		"FromRat(money)":           func() { _, _ = FromRat(money) },
		"FromRatToExponent(1/3)":   func() { _, _, _ = FromRatToExponent(third, -2, TiesToEven) },
		"FromBigInt":               func() { _, _ = FromBigInt(integer) },
		"BigInt(reused)":           func() { _, _ = New(42, 0).BigInt(z) },
		"Rat(reused)":              func() { _, _ = d.Rat(zr) },
		"Float64":                  func() { _, _ = d.Float64() },
		"CompareFloat64":           func() { _, _ = d.CompareFloat64(12345.67) },
		"FromFloat64(integer)":     func() { _, _ = FromFloat64(100) },
		"FromFloat64ToExponent":    func() { _, _, _ = FromFloat64ToExponent(12345.678, -2, TiesToEven) },
		"ParseToExponent":          func() { _, _, _ = ParseToExponent("12345.678", -2, TiesToEven) },
		"ParseWithContext":         func() { _, _, _ = ParseWithContext("12345.678", Decimal128Context()) },
		"AppendTwosComplement(16)": func() { _, _ = d.AppendTwosComplement(dst[:0], 16, binary.LittleEndian) },
		"AppendScientific":         func() { _, _ = d.AppendScientific(dst[:0], 3, DisplayOptions{}) },
	} {
		if n := testing.AllocsPerRun(100, f); n != 0 {
			t.Errorf("%s: %v allocations", name, n)
		}
	}
	if n := testing.AllocsPerRun(100, func() { _, _ = d.Scientific(3) }); n != 1 {
		t.Errorf("Scientific: %v allocations, want the returned string only", n)
	}
}

// TestBinaryInterchangeKernelsMatchBigInt pins both directions of the
// binary conversion of a long coefficient to math/big: the four-bytes-per-
// pass ingress at every length residue, signed and unsigned in both byte
// orders, and the two-limbs-per-pass egress at odd and even limb counts on
// the stack and on the heap, over random values and the carries at word,
// limb and power-of-ten boundaries.
func TestBinaryInterchangeKernelsMatchBigInt(t *testing.T) {
	rng := rand.New(rand.NewPCG(0x62696e, 9))
	one := big.NewInt(1)
	var ingress, negative, stack, heap int
	for length := 17; length <= 700; length += 1 + length/40 {
		for sample := range 12 {
			b := make([]byte, length)
			for i := range b {
				b[i] = byte(rng.Uint32())
			}
			switch sample {
			case 0:
				b = bytes.Repeat([]byte{0xFF}, length)
			case 1:
				clear(b)
				b[0] = 0x80
			case 2:
				b = bytes.Repeat([]byte{0xFF}, length)
				b[0] = 0x7F
			case 3:
				clear(b)
				b[0], b[length-1] = 0x01, 0x01
			}
			unsigned := new(big.Int).SetBytes(b)
			signed := new(big.Int).Set(unsigned)
			if b[0]&0x80 != 0 {
				signed.Sub(signed, new(big.Int).Lsh(one, uint(8*length)))
				negative++
			}
			little := slices.Clone(b)
			slices.Reverse(little)
			for _, order := range []struct {
				little bool
				in     []byte
			}{{false, b}, {true, little}} {
				for _, c := range []struct {
					signed bool
					want   *big.Int
				}{{true, signed}, {false, unsigned}} {
					got, err := fromBinary(order.in, order.little, c.signed, false, -4, Budget{}, "t")
					if err != nil || got.coefficientDigits() != new(big.Int).Abs(c.want).String() || got.negative() != (c.want.Sign() < 0) || got.exponent() != -4 || !got.validRepresentation() {
						t.Fatalf("%d bytes (sample %d, little %t, signed %t): %v, %v; math/big %s", length, sample, order.little, c.signed, got, err, c.want)
					}
					ingress++
				}
			}
		}
	}
	for digits := 39; digits <= 1500; digits += 1 + digits/30 {
		values := []*big.Int{
			randomDigits(rng, digits),
			new(big.Int).Sub(pow10Big(int64(digits)), one), // all nines
			pow10Big(int64(digits - 1)),
		}
		for _, shift := range []uint{64, 128, 192, 640, 2048, 4096} {
			for delta := int64(-1); delta <= 1; delta++ {
				if v := new(big.Int).Lsh(one, shift); len(v.String()) >= 39 {
					values = append(values, v.Add(v, big.NewInt(delta)))
				}
			}
		}
		for _, want := range values {
			d, err := FromBigInt(want)
			if err != nil {
				t.Fatalf("FromBigInt(%s): %v", want, err)
			}
			if d.slow == nil {
				continue // below 2^128: no limbs to convert
			}
			v := coefficientViewOf(d)
			got := limbsToBytes(nil, &v)
			if new(big.Int).SetBytes(reversed(got)).Cmp(want) != 0 || len(got) != (want.BitLen()+7)/8 {
				t.Fatalf("limbsToBytes(%s) = %x", want, got)
			}
			if limbWords(v.count) > 32 {
				heap++
			} else {
				stack++
			}
		}
	}
	if ingress < 3000 || negative < 500 || stack < 300 || heap < 300 {
		t.Fatalf("vacuous path coverage: %d decoded, %d negative, %d on the stack, %d on the heap", ingress, negative, stack, heap)
	}
}

// TestLimbWordsDoesNotWrap checks the word count of a limb coefficient
// against 64-bit arithmetic up to the largest count a 32-bit target can
// hold, where the product 30·count would wrap an int.
func TestLimbWordsDoesNotWrap(t *testing.T) {
	counts := []int{0, 1, 2, 31, 32, 33, 63, 64, 65, 68, 69, 71_582_788, 71_582_789, 71_582_790, math.MaxInt32 / 4}
	rng := rand.New(rand.NewPCG(0x77, 2))
	for range 2000 {
		counts = append(counts, rng.IntN(math.MaxInt32/4))
	}
	for _, count := range counts {
		if want := (uint64(count)*30 + 63) / 64; uint64(limbWords(count)) != want || limbWords(count) < 0 {
			t.Fatalf("limbWords(%d) = %d, want %d", count, limbWords(count), want)
		}
	}
}
