// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"context"
	"database/sql"
	"database/sql/driver"
	"errors"
	"fmt"
	"io"
	"math"
	"math/big"
	"math/bits"
	"math/rand/v2"
	"os"
	"os/exec"
	"runtime"
	"strconv"
	"strings"
	"sync"
	"testing"
	"time"
)

// echoDriver is a stdlib-only database/sql driver whose single query
// returns its bound arguments as one row. The DSN selects the parameter
// and result routes:
//   - "default": a NamedValueChecker that accepts decompose values and
//     returns ErrSkip otherwise, so ordinary arguments pass through the
//     default converter and Value;
//   - "raw": a checker that accepts any value unchanged, so a test can
//     deliver any result kind, including driver-specific types;
//   - "columns": like "default", but its rows implement Go 1.27's
//     RowsColumnScanner and assign through sql.ConvertAssign;
//   - "direct": RowsColumnScanner rows that call the destination's Scan
//     directly with the raw value.
type echoDriver struct{}

var registerEcho = sync.OnceFunc(func() { sql.Register("decimal-echo", echoDriver{}) })

func (echoDriver) Open(dsn string) (driver.Conn, error) { return echoConn{mode: dsn}, nil }

type echoConn struct{ mode string }

func (c echoConn) Prepare(string) (driver.Stmt, error) { return echoStmt(c), nil }
func (c echoConn) Close() error                        { return nil }
func (c echoConn) Begin() (driver.Tx, error)           { return nil, errors.New("no tx") }
func (c echoConn) CheckNamedValue(nv *driver.NamedValue) error {
	if c.mode == "raw" || c.mode == "raw-direct" {
		return nil
	}
	if _, ok := nv.Value.(decimalDecomposer); ok {
		return nil
	}
	return driver.ErrSkip
}

type echoStmt echoConn

func (s echoStmt) Close() error  { return nil }
func (s echoStmt) NumInput() int { return -1 }
func (s echoStmt) Exec([]driver.Value) (driver.Result, error) {
	return driver.RowsAffected(0), nil
}
func (s echoStmt) Query(args []driver.Value) (driver.Rows, error) {
	rows := &echoRows{values: args}
	switch s.mode {
	case "columns", "direct", "raw-direct":
		return &echoColumnRows{echoRows: rows, direct: s.mode != "columns"}, nil
	}
	return rows, nil
}

type echoRows struct {
	values []driver.Value
	done   bool
}

func (r *echoRows) Columns() []string {
	names := make([]string, len(r.values))
	for i := range names {
		names[i] = fmt.Sprint("c", i)
	}
	return names
}
func (r *echoRows) Close() error { return nil }
func (r *echoRows) Next(dest []driver.Value) error {
	if r.done {
		return io.EOF
	}
	r.done = true
	copy(dest, r.values)
	return nil
}

type echoColumnRows struct {
	*echoRows
	direct bool
}

func (r *echoColumnRows) NextRow() error {
	if r.done {
		return io.EOF
	}
	r.done = true
	return nil
}

func (r *echoColumnRows) ScanColumn(ctx driver.ScanContext, index int, dest any) error {
	if r.direct {
		return dest.(sql.Scanner).Scan(r.values[index])
	}
	return sql.ConvertAssign(ctx, dest, r.values[index])
}

// echo binds arg through the driver in the given mode and scans the
// returned column into dest.
func echo(t *testing.T, mode string, arg, dest any) error {
	t.Helper()
	registerEcho()
	db, err := sql.Open("decimal-echo", mode)
	if err != nil {
		t.Fatal(err)
	}
	defer db.Close()
	rows, err := db.QueryContext(context.Background(), "echo", arg)
	if err != nil {
		return err
	}
	defer rows.Close()
	if !rows.Next() {
		t.Fatalf("%s: no row: %v", mode, rows.Err())
	}
	return rows.Scan(dest)
}

// decimalSource is a foreign decompose-only result type.
type decimalSource struct {
	negative    bool
	coefficient []byte
	exponent    int32
	form        byte
}

func (s decimalSource) Decompose([]byte) (byte, bool, []byte, int32) {
	return s.form, s.negative, s.coefficient, s.exponent
}

// TestScanThroughDatabaseSQL covers the accepted kinds end to end through
// database/sql and the echo driver: wide and scaled vectors bind as text (Decimal, NullDecimal) or by
// decompose (SQLDecimal) and scan back with value and scale; results
// delivered as string, []byte, int64, float64 and decompose scan exactly;
// NULL scans into NullDecimal and fails into Decimal; and every route,
// including RowsColumnScanner, agrees.
func TestScanThroughDatabaseSQL(t *testing.T) {
	above := new(big.Int).Lsh(big.NewInt(1), 130)
	vectors := []string{"1.10", "0.00", "-0", "-12345678901234567890123456789012345678E-38", above.String() + "E-3"}
	for _, mode := range []string{"default", "columns", "direct"} {
		for _, text := range vectors {
			want := MustParse(text)
			for _, arg := range []any{want, &want, SQLDecimal{want}, NullDecimal{Decimal: want, Valid: true}} {
				var got Decimal
				if err := echo(t, mode, arg, &got); err != nil || !sameCohort(got, want) {
					t.Fatalf("%s %T %s: (%v, %v)", mode, arg, text, got, err)
				}
				var null NullDecimal
				if err := echo(t, mode, arg, &null); err != nil || !null.Valid || !sameCohort(null.Decimal, want) {
					t.Fatalf("%s %T %s into NullDecimal: (%+v, %v)", mode, arg, text, null, err)
				}
			}
		}
		// NULL: nil, a nil pointer, and an invalid NullDecimal bind as NULL.
		for _, arg := range []any{nil, (*Decimal)(nil), (*NullDecimal)(nil), NullDecimal{}} {
			null := NullDecimal{Decimal: MustParse("7.5"), Valid: true}
			if err := echo(t, mode, arg, &null); err != nil || null.Valid || null.Decimal.slow != nil || !null.Decimal.isZero() || null.Decimal.exponent() != 0 {
				t.Fatalf("%s NULL %T: (%+v, %v)", mode, arg, null, err)
			}
			kept := MustParse("7.5")
			if err := echo(t, mode, arg, &kept); !errors.Is(err, ErrInvalidOperation) || !sameCohort(kept, MustParse("7.5")) {
				t.Fatalf("%s NULL into Decimal: (%v, %v)", mode, kept, err)
			}
		}
	}
	// Result kinds a driver delivers (raw route).
	tenth, _ := FromFloat64Exact(0.1)
	for _, tc := range []struct {
		src  any
		want Decimal
	}{
		{"1.10", MustParse("1.10")},
		{[]byte("-0.000"), MustParse("0.000")},
		{int64(math.MinInt64), MustParse("-9223372036854775808")},
		{0.1, tenth},
		{decimalSource{coefficient: []byte{0x6e}, exponent: -2}, MustParse("1.10")},
		{SQLDecimal{MustParse("-3.00")}, MustParse("-3.00")},
	} {
		for _, mode := range []string{"raw"} {
			var got Decimal
			if err := echo(t, mode, tc.src, &got); err != nil || !sameCohort(got, tc.want) {
				t.Fatalf("raw %T %v: (%v, %v), want %v", tc.src, tc.src, got, err, tc.want)
			}
			var null NullDecimal
			if err := echo(t, mode, tc.src, &null); err != nil || !null.Valid || !sameCohort(null.Decimal, tc.want) {
				t.Fatalf("raw %T into NullDecimal: (%+v, %v)", tc.src, null, err)
			}
		}
	}
	// Refused results keep typed identity through database/sql's wrapping.
	type driverSpecific struct{ digits string }
	for _, tc := range []struct {
		src  any
		code ErrorCode
	}{
		{"NaN", ErrConversionSyntax}, {[]byte("Infinity"), ErrConversionSyntax}, {"-Infinity", ErrConversionSyntax},
		{true, ErrConversionSyntax}, {time.Unix(0, 0), ErrConversionSyntax}, {driverSpecific{"1"}, ErrConversionSyntax},
		{math.NaN(), ErrConversionSyntax}, {decimalSource{form: 2}, ErrConversionSyntax},
	} {
		kept := MustParse("7.5")
		if err := echo(t, "raw", tc.src, &kept); !errors.Is(err, tc.code) || !sameCohort(kept, MustParse("7.5")) {
			t.Fatalf("raw %T %v: (%v, %v), want %v", tc.src, tc.src, kept, err, tc.code)
		}
	}
}

// TestNullDecimalWithStdlibNull covers the interplay with sql.Null[Decimal]:
// both carry NULL and values through database/sql, and only
// NullDecimal keeps its fields on a failed scan.
func TestNullDecimalWithStdlibNull(t *testing.T) {
	var stdlib sql.Null[Decimal]
	if err := echo(t, "default", SQLDecimal{MustParse("1.10")}, &stdlib); err != nil || !stdlib.Valid || !sameCohort(stdlib.V, MustParse("1.10")) {
		t.Fatalf("sql.Null[Decimal]: (%+v, %v)", stdlib, err)
	}
	ours := NullDecimal{Decimal: MustParse("9.9"), Valid: true}
	if err := ours.Scan("x"); err == nil || !ours.Valid || !sameCohort(ours.Decimal, MustParse("9.9")) {
		t.Fatalf("failed NullDecimal scan changed the receiver: (%+v, %v)", ours, err)
	}
	if v, err := (NullDecimal{}).Value(); v != nil || err != nil {
		t.Fatalf("invalid Value: (%v, %v)", v, err)
	}
	if v, err := (NullDecimal{Decimal: MustParse("1.10"), Valid: true}).Value(); v != "1.10" || err != nil {
		t.Fatalf("valid Value: (%v, %v)", v, err)
	}
}

// TestScanDirectMatrix covers accepted and unknown source kinds and the
// Scan precedence directly: each kind against
// an independent oracle, receiver atomicity on a populated slow receiver,
// nil receivers, typed-nil decompose sources, and no retention of []byte.
func TestScanDirectMatrix(t *testing.T) {
	populated := MustParse(strings.Repeat("7", 60) + "E-5")
	failures := []struct {
		src  any
		code ErrorCode
	}{
		{"", ErrConversionSyntax}, {[]byte(nil), ErrConversionSyntax}, {"1_000", ErrConversionSyntax}, {"NaN", ErrConversionSyntax},
		{"1e2147483648", ErrExponentRange}, {math.Inf(-1), ErrConversionSyntax}, {false, ErrConversionSyntax},
		{namedText("1.5"), ErrConversionSyntax},
		{(*SQLDecimal)(nil), ErrConversionSyntax}, {(*foreignSource)(nil), ErrConversionSyntax},
		{decimalSource{form: 1}, ErrConversionSyntax}, {decimalSource{form: 9}, ErrConversionSyntax},
	}
	for _, tc := range failures {
		d := populated
		err := d.Scan(tc.src)
		if !errors.Is(err, tc.code) || !sameCohort(d, populated) || d.slow != populated.slow {
			t.Fatalf("Scan(%T %v): err %v, receiver %v", tc.src, tc.src, err, d)
		}
		n := NullDecimal{Decimal: populated, Valid: true}
		if err := n.Scan(tc.src); !errors.Is(err, tc.code) || !n.Valid || n.Decimal.slow != populated.slow {
			t.Fatalf("NullDecimal.Scan(%T): err %v, receiver %+v", tc.src, err, n)
		}
	}
	var unsupported *Error
	if err := new(Decimal).Scan(time.Unix(0, 0)); !errors.As(err, &unsupported) || unsupported.Remedy != "unsupported source time.Time" || strings.Contains(err.Error(), "1970") {
		t.Fatalf("unsupported source: %v", err)
	}
	var pe *Error
	if err := new(Decimal).Scan("NaN"); !errors.As(err, &pe) || pe.Op != "Scan" || pe.Input != "NaN" {
		t.Fatalf("text error carrier: %v", err)
	}
	for name, f := range map[string]func() error{
		"*Decimal":          func() error { return (*Decimal)(nil).Scan("1") },
		"*NullDecimal":      func() error { return (*NullDecimal)(nil).Scan("1") },
		"Decimal NULL":      func() error { return new(Decimal).Scan(nil) },
		"*Decimal budgeted": func() error { return (*Decimal)(nil).ScanWithBudget("1", Budget{}) },
	} {
		var oe *Error
		if err := f(); !errors.As(err, &oe) || !errors.Is(err, ErrInvalidOperation) || oe.Condition != InvalidOperation {
			t.Fatalf("%s: %v", name, err)
		}
	}
	raw := []byte("12.3400")
	var got Decimal
	if err := got.Scan(raw); err != nil {
		t.Fatal(err)
	}
	copy(raw, "99.9999")
	if !sameCohort(got, MustParse("12.3400")) {
		t.Fatalf("[]byte retained: %v", got)
	}
	for _, f := range []float64{0, math.Copysign(0, -1)} {
		d := populated
		if err := d.Scan(f); err != nil || !d.isZero() || d.exponent() != 0 || d.negative() || d.slow != nil {
			t.Fatalf("float64 %v: (%#v, %v)", f, d, err)
		}
	}
	rng := rand.New(rand.NewPCG(50, 1))
	for range 5000 {
		switch rng.IntN(3) {
		case 0:
			v := int64(rng.Uint64())
			var d Decimal
			if err := d.Scan(v); err != nil || d.String() != fmt.Sprint(v) || d.exponent() != 0 {
				t.Fatalf("int64 %d: (%v, %v)", v, d, err)
			}
		case 1:
			f := math.Float64frombits(rng.Uint64())
			if math.IsNaN(f) || math.IsInf(f, 0) {
				continue
			}
			var d Decimal
			// The cohort is the largest exponent <= 0 at which the value is
			// exact: minus the power of two in big.Rat's reduced denominator.
			want := new(big.Rat).SetFloat64(f)
			if err := d.Scan(f); err != nil || decimalRat(t, d).Cmp(want) != 0 || int(d.exponent()) != -(want.Denom().BitLen()-1) {
				t.Fatalf("float64 %v: (%v, %v)", f, d, err)
			}
		default:
			raw := make([]byte, rng.IntN(40))
			for i := range raw {
				raw[i] = byte(rng.Uint32())
			}
			c := new(big.Int).SetBytes(raw)
			e := int32(rng.IntN(80) - 40)
			var d Decimal
			if err := d.Scan(decimalSource{negative: rng.IntN(2) == 0, coefficient: c.Bytes(), exponent: e}); err != nil || d.exponent() != e || d.coefficientDigits() != c.String() && c.Sign() != 0 || c.Sign() == 0 && !d.isZero() {
				t.Fatalf("decompose %s E%d: (%v, %v)", c, e, d, err)
			}
		}
	}
}

type namedText string

type foreignSource struct{ value Decimal }

func (s *foreignSource) Decompose(buf []byte) (byte, bool, []byte, int32) {
	return SQLDecimal{s.value}.Decompose(buf)
}

// TestScanWithBudget covers the Scan tariff per kind: byte, digit
// and work caps at their boundaries, and pre-scan refusals that copy no
// input (a []byte refusal is an Error without Input).
func TestScanWithBudget(t *testing.T) {
	text := "123.4500"
	populated := MustParse(strings.Repeat("7", 60) + "E-5")
	for _, tc := range []struct {
		src    any
		budget Budget
		ok     bool
	}{
		{text, Budget{MaxInputBytes: 7}, false}, {text, Budget{MaxInputBytes: 8}, true},
		{text, Budget{MaxWork: 7}, false}, {text, Budget{MaxWork: 8}, true},
		{text, Budget{MaxDigits: 6}, false}, {text, Budget{MaxDigits: 7}, true},
		{int64(-12345), Budget{MaxDigits: 4}, false}, {int64(-12345), Budget{MaxDigits: 5, MaxWork: 1}, true},
		// Powers of ten gain a digit exactly at the boundary.
		{int64(10), Budget{MaxDigits: 1}, false}, {int64(10), Budget{MaxDigits: 2}, true},
		{int64(-100), Budget{MaxDigits: 2}, false}, {int64(-100), Budget{MaxDigits: 3}, true},
		{int64(9), Budget{MaxDigits: 1}, true},
		// 0.1 = 3602879701896397·2^−55: 5 passes (435 units), 55 digits.
		{0.1, Budget{MaxWork: 434}, false}, {0.1, Budget{MaxWork: 435}, true},
		{0.1, Budget{MaxDigits: 54}, false}, {0.1, Budget{MaxDigits: 55}, true},
		// A 20-byte coefficient: n = 160 bits, U = ⌊160·30103/100000⌋+1 = 49, W = (2·6)²+2·6 = 156.
		{decimalSource{coefficient: make20(), exponent: -3}, Budget{MaxInputBytes: 19}, false},
		{decimalSource{coefficient: make20(), exponent: -3}, Budget{MaxInputBytes: 20}, true},
		{decimalSource{coefficient: make20(), exponent: -3}, Budget{MaxDigits: 48}, false},
		{decimalSource{coefficient: make20(), exponent: -3}, Budget{MaxDigits: 49}, true},
		{decimalSource{coefficient: make20(), exponent: -3}, Budget{MaxWork: 155}, false},
		{decimalSource{coefficient: make20(), exponent: -3}, Budget{MaxWork: 156}, true},
	} {
		d := populated
		err := d.ScanWithBudget(tc.src, tc.budget)
		n := NullDecimal{Decimal: populated, Valid: true}
		nerr := n.ScanWithBudget(tc.src, tc.budget)
		for _, got := range []error{err, nerr} {
			if tc.ok != (got == nil) {
				t.Fatalf("%T %v under %+v: %v", tc.src, tc.src, tc.budget, got)
			}
			if !tc.ok && (!errors.Is(got, ErrInsufficientStorage) || scanErrorOp(got) != "ScanWithBudget" || scanErrorCondition(got) != InsufficientStorage) {
				t.Fatalf("%T %v under %+v: refusal identity %#v", tc.src, tc.src, tc.budget, got)
			}
		}
		if !tc.ok && (d.slow != populated.slow || !sameCohort(d, populated) || !n.Valid || n.Decimal.slow != populated.slow) {
			t.Fatalf("%T %v under %+v: refusal changed a receiver: %v, %+v", tc.src, tc.src, tc.budget, d, n)
		}
		if tc.ok && (!n.Valid || !sameCohort(n.Decimal, d)) {
			t.Fatalf("%T %v under %+v: NullDecimal %+v, Decimal %v", tc.src, tc.src, tc.budget, n, d)
		}
	}
	huge := []byte(strings.Repeat("9", 1<<20))
	var oe *Error
	var d Decimal
	if err := d.ScanWithBudget(huge, Budget{MaxInputBytes: 1}); !errors.As(err, &oe) || !errors.Is(err, ErrInsufficientStorage) {
		t.Fatalf("[]byte pre-scan refusal: %v", err)
	}
	src := any(huge)
	if allocs := testing.AllocsPerRun(5, func() { _ = d.ScanWithBudget(src, Budget{MaxInputBytes: 1}) }); allocs > 1 {
		t.Fatalf("[]byte pre-scan refusal allocated %v times", allocs)
	}
	// The string refusal carries the caller's own string: one allocation
	// for the carrier and none for a copy of the megabyte.
	var pe *Error
	text1M := string(huge)
	if err := d.ScanWithBudget(text1M, Budget{MaxInputBytes: 1}); !errors.As(err, &pe) || pe.Input != text1M {
		t.Fatalf("string pre-scan refusal: %v", err)
	}
	src = any(text1M)
	if allocs := testing.AllocsPerRun(5, func() { _ = d.ScanWithBudget(src, Budget{MaxInputBytes: 1}) }); allocs > 1 {
		t.Fatalf("string pre-scan refusal allocated %v times", allocs)
	}
}

// scanErrorOp and scanErrorCondition read the identity fields of either
// Scan error carrier.
func scanErrorOp(err error) string {
	if pe, ok := errors.AsType[*Error](err); ok {
		return pe.Op
	}
	if oe, ok := errors.AsType[*Error](err); ok {
		return oe.Op
	}
	return ""
}

func scanErrorCondition(err error) Conditions {
	if pe, ok := errors.AsType[*Error](err); ok {
		return pe.Condition
	}
	if oe, ok := errors.AsType[*Error](err); ok {
		return oe.Condition
	}
	return 0
}

// TestScanPrecedence covers Scan's refusal precedence: one row per adjacent
// pair of steps (receiver, NULL, classification, byte and work caps,
// syntax and range, digit cap), each through both receivers, with the
// error code, carrier, Op and Condition pinned.
func TestScanPrecedence(t *testing.T) {
	tight := Budget{MaxInputBytes: 1, MaxDigits: 1, MaxWork: 1}
	for _, tc := range []struct {
		name  string
		src   any
		b     Budget
		code  ErrorCode
		parse bool // an *Error with Input; otherwise one without
	}{
		{"classification: kind before caps", true, tight, ErrConversionSyntax, false},
		{"classification: nil pointer before caps", (*SQLDecimal)(nil), tight, ErrConversionSyntax, false},
		{"classification: form before byte cap", decimalSource{form: 1, coefficient: make([]byte, 100)}, tight, ErrConversionSyntax, false},
		{"classification: finiteness before work cap", math.NaN(), tight, ErrConversionSyntax, false},
		{"classification: infinity before digit cap", math.Inf(1), tight, ErrConversionSyntax, false},
		{"byte cap before syntax (string)", "NaN", Budget{MaxInputBytes: 2}, ErrInsufficientStorage, true},
		{"byte cap before syntax ([]byte)", []byte("NaN"), Budget{MaxInputBytes: 2}, ErrInsufficientStorage, false},
		{"work cap before syntax ([]byte)", []byte("NaN"), Budget{MaxWork: 2}, ErrInsufficientStorage, false},
		{"decompose byte cap before digit cap", decimalSource{coefficient: make([]byte, 3)}, Budget{MaxInputBytes: 2, MaxDigits: 1}, ErrInsufficientStorage, false},
		{"syntax before digit cap", "12345x", Budget{MaxDigits: 2}, ErrConversionSyntax, true},
		{"range before digit cap", "12345e99999999999", Budget{MaxDigits: 2}, ErrExponentRange, true},
		// A []byte resource refusal never copies.
		{"digit cap last ([]byte)", []byte("12345"), Budget{MaxDigits: 4}, ErrInsufficientStorage, false},
	} {
		var d Decimal
		var n NullDecimal
		for receiver, err := range map[string]error{"*Decimal": d.ScanWithBudget(tc.src, tc.b), "*NullDecimal": n.ScanWithBudget(tc.src, tc.b)} {
			e, typed := errors.AsType[*Error](err)
			isParse := typed && e.Input != ""
			isOp := typed && e.Input == ""
			// An exponent-range refusal raises no condition flag.
			condition := map[ErrorCode]Conditions{ErrConversionSyntax: ConversionSyntax, ErrInsufficientStorage: InsufficientStorage}[tc.code]
			if !errors.Is(err, tc.code) || isParse != tc.parse || !tc.parse && !isOp || scanErrorOp(err) != "ScanWithBudget" || scanErrorCondition(err) != condition {
				t.Errorf("%s via %s: %#v", tc.name, receiver, err)
			}
		}
	}
	// Step 1 before step 2: a nil receiver is refused even for NULL.
	for name, err := range map[string]error{
		"*Decimal":     (*Decimal)(nil).Scan(nil),
		"*NullDecimal": (*NullDecimal)(nil).Scan(nil),
		"budgeted":     (*NullDecimal)(nil).ScanWithBudget(nil, tight),
	} {
		if !errors.Is(err, ErrInvalidOperation) {
			t.Errorf("nil %s receiver with NULL: %v", name, err)
		}
	}
	// The unsupported-kind carrier keeps its Op and Condition.
	err := new(NullDecimal).Scan(true)
	if e, ok := errors.AsType[*Error](err); !ok || e.Remedy != "unsupported source bool" || scanErrorOp(err) != "Scan" || scanErrorCondition(err) != ConversionSyntax {
		t.Errorf("unsupported carrier: %#v", err)
	}
}

func make20() []byte {
	b := make([]byte, 20)
	for i := range b {
		b[i] = byte(0x91 + i)
	}
	return b
}

// TestScanAllocations covers Scan's allocation class: inline
// results scan without allocating (the any is boxed outside the loop). A
// decompose source is not claimed: Decompose(nil) returns a fresh
// coefficient, and any buffer passed through the interface call escapes.
func TestScanAllocations(t *testing.T) {
	var d Decimal
	for name, src := range map[string]any{
		"string": "12345.6789", "bytes": []byte("-0.00012"), "int64": int64(-42), "float64": 2.5,
	} {
		if allocs := testing.AllocsPerRun(50, func() { _ = d.Scan(src) }); allocs != 0 {
			t.Fatalf("%s allocated %v times", name, allocs)
		}
	}
}

// TestScanReceivers checks the method sets: Value is on the value receiver and
// Scan on the pointer receiver for both types, and failures are atomic.
func TestScanReceivers(t *testing.T) {
	var valuer driver.Valuer = NullDecimal{}
	var scanner sql.Scanner = &NullDecimal{}
	var d Decimal
	var scannerD sql.Scanner = &d
	var valuerD driver.Valuer = d
	if valuer == nil || scanner == nil || scannerD == nil || valuerD == nil {
		t.Fatal("interfaces")
	}
	slow := MustParse(strings.Repeat("3", 50))
	d = slow
	if err := d.Scan(struct{}{}); err == nil || d.slow != slow.slow {
		t.Fatalf("failed Scan changed the receiver: %v", err)
	}
}

// TestScanMathBigSources covers exact math/big sources. Integer text and hand-derived reduced rational coefficients are
// independent of Decimal's conversion engines.
func TestScanMathBigSources(t *testing.T) {
	large, _ := new(big.Int).SetString("-1234567890123456789012345678901234567890", 10)
	nonReduced := big.NewRat(1, 2)
	nonReduced.Num().SetInt64(3)
	nonReduced.Denom().SetInt64(6)
	for _, tc := range []struct {
		src  any
		want string
	}{
		{big.Int{}, "0"}, {new(big.Int), "0"}, {*large, large.Text(10)}, {large, large.Text(10)},
		{*big.NewRat(-11, 10), "-1.1"}, {big.NewRat(-11, 10), "-1.1"},
		{big.Rat{}, "0"}, {new(big.Rat), "0"}, {*nonReduced, "0.5"}, {nonReduced, "0.5"},
		{big.NewRat(100, 1), "100"},
	} {
		d := MustParse("999.00")
		if err := d.Scan(tc.src); err != nil || d.String() != tc.want {
			t.Errorf("%T: Scan = %s, %v; want %s", tc.src, d, err, tc.want)
		}
		n := NullDecimal{Decimal: MustParse("999.00"), Valid: true}
		if err := n.Scan(tc.src); err != nil || !n.Valid || n.Decimal.String() != tc.want {
			t.Errorf("%T: nullable Scan = %+v, %v; want %s", tc.src, n, err, tc.want)
		}
	}
}

// TestScanNonTerminatingRational checks that Scan, which has no
// rounding instruction, refuses atomically with its own actionable remedy.
func TestScanNonTerminatingRational(t *testing.T) {
	for _, r := range []*big.Rat{big.NewRat(1, 3), big.NewRat(2, 7)} {
		for _, src := range []any{r, *r} {
			for _, budgeted := range []bool{false, true} {
				d := MustParse("123456789012345678901234567890.00")
				before := d.String()
				op := "Scan"
				var err error
				if budgeted {
					op = "ScanWithBudget"
					err = d.ScanWithBudget(src, Budget{})
				} else {
					err = d.Scan(src)
				}
				n := NullDecimal{Decimal: d, Valid: true}
				var nerr error
				if budgeted {
					nerr = n.ScanWithBudget(src, Budget{})
				} else {
					nerr = n.Scan(src)
				}
				var nce *Error
				if !errors.As(nerr, &nce) || nce.Op != op || nce.Condition != Inexact || !strings.Contains(nce.Remedy, "scan into a *big.Rat variable") || !n.Valid || n.Decimal.String() != before {
					t.Errorf("nullable rational: %v", nerr)
				}
				var ce *Error
				if !errors.As(err, &ce) || ce.Code != 0 || !errors.Is(err, ErrInexact) || ce.Op != op || ce.Condition != Inexact || !strings.Contains(ce.Remedy, "scan into a *big.Rat variable") {
					t.Errorf("%T: %v, want Scan nonterminating remedy", src, err)
				}
				if d.String() != before {
					t.Fatal("refusal mutated receiver")
				}
			}
		}
	}
}

// TestScanBigFloatRefused checks that classification refuses
// all binary float forms before reading values or inspecting budgets.
func TestScanBigFloatRefused(t *testing.T) {
	mantissa := new(big.Int).Lsh(big.NewInt(1), (1<<22)-1)
	mantissa.Add(mantissa, big.NewInt(1))
	huge := new(big.Float).SetPrec(1 << 22).SetInt(mantissa)
	huge.SetMantExp(huge, big.MinExp)
	negativeZero := new(big.Float).Neg(new(big.Float))
	for _, src := range []any{big.Float{}, new(big.Float), (*big.Float)(nil), *negativeZero, negativeZero, new(big.Float).SetInf(false), new(big.Float).SetInf(true), *new(big.Float).SetInf(false), *new(big.Float).SetInf(true), big.NewFloat(-1.25), huge, *huge} {
		for _, budgeted := range []bool{false, true} {
			for _, nullable := range []bool{false, true} {
				d := MustParse("123456789012345678901234567890.00")
				n := NullDecimal{Decimal: d, Valid: true}
				before := d.String()
				op := "Scan"
				if budgeted {
					op = "ScanWithBudget"
				}
				run := func() error {
					b := Budget{MaxInputBytes: 1, MaxWork: 1}
					if nullable {
						if budgeted {
							return n.ScanWithBudget(src, b)
						}
						return n.Scan(src)
					}
					if budgeted {
						return d.ScanWithBudget(src, b)
					}
					return d.Scan(src)
				}
				err := run()
				var operation *Error
				kind := fmt.Sprintf("%T", src)
				if !errors.As(err, &operation) || operation.Op != op || operation.Condition != ConversionSyntax || operation.Remedy != "unsupported source "+kind+": "+scanBigFloatRemedy || !errors.Is(err, ErrConversionSyntax) {
					t.Errorf("%T: %v, want binary float remedy", src, err)
				}
				if d.String() != before || n.Decimal.String() != before || !n.Valid {
					t.Fatal("float refusal mutated receiver")
				}
				if count := testing.AllocsPerRun(20, func() { _ = run() }); count > 2 {
					t.Errorf("%T refusal allocations = %g, want <=2", src, count)
				}
				if _, err := EstimateScan(src, Budget{}); !errors.Is(err, ErrConversionSyntax) {
					t.Fatal(err)
				}
				if count := testing.AllocsPerRun(20, func() { _, _ = EstimateScan(src, Budget{}) }); count != 0 {
					t.Errorf("float estimator allocated %g", count)
				}
			}
		}
	}
}

// TestScanMathBigThroughDatabaseSQL checks that database/sql keeps
// exact dynamic types, typed nils and wrapped error identities intact.
func TestScanMathBigThroughDatabaseSQL(t *testing.T) {
	for _, mode := range []string{"raw", "raw-direct"} {
		for _, tc := range []struct {
			src  any
			want string
			code ErrorCode
		}{
			{*big.NewInt(123), "123", 0}, {big.NewInt(-123), "-123", 0},
			{*big.NewRat(11, 10), "1.1", 0}, {big.NewRat(1, 8), "0.125", 0},
			{big.Float{}, "", ErrConversionSyntax}, {big.NewFloat(1), "", ErrConversionSyntax},
			{(*big.Float)(nil), "", ErrConversionSyntax}, {(*big.Int)(nil), "", ErrConversionSyntax}, {(*big.Rat)(nil), "", ErrConversionSyntax},
			{big.NewRat(1, 3), "", ErrInexact},
		} {
			var d Decimal
			err := echo(t, mode, tc.src, &d)
			if tc.code != 0 {
				n := NullDecimal{Decimal: MustParse("123456789012345678901234567890.00"), Valid: true}
				before := n.Decimal.String()
				if nerr := echo(t, mode, tc.src, &n); !errors.Is(nerr, tc.code) || !n.Valid || n.Decimal.String() != before {
					t.Errorf("nullable SQL %T: %v", tc.src, nerr)
				}
				if !errors.Is(err, tc.code) {
					t.Errorf("%s %T: %v, want %v", mode, tc.src, err, tc.code)
				}
				continue
			}
			if err != nil || d.String() != tc.want {
				t.Errorf("%s %T: %s, %v", mode, tc.src, d, err)
			}
			var n sql.Null[Decimal]
			if err := echo(t, mode, tc.src, &n); err != nil || !n.Valid || n.V.String() != tc.want {
				t.Errorf("sql.Null %s %T: %v", mode, tc.src, err)
			}
		}
		var n NullDecimal
		if err := echo(t, mode, nil, &n); err != nil || n.Valid {
			t.Errorf("NULL: %v", err)
		}
		var d Decimal
		if err := echo(t, mode, nil, &d); !errors.Is(err, ErrInvalidOperation) {
			t.Errorf("bare NULL: %v", err)
		}
	}
}

// TestScanMathBigPrecedence checks that nil receivers, classified
// sources and byte caps precede delegated work while failures stay atomic.
func TestScanMathBigPrecedence(t *testing.T) {
	badInt := big.NewInt(1)
	badInt.Bits()[0] = 0
	badRat := big.NewRat(1, 2)
	badRat.Denom().Bits()[0] = 0
	for _, src := range []any{(*big.Int)(nil), (*big.Rat)(nil), badInt, *badInt, badRat, *badRat} {
		var nilD *Decimal
		if err := nilD.Scan(src); !errors.Is(err, ErrInvalidOperation) {
			t.Errorf("nil receiver: %v", err)
		}
		for _, budgeted := range []bool{false, true} {
			d := MustParse("123456789012345678901234567890.00")
			n := NullDecimal{Decimal: d, Valid: true}
			before := d.String()
			op := "Scan"
			var errs []error
			if budgeted {
				op = "ScanWithBudget"
				b := Budget{MaxInputBytes: 1, MaxDigits: 1, MaxWork: 1}
				errs = []error{d.ScanWithBudget(src, b), n.ScanWithBudget(src, b)}
			} else {
				errs = []error{d.Scan(src), n.Scan(src)}
			}
			for _, err := range errs {
				var oe *Error
				if !errors.As(err, &oe) || oe.Op != op || !errors.Is(err, ErrConversionSyntax) {
					t.Errorf("%T: %v", src, err)
				}
			}
			if d.String() != before || !n.Valid || n.Decimal.String() != before {
				t.Fatal("failure changed receiver")
			}
		}
	}
}

// TestScanMathBigBudget covers math/big budgets: byte units are minimal
// magnitude bytes, integer digit/work envelopes are checked before copies.
func TestScanMathBigBudget(t *testing.T) {
	for _, src := range []any{big.NewInt(256), *big.NewInt(256)} {
		for _, tc := range []struct {
			b    Budget
			fail bool
		}{
			{Budget{MaxInputBytes: 1}, true}, {Budget{MaxInputBytes: 2}, false},
			{Budget{MaxDigits: 2}, true}, {Budget{MaxDigits: 3}, false},
			{Budget{MaxWork: 5}, true}, {Budget{MaxWork: 6}, false},
		} {
			var d Decimal
			err := d.ScanWithBudget(src, tc.b)
			if tc.fail {
				if !errors.Is(err, ErrInsufficientStorage) {
					t.Errorf("%T %+v: %v", src, tc.b, err)
				}
				if n := testing.AllocsPerRun(20, func() { _ = d.ScanWithBudget(src, tc.b) }); n > 1 {
					t.Errorf("refusal allocated %g", n)
				}
			} else if err != nil || d.String() != "256" {
				t.Errorf("%T %+v: %s %v", src, tc.b, d, err)
			}
		}
	}
	for _, src := range []any{big.NewRat(1, 256), *big.NewRat(1, 256)} {
		var d Decimal
		if err := d.ScanWithBudget(src, Budget{MaxInputBytes: 2}); !errors.Is(err, ErrInsufficientStorage) {
			t.Errorf("rational bytes: %v", err)
		}
		if n := testing.AllocsPerRun(20, func() { _ = d.ScanWithBudget(src, Budget{MaxInputBytes: 2}) }); n != 1 {
			t.Errorf("rational byte refusal allocated %g", n)
		}
		if err := d.ScanWithBudget(src, Budget{MaxInputBytes: 3}); err != nil || d.String() != "0.00390625" {
			t.Errorf("rational bytes: %s %v", d, err)
		}
		if n := testing.AllocsPerRun(20, func() { _ = d.ScanWithBudget(src, Budget{MaxWork: 1}) }); n > 1 {
			t.Errorf("rational precharge allocated %g", n)
		}
	}
}

// TestScanEquivalentToConstructors checks that Scan equals the
// constructors across values and every small digit/work boundary, with a guard
// requiring successful and refused calls from both constructor families.
func TestScanEquivalentToConstructors(t *testing.T) {
	rng := rand.New(rand.NewPCG(64, 64))
	var successes, refusals [2]int
	for range 160 {
		x := big.NewInt(rng.Int64N(200000) - 100000)
		r := new(big.Rat).SetFrac(x, big.NewInt(rng.Int64N(100)+1))
		for family, ptr := range []any{x, r} {
			for _, digits := range []uint64{0, 1, 3, 8} {
				for _, work := range []uint64{0, 1, 5, 50, 500} {
					b := Budget{MaxDigits: digits, MaxWork: work}
					var want Decimal
					var expected error
					var value any
					if family == 0 {
						want, expected = FromBigIntWithBudget(x, Budget{MaxInputDigits: digits, MaxDigits: digits, MaxWork: work})
						value = *x
					} else {
						want, _, expected = FromRatWithContext(r, Context{}.WithBudget(Budget{MaxDigits: digits, MaxWork: work}))
						value = *r
					}
					for _, src := range []any{ptr, value} {
						var got Decimal
						err := got.ScanWithBudget(src, b)
						carrier := func(e error) (string, Conditions) {
							if oe, ok := errors.AsType[*Error](e); ok {
								return "operation", oe.Condition
							}
							if ce, ok := errors.AsType[*Error](e); ok {
								return "condition", ce.Condition
							}
							if e == nil {
								return "", 0
							}
							return fmt.Sprintf("%T", e), 0
						}
						kind, cond := carrier(err)
						wantKind, wantCond := carrier(expected)
						if kind != wantKind || cond != wantCond {
							t.Fatalf("%T %+v carrier/condition: %s %v vs %s %v", src, b, kind, cond, wantKind, wantCond)
						}
						if expected == nil {
							successes[family]++
							if err != nil || got.String() != want.String() || got.Exponent() != want.Exponent() {
								t.Fatalf("%T %+v: %s %v vs %s %v", src, b, got, err, want, expected)
							}
						} else {
							refusals[family]++
							for code := ErrConversionSyntax; code <= ErrDivisionUndefined; code++ {
								if errors.Is(err, code) != errors.Is(expected, code) {
									t.Fatalf("%T %+v: %v vs %v", src, b, err, expected)
								}
							}
						}
					}
				}
			}
		}
	}
	for i := range 2 {
		if successes[i] == 0 || refusals[i] == 0 {
			t.Fatal("vacuous constructor differential", successes, refusals)
		}
	}
}

// TestScanMathBigExponentPrecharge checks that the definite rational exponent check precedes work admission. The source is
// held once, and every refusal allocates only its Error.
func TestScanMathBigExponentPrecharge(t *testing.T) {
	if strconv.IntSize != 64 {
		t.Skip("the 256 MiB source boundary needs a 64-bit target")
	}
	words := make([]big.Word, (uint64(1)<<31)/uint64(bits.UintSize)+1)
	r := big.NewRat(1, 2)
	for _, tc := range []struct {
		top  big.Word
		code ErrorCode
	}{{1, ErrInsufficientStorage}, {2, ErrExponentRange}} {
		words[len(words)-1] = tc.top
		r.Denom().SetBits(words)
		var d Decimal
		b := Budget{MaxWork: 1}
		err := d.ScanWithBudget(r, b)
		var oe *Error
		condition := InsufficientStorage
		if tc.code == ErrExponentRange {
			condition = 0
		}
		if !errors.Is(err, tc.code) || !errors.As(err, &oe) || oe.Op != "ScanWithBudget" || oe.Condition != condition {
			t.Fatalf("top %d: %v, want %v/%v", tc.top, err, tc.code, condition)
		}
		_, estErr := EstimateScan(r, Budget{})
		if tc.code == ErrExponentRange {
			if !errors.Is(estErr, ErrExponentRange) {
				t.Errorf("exponent estimator: %v", estErr)
			}
		} else if runtime.GOARCH == "wasm" {
			// Go's wasm int is 64-bit, but its linear-memory address window
			// cannot admit this in-domain result plan.
			if !errors.Is(estErr, ErrInsufficientStorage) {
				t.Errorf("wasm physical-plan estimator: %v", estErr)
			}
		} else if estErr != nil {
			t.Errorf("in-domain exponent estimator: %v", estErr)
		}
		if n := testing.AllocsPerRun(5, func() { _ = d.ScanWithBudget(r, b) }); n > 1 {
			t.Errorf("exponent refusal allocated %g", n)
		}
		// The Scan-only byte cap still precedes the delegated exponent check.
		if err := d.ScanWithBudget(r, Budget{MaxInputBytes: 1, MaxWork: 1}); !errors.Is(err, ErrInsufficientStorage) {
			t.Errorf("byte cap: %v", err)
		}
	}
}

// TestScanBigFloatClassificationDeadline checks that big.Float is refused
// before Float.Rat materializes it. The
// subprocess bounds a mistaken Float.Rat materialization independently of
// allocation counters; typed-nil coverage catches observable early reads.
func TestScanBigFloatClassificationDeadline(t *testing.T) {
	if runtime.GOOS == "js" {
		t.Skip("wasm cannot launch the deadline subprocess; refusal identity runs separately")
	}
	if os.Getenv("DECIMAL_SCAN_FLOAT_CHILD") != "1" {
		ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
		defer cancel()
		cmd := exec.CommandContext(ctx, os.Args[0], "-test.run=^TestScanBigFloatClassificationDeadline$", "-test.count=1")
		cmd.Env = append(os.Environ(), "DECIMAL_SCAN_FLOAT_CHILD=1")
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("float classification subprocess: %v (%v): %s", err, ctx.Err(), out)
		}
		return
	}
	rng := rand.New(rand.NewPCG(64064, 1))
	raw := make([]byte, 1<<19)
	for i := range raw {
		raw[i] = byte(rng.Uint32())
	}
	raw[0] |= 0x80
	raw[len(raw)-1] |= 1
	x := new(big.Float).SetPrec(1 << 22).SetInt(new(big.Int).SetBytes(raw))
	// MinExp+1 avoids math/big.Float.Rat's int32 subtraction overflow
	// at the exact boundary, so a mistaken materialization would reach costly work.
	x.SetMantExp(x, big.MinExp+1)
	var d Decimal
	if err := d.Scan(x); !errors.Is(err, ErrConversionSyntax) {
		t.Fatal(err)
	}
}

// TestScanZeroRatAllocation checks that the implicit
// denominator of big.Rat{} must not allocate before a zero's work refusal,
// or on success when its estimator promises zero heap.
func TestScanZeroRatAllocation(t *testing.T) {
	for _, src := range []any{big.Rat{}, new(big.Rat), *big.NewRat(0, 1), big.NewRat(0, 1)} {
		for _, work := range []uint64{0, 1, 4} {
			var d Decimal
			b := Budget{MaxWork: work}
			err := d.ScanWithBudget(src, b)
			want := float64(0)
			if work == 1 {
				want = 1
				if !errors.Is(err, ErrInsufficientStorage) {
					t.Fatal(err)
				}
			} else if err != nil || !d.IsZero() {
				t.Fatal(err)
			}
			if n := testing.AllocsPerRun(20, func() { _ = d.ScanWithBudget(src, b) }); n != want {
				t.Errorf("%T work %d: allocations %g, want %g", src, work, n, want)
			}
		}
	}
}

// TestScanRationalCoefficientOracle covers hand-derived rational witnesses
// and an independent reduced-factor oracle; no Decimal egress is an oracle.
func TestScanRationalCoefficientOracle(t *testing.T) {
	pow := func(b, e int64) *big.Int { return new(big.Int).Exp(big.NewInt(b), big.NewInt(e), nil) }
	three := pow(3, 20000)
	pairs := [][2]*big.Int{
		{big.NewInt(1), pow(2, 65536)}, {big.NewInt(1), pow(5, 28224)},
		{big.NewInt(1), new(big.Int).Mul(pow(2, 32768), pow(5, 14112))},
		{big.NewInt(1), new(big.Int).Mul(pow(2, 65536), pow(5, 28224))},
		{three, pow(2, 65536)}, {three, pow(5, 28224)},
		{new(big.Int).Mul(big.NewInt(6), pow(7, 500)), new(big.Int).Mul(new(big.Int).Mul(big.NewInt(2), pow(7, 500)), pow(5, 9000))},
	}
	rng := rand.New(rand.NewPCG(64, 7))
	for range 60 {
		pairs = append(pairs, [2]*big.Int{big.NewInt(rng.Int64N(20000) - 10000), new(big.Int).Mul(pow(2, rng.Int64N(90)), pow(5, rng.Int64N(90)))})
	}
	for _, pair := range pairs {
		r := big.NewRat(1, 2)
		r.Num().Set(pair[0])
		r.Denom().Set(pair[1])
		red := new(big.Rat).SetFrac(pair[0], pair[1])
		den := new(big.Int).Set(red.Denom())
		a := den.TrailingZeroBits()
		den.Rsh(den, a)
		var b uint
		for q, rem := new(big.Int), new(big.Int); ; b++ {
			q.QuoRem(den, big.NewInt(5), rem)
			if rem.Sign() != 0 {
				break
			}
			den.Set(q)
		}
		if den.Cmp(big.NewInt(1)) != 0 {
			t.Fatal("nonterminating oracle witness")
		}
		m := max(a, b)
		coefficient := new(big.Int).Lsh(new(big.Int).Set(red.Num()), m-a)
		coefficient.Mul(coefficient, pow(5, int64(m-b)))
		text := coefficient.Text(10)
		for _, src := range []any{r, *r} {
			var d Decimal
			if err := d.Scan(src); err != nil {
				t.Fatal(err)
			}
			// Fixed-point formatting is a value/cohort observation; the
			// coefficient/exponent expectation is derived entirely above.
			want := text
			if m > 0 {
				negative := strings.HasPrefix(want, "-")
				want = strings.TrimPrefix(want, "-")
				if len(want) <= int(m) {
					want = strings.Repeat("0", int(m)-len(want)+1) + want
				}
				i := len(want) - int(m)
				want = want[:i] + "." + want[i:]
				if negative {
					want = "-" + want
				}
			}
			if fmt.Sprintf("%f", d) != want || d.Exponent() != -int32(m) {
				t.Fatalf("rational oracle mismatch at %d/%d bits", pair[0].BitLen(), pair[1].BitLen())
			}
			if r.Num().Cmp(pair[0]) != 0 || r.Denom().Cmp(pair[1]) != 0 {
				t.Fatal("Scan mutated source")
			}
		}
	}
}

// TestScanRationalLargePrecharge covers the 1/5^451596 witness:
// a cap one below the independently calculated B refuses without math/big work.
func TestScanRationalLargePrecharge(t *testing.T) {
	r := new(big.Rat).SetFrac(big.NewInt(1), new(big.Int).Exp(big.NewInt(5), big.NewInt(451596), nil))
	// The rational precharge: a=0, bMax=floor(bd*log_5(2)) using the
	// fixed-point upper bound of log_5(2). All quantities here fit uint64.
	bd := uint64(r.Denom().BitLen())
	bmax := new(big.Int).Mul(new(big.Int).SetUint64(bd), big.NewInt(430676558073393051))
	bmax.Quo(bmax, big.NewInt(1000000000000000000))
	m := bmax.Uint64()
	wn, wd := uint64(1), (bd+63)/64
	wm := (m*332193/100000 + 1 + 63) / 64
	uc := ((wn+wm)*64*30103)/100000 + 1
	charge := m*(wd+1) + (wn + wd) + (4*wm*wm+2)/3 + wm + wn*wm + uc*((uc+8)/9) + wn + wd
	var d Decimal
	b := Budget{MaxWork: charge - 1}
	if err := d.ScanWithBudget(r, b); !errors.Is(err, ErrInsufficientStorage) {
		t.Fatal(err)
	}
	if n := testing.AllocsPerRun(5, func() { _ = d.ScanWithBudget(r, b) }); n != 1 {
		t.Errorf("precharge allocated %g, want error only", n)
	}
}

// TestScanBigFloatRemedy checks the big.Float remedy text: the
// explicit-conversion remedy must bind both Float.Rat return values before
// calling FromRatToExponent, and the shown statements must compile.
func TestScanBigFloatRemedy(t *testing.T) {
	f := big.NewFloat(1.25)
	var d Decimal
	err := d.Scan(f)
	if err == nil || !strings.Contains(err.Error(), "r, _ := f.Rat(nil); FromRatToExponent(r, -scale, mode)") {
		t.Fatalf("non-compilable remedy: %v", err)
	}
	scale, mode := int32(2), TiesToEven
	r, _ := f.Rat(nil)
	got, _, convertErr := FromRatToExponent(r, -scale, mode)
	if convertErr != nil || got.String() != "1.25" {
		t.Fatalf("remedy: %s %v", got, convertErr)
	}
}

// TestScanEveryIntegerKind checks that every Go integer kind
// and float32 scan exactly (drivers deliver uint64 for unsigned BIGINT), as
// the decimal integer strconv prints at exponent 0 and the exact binary
// expansion of a float32, and EstimateScan admits each under its estimate.
func TestScanEveryIntegerKind(t *testing.T) {
	sources := []any{
		int(-7), int8(math.MinInt8), int16(math.MaxInt16), int32(math.MinInt32),
		int64(math.MinInt64), uint(0), uint8(255), uint16(math.MaxUint16),
		uint32(math.MaxUint32), uint64(math.MaxUint64), uint64(1 << 63), uint(math.MaxUint),
	}
	for _, src := range sources {
		want := fmt.Sprint(src) // strconv's decimal integer, the oracle
		var d Decimal
		if err := d.Scan(src); err != nil || d.String() != want || d.exponent() != 0 {
			t.Fatalf("Scan(%T %v) = %v, %v; want %s", src, src, d, err, want)
		}
		n := NullDecimal{}
		if err := n.Scan(src); err != nil || !n.Valid || n.Decimal.String() != want {
			t.Fatalf("NullDecimal.Scan(%T %v) = %+v, %v", src, src, n, err)
		}
		c, err := EstimateScan(src, Budget{})
		if err != nil || c.Digits != uint64(len(strings.TrimPrefix(want, "-"))) {
			t.Fatalf("EstimateScan(%T %v) = %+v, %v", src, src, c, err)
		}
		if err := d.ScanWithBudget(src, c.Budget()); err != nil {
			t.Fatalf("ScanWithBudget(%T %v) refused under its estimate: %v", src, src, err)
		}
		if c.Digits > 1 {
			if err := d.ScanWithBudget(src, Budget{MaxDigits: c.Digits - 1}); !errors.Is(err, ErrInsufficientStorage) {
				t.Fatalf("ScanWithBudget(%T %v) admitted below its digits: %v", src, src, err)
			}
		}
	}
	floats := []float32{0.1, -1.5, math.SmallestNonzeroFloat32, math.MaxFloat32, float32(math.Copysign(0, -1)), 16777217}
	for _, f := range floats {
		var d Decimal
		if err := d.Scan(f); err != nil {
			t.Fatalf("Scan(float32 %v): %v", f, err)
		}
		want := new(big.Rat).SetFloat64(float64(f)) // exact: float32 ⊂ float64
		if got, err := d.Rat(nil); err != nil || got.Cmp(want) != 0 {
			t.Fatalf("Scan(float32 %v) = %v; want %v", f, d, want.FloatString(160))
		}
		var wide Decimal
		if err := wide.Scan(float64(f)); err != nil || !sameCohort(d, wide) {
			t.Fatalf("Scan(float32 %v) = %v, float64 path %v", f, d, wide)
		}
		if c, err := EstimateScan(f, Budget{}); err != nil || d.ScanWithBudget(f, c.Budget()) != nil {
			t.Fatalf("EstimateScan(float32 %v) = %+v, %v", f, c, err)
		}
	}
	for _, f := range []float32{float32(math.Inf(1)), float32(math.NaN())} {
		if err := new(Decimal).Scan(f); !errors.Is(err, ErrConversionSyntax) {
			t.Fatalf("Scan(float32 %v): %v", f, err)
		}
	}
}
