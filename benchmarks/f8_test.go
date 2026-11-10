// SPDX-License-Identifier: Apache-2.0

// Family F8: database/sql round trip through an in-tree, stdlib-only fake
// driver. Nothing here opens a database
// or imports a third-party driver.

package benchmarks

import (
	"database/sql"
	"database/sql/driver"
	"errors"
	"fmt"
	"io"
	"math/big"
	"strings"
	"sync"
	"testing"

	decimal "github.com/0xCarbon/decimal"
)

// f8Driver echoes each query's bound arguments as one row. Its
// NamedValueChecker accepts decompose values (modelling a driver that types
// parameters by value) and returns ErrSkip otherwise, so ordinary arguments
// pass through Value. Text arrives as string and is returned as []byte, as
// lib/pq and go-sql-driver/mysql deliver NUMERIC; decompose values and nil
// are returned unchanged.
type f8Driver struct{}

var registerF8 = sync.OnceFunc(func() { sql.Register("decimal-f8", f8Driver{}) })

func (f8Driver) Open(string) (driver.Conn, error) { return f8Conn{}, nil }

type f8Conn struct{}

func (f8Conn) Prepare(string) (driver.Stmt, error) { return f8Stmt{}, nil }
func (f8Conn) Close() error                        { return nil }
func (f8Conn) Begin() (driver.Tx, error)           { return nil, errors.New("f8: no transactions") }
func (f8Conn) CheckNamedValue(nv *driver.NamedValue) error {
	if _, ok := nv.Value.(interface {
		Decompose([]byte) (byte, bool, []byte, int32)
	}); ok {
		return nil
	}
	return driver.ErrSkip
}

type f8Stmt struct{}

func (f8Stmt) Close() error  { return nil }
func (f8Stmt) NumInput() int { return -1 }
func (f8Stmt) Exec([]driver.Value) (driver.Result, error) {
	return driver.RowsAffected(0), nil
}
func (f8Stmt) Query(args []driver.Value) (driver.Rows, error) {
	row := make([]driver.Value, len(args))
	for i, v := range args {
		if s, ok := v.(string); ok {
			v = []byte(s)
		}
		row[i] = v
	}
	return &f8Rows{row: row}, nil
}

type f8Rows struct {
	row  []driver.Value
	done bool
}

func (r *f8Rows) Columns() []string { return []string{"v"} }
func (r *f8Rows) Close() error      { return nil }
func (r *f8Rows) Next(dest []driver.Value) error {
	if r.done {
		return io.EOF
	}
	r.done = true
	copy(dest, r.row)
	return nil
}

// f8Oracle is the library-independent canonical form of a fixed-point
// corpus entry: the sign, the math/big integer of the digits
// with leading zeros removed and the written scale, zero unsigned.
type f8Oracle struct {
	text        string
	negative    bool
	coefficient *big.Int
	exponent    int32
}

func newF8Oracle(entry string) f8Oracle {
	negative := strings.HasPrefix(entry, "-")
	body := strings.TrimPrefix(entry, "-")
	integral, fraction, _ := strings.Cut(body, ".")
	coefficient, ok := new(big.Int).SetString(integral+fraction, 10)
	if !ok {
		panic("f8 corpus entry " + entry)
	}
	negative = negative && coefficient.Sign() != 0
	digits := coefficient.String()
	if len(digits) <= len(fraction) {
		digits = strings.Repeat("0", len(fraction)-len(digits)+1) + digits
	}
	text := digits
	if len(fraction) > 0 {
		text = digits[:len(digits)-len(fraction)] + "." + digits[len(digits)-len(fraction):]
	}
	if negative {
		text = "-" + text
	}
	return f8Oracle{text: text, negative: negative, coefficient: coefficient, exponent: -int32(len(fraction))}
}

// f8Captured records a decompose value as it arrives back from the driver.
type f8Captured struct {
	form        byte
	negative    bool
	coefficient []byte
	exponent    int32
}

func (c *f8Captured) Scan(src any) error {
	s, ok := src.(interface {
		Decompose([]byte) (byte, bool, []byte, int32)
	})
	if !ok {
		return fmt.Errorf("f8: %T is not a decompose value", src)
	}
	c.form, c.negative, c.coefficient, c.exponent = s.Decompose(nil)
	return nil
}

// f8NullPattern derives the NULL pattern for the null-roundtrip variant
// from the committed seed.
func f8NullPattern(n int) []bool {
	r := newPortfolioRNG()
	valid := make([]bool, n)
	for i := range valid {
		valid[i] = r.Intn(4) != 0
	}
	return valid
}

// f8Corpus returns the F4 fixed2dp values, their oracles and the NULL
// pattern.
func f8Corpus() ([]decimal.Decimal, []f8Oracle, []bool) {
	entries := f4FormatInputs()["fixed2dp"]
	values := make([]decimal.Decimal, len(entries))
	oracles := make([]f8Oracle, len(entries))
	for i, entry := range entries {
		values[i] = decimal.MustParse(entry)
		oracles[i] = newF8Oracle(entry)
	}
	return values, oracles, f8NullPattern(len(entries))
}

func openF8(tb testing.TB) *sql.DB {
	registerF8()
	db, err := sql.Open("decimal-f8", "")
	if err != nil {
		tb.Fatal(err)
	}
	db.SetMaxIdleConns(1)
	return db
}

// f8Accuracy runs one variant's round trip over the corpus against the
// independent oracle and returns got/want strings for the matched-accuracy
// precondition: the driver-side text or decompose tuple, then the
// scanned value's canonical text and validity.
func f8Accuracy(tb testing.TB, db *sql.DB, variant string) (got, want []string) {
	values, oracles, valid := f8Corpus()
	for i, v := range values {
		o := oracles[i]
		switch variant {
		case "valuer-scan":
			var wire []byte
			if err := db.QueryRow("echo", v).Scan(&wire); err != nil {
				tb.Fatal(err)
			}
			var out decimal.Decimal
			if err := db.QueryRow("echo", v).Scan(&out); err != nil {
				tb.Fatal(err)
			}
			got = append(got, string(wire)+" "+out.String())
			want = append(want, o.text+" "+o.text)
		case "sqldecimal-compose":
			var wire f8Captured
			if err := db.QueryRow("echo", decimal.SQLDecimal{Decimal: v}).Scan(&wire); err != nil {
				tb.Fatal(err)
			}
			var out decimal.Decimal
			if err := db.QueryRow("echo", decimal.SQLDecimal{Decimal: v}).Scan(&out); err != nil {
				tb.Fatal(err)
			}
			got = append(got, fmt.Sprintf("%d %t %x %d %s", wire.form, wire.negative, new(big.Int).SetBytes(wire.coefficient), wire.exponent, out.String()))
			want = append(want, fmt.Sprintf("0 %t %x %d %s", o.negative, o.coefficient, o.exponent, o.text))
		case "null-roundtrip":
			arg := decimal.NullDecimal{Decimal: v, Valid: valid[i]}
			var out decimal.NullDecimal
			if err := db.QueryRow("echo", arg).Scan(&out); err != nil {
				tb.Fatal(err)
			}
			got = append(got, fmt.Sprintf("%t %s", out.Valid, out.Decimal.String()))
			if valid[i] {
				want = append(want, "true "+o.text)
			} else {
				want = append(want, "false 0")
			}
		default:
			tb.Fatalf("f8: unknown variant %s", variant)
		}
	}
	return got, want
}

// TestF8FakeDriverRoundTrip pins that the fake driver family is
// deterministic: every F8 variant round-trips the committed-seed corpus
// through the stdlib-only fake driver, twice with identical outputs,
// against the independent canonical-form oracle.
func TestF8FakeDriverRoundTrip(t *testing.T) {
	db := openF8(t)
	defer db.Close()
	for _, variant := range portfolioFamilyVariants["F8Database"] {
		got, want := f8Accuracy(t, db, variant)
		if err := matchedAccuracyError("F8Database/"+variant, got, want); err != nil {
			t.Fatal(err)
		}
		again, _ := f8Accuracy(t, db, variant)
		if strings.Join(again, "\n") != strings.Join(got, "\n") {
			t.Fatalf("F8 %s is not deterministic", variant)
		}
	}
}

// BenchmarkSQLCompose isolates the public Compose operation from database/sql
// bookkeeping. It supplements the F8 round trips; each coefficient
// and cohort is checked against math/big before timing, including the general
// path beyond 16 bytes.
func BenchmarkSQLCompose(b *testing.B) {
	for _, width := range []int{0, 4, 8, 16, 17, 32} {
		b.Run(fmt.Sprintf("bytes%d", width), func(b *testing.B) {
			rng := newPortfolioRNG()
			coefficients := make([][]byte, 256)
			var out decimal.Decimal
			for i := range coefficients {
				coefficient := make([]byte, width)
				for j := range coefficient {
					coefficient[j] = byte(rng.Intn(256))
				}
				coefficients[i] = coefficient
				negative := i%2 != 0
				if err := out.Compose(0, negative, coefficient, -2); err != nil {
					b.Fatal(err)
				}
				want := new(big.Int).SetBytes(coefficient)
				if err := sameCohort(out, negative && want.Sign() != 0, want, -2); err != nil {
					b.Fatalf("input %d: %v (timing void)", i, err)
				}
			}
			b.ReportAllocs()
			b.ResetTimer()
			i := 0
			for b.Loop() {
				if err := out.Compose(0, i%2 != 0, coefficients[i], -2); err != nil {
					b.Fatal(err)
				}
				i = (i + 1) % len(coefficients)
			}
		})
	}
}
