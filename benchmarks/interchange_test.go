// SPDX-License-Identifier: Apache-2.0

package benchmarks

import (
	"bytes"
	"encoding/binary"
	"fmt"
	"math/big"
	"strings"
	"testing"

	decimal "github.com/0xCarbon/decimal"
)

// Coefficient interchange A/B: the public fixed-width API
// against the path a consumer takes without it, which goes through
// math/big and text. Rows are named Interchange/<path>/<variant>, with
// path api (NewInt128, NewTwosComplement, AppendTwosComplement) or
// bigint-string (big.Int.SetBytes, then String, then Parse; and the reverse
// for egress). Both paths of a row consume the same 256 committed-seed
// signed cent coefficients of 1 to 19 digits at exponent −2 (so a 16-byte
// value's
// high word is always the sign extension), and every result of each path
// is checked against the math/big oracle before any timing; the two paths therefore agree, which TestInterchangeOracle also
// checks directly.
var interchangeVariants = []string{"int128-in", "twos-complement16-in", "twos-complement16-out"}

// interchangePaths are the compared paths: api is the fixed-width API and
// bigint-string the path without it.
var interchangePaths = []string{"api", "bigint-string"}

var twoTo128 = new(big.Int).Lsh(big.NewInt(1), 128)

// consumerFromLane is the consumer's ingress: a 16-byte big-endian
// two's-complement coefficient read with big.Int.SetBytes, printed with
// String and parsed with the exponent appended.
func consumerFromLane(lane []byte, exponent string) (decimal.Decimal, error) {
	v := new(big.Int).SetBytes(lane)
	if lane[0]&0x80 != 0 {
		v.Sub(v, twoTo128)
	}
	return decimal.Parse(v.String() + exponent)
}

// consumerToLane is the reverse of consumerFromLane for a value at
// exponent −2: String, the digits without the point read with
// big.Int.SetString, and the 16-byte big-endian two's complement.
func consumerToLane(d decimal.Decimal, dst []byte) ([]byte, error) {
	s := d.String()
	v, ok := new(big.Int).SetString(strings.Replace(s, ".", "", 1), 10)
	if !ok || !strings.Contains(s, ".") || len(s)-strings.IndexByte(s, '.') != 3 {
		return nil, fmt.Errorf("%s is not plain text at exponent -2", s)
	}
	if v.Sign() < 0 {
		v.Add(v, twoTo128)
	}
	return v.FillBytes(dst[:16]), nil
}

// interchangeRows builds the rows of one path over the conversion corpus.
func interchangeRows(tb testing.TB, path string) []oracleRow {
	centText, _, _ := conversionCorpora()
	cents := make([]*big.Int, 256)
	lanes := make([][]byte, 256)
	his, los := make([]int64, 256), make([]uint64, 256)
	values := make([]decimal.Decimal, 256)
	for i, c := range centText {
		v, ok := new(big.Int).SetString(c, 10)
		if !ok {
			tb.Fatalf("big.Int(%q)", c)
		}
		cents[i] = v
		lanes[i] = twosComplement128(v)
		his[i] = int64(binary.BigEndian.Uint64(lanes[i][:8]))
		los[i] = binary.BigEndian.Uint64(lanes[i][8:])
		values[i] = decimal.MustParse(c + "E-2")
	}
	cohort := func(got decimal.Decimal, i int) error {
		return sameCohort(got, cents[i].Sign() < 0, new(big.Int).Abs(cents[i]), -2)
	}
	scratch := make([]byte, 16)
	int128In := func(i int) (decimal.Decimal, error) {
		if path == "api" {
			return decimal.NewInt128(his[i], los[i], -2), nil
		}
		var lane [16]byte
		binary.BigEndian.PutUint64(lane[:8], uint64(his[i]))
		binary.BigEndian.PutUint64(lane[8:], los[i])
		return consumerFromLane(lane[:], "E-2")
	}
	twosIn := func(i int) (decimal.Decimal, error) {
		if path == "api" {
			return decimal.NewTwosComplement(lanes[i], binary.BigEndian, -2)
		}
		return consumerFromLane(lanes[i], "E-2")
	}
	twosOut := func(i int) ([]byte, error) {
		if path == "api" {
			return values[i].AppendTwosComplement(scratch[:0], 16, binary.BigEndian)
		}
		return consumerToLane(values[i], scratch)
	}
	ingress := func(f func(int) (decimal.Decimal, error)) func() error {
		return func() error {
			return eachEntry(256, func(i int) error {
				got, err := f(i)
				if err != nil {
					return err
				}
				return cohort(got, i)
			})
		}
	}
	return []oracleRow{
		{
			variant: "int128-in", size: 256, check: ingress(int128In),
			run: func(i int) (err error) { sinkDecimal, err = int128In(i); return },
		},
		{
			variant: "twos-complement16-in", size: 256, check: ingress(twosIn),
			run: func(i int) (err error) { sinkDecimal, err = twosIn(i); return },
		},
		{
			variant: "twos-complement16-out", size: 256,
			check: func() error {
				return eachEntry(256, func(i int) error {
					got, err := twosOut(i)
					if err != nil {
						return err
					}
					if !bytes.Equal(got, lanes[i]) {
						return fmt.Errorf("got %x, math/big %x", got, lanes[i])
					}
					return nil
				})
			},
			run: func(i int) (err error) { sinkBytes, err = twosOut(i); return },
		},
	}
}

// TestInterchangeOracle checks both paths of every interchange row against
// the math/big oracle over the whole corpus, and the paths against each
// other, as the timed runs do before timing (the corpus holds negative, positive, one-digit and 19-digit
// coefficients).
func TestInterchangeOracle(t *testing.T) {
	for _, path := range interchangePaths {
		testOracleRows(t, interchangeRows(t, path), interchangeVariants)
	}
	api, consumer := interchangeRows(t, "api"), interchangeRows(t, "bigint-string")
	for r := range 2 {
		for i := range 256 {
			if err := api[r].run(i); err != nil {
				t.Fatal(err)
			}
			a := sinkDecimal
			if err := consumer[r].run(i); err != nil {
				t.Fatal(err)
			}
			if a.String() != sinkDecimal.String() || a.Exponent() != sinkDecimal.Exponent() {
				t.Fatalf("%s entry %d: api %s, bigint-string %s", interchangeVariants[r], i, a, sinkDecimal)
			}
		}
	}
	centText, _, _ := conversionCorpora()
	var neg, one, long bool
	for _, c := range centText {
		neg = neg || strings.HasPrefix(c, "-")
		one = one || len(strings.TrimPrefix(c, "-")) == 1
		long = long || len(strings.TrimPrefix(c, "-")) == 19
	}
	if !neg || !one || !long {
		t.Fatalf("corpus lacks a negative (%t), one-digit (%t) or 19-digit (%t) coefficient", neg, one, long)
	}
}

// BenchmarkInterchange times Interchange/<path>/<variant> after each row's
// check. For an A/B comparison run each path in its own invocation (-test.bench '^BenchmarkInterchange$/^<path>$/') in ABBA order.
func BenchmarkInterchange(b *testing.B) {
	for _, path := range interchangePaths {
		b.Run(path, func(b *testing.B) {
			for _, row := range interchangeRows(b, path) {
				if err := row.check(); err != nil {
					b.Fatalf("%s/%s: %v (timing void)", path, row.variant, err)
				}
				b.Run(row.variant, func(b *testing.B) {
					b.ReportAllocs()
					i := 0
					for b.Loop() {
						if err := row.run(i); err != nil {
							b.Fatal(err)
						}
						if i++; i == row.size {
							i = 0
						}
					}
				})
			}
		})
	}
}
