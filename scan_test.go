// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"math/big"
	"math/rand/v2"
	"regexp"
	"strconv"
	"strings"
	"testing"
)

func TestScanGrammar(t *testing.T) {
	for _, tc := range []struct {
		text, integral, fraction string
		exponent                 int32
		negative                 bool
	}{
		{"+5", "5", "", 0, false},
		{".5", "", "5", -1, false},
		{"5.", "5", "", 0, false},
		{"007.0100", "007", "0100", -4, false},
		{"-0.00", "0", "00", -2, true},
		{"2.5e-3", "2", "5", -4, false},
		{"1e999999999", "1", "", 999999999, false},
		{"1E-2147483648", "1", "", -2147483648, false},
		{"1.2E+2147483648", "1", "2", 2147483647, false},
		{"1.23E+2147483649", "1", "23", 2147483647, false},
		{"1.2E-2147483647", "1", "2", -2147483648, false},
	} {
		t.Run(tc.text, func(t *testing.T) {
			p, result := scanDecimal(tc.text)
			want := decimalParts[string]{tc.integral, tc.fraction, int64(tc.exponent), tc.negative}
			if result != scanOK || p != want {
				t.Fatalf("scan = %+v, %v; want %+v, OK", p, result, want)
			}
		})
	}
	for _, text := range []string{"", "+", "-", ".", "e5", " 1", "1 ", "1_000", "1,5", "0x10", "1.2.3", "1e", "1e+", "1e-", "1e2e3", "NaN", "Infinity", "\x001", "١", "1e999999999999x"} {
		if _, result := scanDecimal(text); result != scanSyntax {
			t.Errorf("%q: result %v, want syntax", text, result)
		}
	}
	for _, text := range []string{"1E+2147483648", "1E-2147483649", "1.0E-2147483648", "1E+18446744073709551616", "1e-999999999999999999999"} {
		if _, result := scanDecimal(text); result != scanRange {
			t.Errorf("%q: result %v, want range", text, result)
		}
	}
}

// This oracle uses RE2 for syntax and arbitrary-width binary arithmetic for
// the effective exponent. It shares neither the scanner nor its overflow code.
var decimalGrammarOracle = regexp.MustCompile(`^[+-]?(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?$`)

func scanOracle(s string) (int64, scanResult) {
	if !decimalGrammarOracle.MatchString(s) {
		return 0, scanSyntax
	}
	body, exp := s, "0"
	if i := strings.IndexAny(s, "eE"); i >= 0 {
		body, exp = s[:i], s[i+1:]
	}
	e, ok := new(big.Int).SetString(exp, 10)
	if !ok {
		panic("oracle grammar and integer parser disagree")
	}
	if point := strings.IndexByte(body, '.'); point >= 0 {
		e.Sub(e, big.NewInt(int64(len(body)-point-1)))
	}
	if !e.IsInt64() || e.Int64() < -1<<31 || e.Int64() > 1<<31-1 {
		return 0, scanRange
	}
	return e.Int64(), scanOK
}

func compareScanOracle(t testing.TB, s string) {
	t.Helper()
	exponent, want := scanOracle(s)
	p, got := scanDecimal(s)
	if got != want || got == scanOK && int64(p.exponent) != exponent {
		t.Fatalf("%q: scan %+v/%v, oracle exponent %d/%v", s, p, got, exponent, want)
	}
}

func TestScanOracle(t *testing.T) {
	r := rand.New(rand.NewPCG(20260922, 15))
	const alphabet = "0000000000112233445566778899.eE+-_ x\xff"
	for range 20000 {
		buf := make([]byte, r.IntN(160))
		for i := range buf {
			buf[i] = alphabet[r.IntN(len(alphabet))]
		}
		compareScanOracle(t, string(buf))
	}
	for _, e := range []string{"2147483647", "2147483648", "2147483649", "-2147483648", "-2147483647", "99999999999999999999", "000000000000000000000000000001"} {
		for fraction := range 20 {
			compareScanOracle(t, "123."+strings.Repeat("7", fraction)+"e"+e)
		}
	}
}

func TestScanBoundedWork(t *testing.T) {
	for _, tc := range []struct {
		text string
		want scanResult
	}{
		{strings.Repeat("9", 1000000), scanOK},
		{"1e" + strings.Repeat("0", 1000000) + "1", scanOK},
		{"1e" + strings.Repeat("9", 1000000), scanRange},
		{"1e" + strings.Repeat("9", 1000000) + "x", scanSyntax},
	} {
		if _, got := scanDecimal(tc.text); got != tc.want {
			t.Fatalf("input length %d: result %v, want %v", len(tc.text), got, tc.want)
		}
		if n := testing.AllocsPerRun(10, func() { scanDecimal(tc.text) }); n != 0 {
			t.Fatalf("scanner allocated %v times for input length %d", n, len(tc.text))
		}
	}
}

func FuzzScanDecimal(f *testing.F) {
	for _, s := range []string{"", "007.0100", "1.2E+2147483648", "1e999999999", "-0.00", "1E-2147483649", "1e999999999999x"} {
		f.Add(s)
	}
	f.Fuzz(func(t *testing.T, s string) {
		// Bound the independent big.Int oracle, not the production scanner.
		if len(s) > 4096 {
			scanDecimal(s)
			return
		}
		compareScanOracle(t, s)
	})
}

var scanPartsSink decimalParts[string]
var scanResultSink scanResult

// BenchmarkScanGrammar measures the internal lexical stage only. It does
// not construct a Decimal; public parsing is benchmarked in benchmarks/.
func BenchmarkScanGrammar(b *testing.B) {
	for _, tc := range []struct{ name, text string }{
		{"money6", "1234.56"},
		{"int19", "1234567890123456789"},
		{"digits128", strings.Repeat("9", 128)},
		{"digits1024", strings.Repeat("9", 1024)},
		{"million", strings.Repeat("9", 1000000)},
		{"largeExponent", "1.2E+2147483648"},
	} {
		b.Run(tc.name, func(b *testing.B) {
			compareScanOracle(b, tc.text)
			b.ReportAllocs()
			b.SetBytes(int64(len(tc.text)))
			for b.Loop() {
				scanPartsSink, scanResultSink = scanDecimal(tc.text)
			}
		})
	}
}

// BenchmarkScanExponentLength measures scan work without constructing an
// exponent-sized value or including input construction in the timed loop.
func BenchmarkScanExponentLength(b *testing.B) {
	for _, zeros := range [...]int{0, 10, 100, 1_000, 10_000, 100_000, 1_000_000} {
		input := "1e+" + strings.Repeat("0", zeros) + "7"
		b.Run("zeros="+strconv.Itoa(zeros), func(b *testing.B) {
			value, err := Parse(input)
			if err != nil || value.words != (uint128{lo: 1}) || value.exponent() != 7 {
				b.Fatalf("deep exponent %d: got %+v, %v", zeros, value, err)
			}
			b.ReportAllocs()
			b.ResetTimer()
			for b.Loop() {
				value, err := Parse(input)
				if err != nil {
					b.Fatal(err)
				}
				sinkHostile = value
			}
			b.ReportMetric(float64(len(input)), "input-bytes")
		})
	}
}
