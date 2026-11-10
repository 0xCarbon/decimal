// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"bytes"
	"errors"
	"fmt"
	"math"
	"math/big"
	"math/rand"
	randv2 "math/rand/v2"
	"reflect"
	"slices"
	"strconv"
	"strings"
	"sync"
	"testing"
)

func TestDisplaySignaturesAndVectors(t *testing.T) {
	var _ func(Decimal, uint64) (string, error) = Decimal.Fixed
	var _ func(Decimal, uint64, DisplayOptions) (string, error) = Decimal.FixedWithOptions
	var _ func(Decimal, uint64) (string, error) = Decimal.Scientific
	var _ func(Decimal, uint64, DisplayOptions) (string, error) = Decimal.ScientificWithOptions
	var _ func(Decimal) (string, error) = Decimal.Engineering
	var _ func(Decimal, Budget) (string, error) = Decimal.EngineeringWithBudget
	var _ fmt.Formatter = Decimal{}
	for _, tc := range []struct {
		name string
		call func() (string, error)
		want string
	}{
		{"fixed even", func() (string, error) { return MustParse("1.005").Fixed(2) }, "1.00"},
		{"fixed away", func() (string, error) {
			return MustParse("1.005").FixedWithOptions(2, DisplayOptions{Mode: TiesAwayFromZero})
		}, "1.01"},
		{"fixed integral", func() (string, error) { return MustParse("12.5").Fixed(0) }, "12"},
		{"fixed carry", func() (string, error) { return MustParse("999.995").Fixed(2) }, "1000.00"},
		{"scientific", func() (string, error) { return MustParse("1234.5").Scientific(3) }, "1.23E+3"},
		{"scientific carry", func() (string, error) { return MustParse("9.995").Scientific(3) }, "1.00E+1"},
		{"scientific zero one", func() (string, error) { return New(0, 17).Scientific(1) }, "0E+0"},
		{"scientific zeros", func() (string, error) { return New(0, 17).Scientific(4) }, "0.000E+0"},
		{"engineering", func() (string, error) { return MustParse("12345").Engineering() }, "12.345E+3"},
		{"engineering cohort", func() (string, error) { return New(1, 2).Engineering() }, "100E+0"},
		{"engineering negative exponent", func() (string, error) { return New(1, -1).Engineering() }, "100E-3"},
		{"engineering zero", func() (string, error) { return New(0, -9).Engineering() }, "0E+0"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got, err := tc.call()
			if err != nil || got != tc.want {
				t.Fatalf("got %q, %v; want %q", got, err, tc.want)
			}
		})
	}
	d := MustParse("1.005")
	for _, call := range []func() (string, error){func() (string, error) { return d.Fixed(2) }, func() (string, error) { return d.FixedWithOptions(2, DisplayOptions{}) }} {
		if got, err := call(); err != nil || got != "1.00" {
			t.Fatalf("shared Fixed policy: %q %v", got, err)
		}
	}
	for _, call := range []func() (string, error){func() (string, error) { return d.Scientific(3) }, func() (string, error) { return d.ScientificWithOptions(3, DisplayOptions{}) }} {
		if got, err := call(); err != nil || got != "1.00E+0" {
			t.Fatalf("shared Scientific policy: %q %v", got, err)
		}
	}
	a, ea := d.Engineering()
	b, eb := d.EngineeringWithBudget(Budget{})
	if ea != nil || eb != nil || a != b {
		t.Fatalf("shared Engineering policy: %q %v; %q %v", a, ea, b, eb)
	}
}

func displayCheckError(t *testing.T, got string, err error, op string, cause error) {
	t.Helper()
	var display *Error
	if got != "" || !errors.Is(err, cause) || !errors.As(err, &display) || display.Op != op {
		t.Fatalf("got %q, %v; want empty *Error{%s,%v}", got, err, op, cause)
	}
}

func TestDisplayErrorsAndPrecedence(t *testing.T) {
	d := MustParse("1.005")
	got, err := d.FixedWithOptions(2, DisplayOptions{Mode: Exact})
	displayCheckError(t, got, err, "FixedWithOptions", ErrInexact)
	got, err = d.ScientificWithOptions(3, DisplayOptions{Mode: Exact})
	displayCheckError(t, got, err, "ScientificWithOptions", ErrInexact)
	got, err = d.FixedWithOptions(math.MaxUint64, DisplayOptions{Mode: RoundingMode(255), Budget: Budget{MaxWork: 1}})
	displayCheckError(t, got, err, "FixedWithOptions", ErrInvalidContext)
	got, err = d.Scientific(0)
	displayCheckError(t, got, err, "Scientific", ErrInvalidContext)
	got, err = d.FixedWithOptions(math.MaxUint64, DisplayOptions{Mode: Exact, Budget: Budget{MaxWork: 1}})
	displayCheckError(t, got, err, "FixedWithOptions", ErrInsufficientStorage)
	got, err = d.FixedWithOptions(2, DisplayOptions{Mode: Exact, Budget: Budget{MaxOutputBytes: 4}})
	displayCheckError(t, got, err, "FixedWithOptions", ErrInexact)
	got, err = d.FixedWithOptions(2, DisplayOptions{Mode: Exact, Budget: Budget{MaxOutputBytes: 3}})
	displayCheckError(t, got, err, "FixedWithOptions", ErrInsufficientStorage)
	if got, err := MustParse("1.000").FixedWithOptions(2, DisplayOptions{Mode: Exact}); err != nil || got != "1.00" {
		t.Fatalf("zero-only Exact cut: %q %v", got, err)
	}
	var nilError *Error
	for _, e := range []*Error{nilError, {}} {
		if e.Error() == "" || e.Unwrap() != nil {
			t.Fatalf("total error: %#v", e)
		}
	}
}

func TestDisplayBudgetBoundaries(t *testing.T) {
	d := New(-12345, -2) // N=5, Fixed(2) output L=7, W=12.
	for _, tc := range []struct {
		budget    Budget
		wantError bool
	}{
		{Budget{MaxOutputBytes: 6}, true},
		{Budget{MaxOutputBytes: 7}, false},
		{Budget{MaxWork: 4}, true},
		{Budget{MaxWork: 5}, true},
		{Budget{MaxWork: 11}, true},
		{Budget{MaxWork: 12}, false},
	} {
		got, err := d.FixedWithOptions(2, DisplayOptions{Budget: tc.budget})
		if tc.wantError {
			displayCheckError(t, got, err, "FixedWithOptions", ErrInsufficientStorage)
		} else if err != nil || got != "-123.45" {
			t.Fatalf("budget %+v: %q %v", tc.budget, got, err)
		}
	}
	got, err := New(1, math.MinInt32).FixedWithOptions(math.MaxUint64, DisplayOptions{Budget: Budget{MaxOutputBytes: 32}})
	displayCheckError(t, got, err, "FixedWithOptions", ErrInsufficientStorage)
	got, err = New(1, math.MaxInt32).FixedWithOptions(0, DisplayOptions{Budget: Budget{MaxOutputBytes: 32}})
	displayCheckError(t, got, err, "FixedWithOptions", ErrInsufficientStorage)
	for _, tc := range []struct {
		name string
		call func(Budget) (string, error)
		want string
	}{
		{"ScientificWithOptions", func(b Budget) (string, error) {
			return New(12345, -2).ScientificWithOptions(5, DisplayOptions{Budget: b})
		}, "1.2345E+2"},
		{"EngineeringWithBudget", func(b Budget) (string, error) { return New(12345, -2).EngineeringWithBudget(b) }, "123.45E+0"},
	} {
		length := uint64(len(tc.want))
		for _, budget := range []Budget{{MaxOutputBytes: length - 1}, {MaxWork: length + 4}} {
			got, err := tc.call(budget)
			displayCheckError(t, got, err, tc.name, ErrInsufficientStorage)
		}
		for _, budget := range []Budget{{MaxOutputBytes: length}, {MaxWork: length + 5}} {
			got, err := tc.call(budget)
			if err != nil || got != tc.want {
				t.Fatalf("%s budget %+v: %q %v", tc.name, budget, got, err)
			}
		}
	}
	long := MustParse(strings.Repeat("1234567890", 1_000))
	got, err = long.ScientificWithOptions(1, DisplayOptions{Budget: Budget{MaxWork: 9_999}})
	displayCheckError(t, got, err, "ScientificWithOptions", ErrInsufficientStorage)
	got, err = long.EngineeringWithBudget(Budget{MaxWork: 9_999})
	displayCheckError(t, got, err, "EngineeringWithBudget", ErrInsufficientStorage)
}

func TestDisplayRoundModesAgainstBigRat(t *testing.T) {
	// The oracle uses rational arithmetic, independent of coefficient limbs.
	for _, mode := range []RoundingMode{TiesToEven, TiesAwayFromZero, TiesTowardZero, TowardZero, AwayFromZero, TowardPositiveInfinity, TowardNegativeInfinity, Exact} {
		for _, negative := range []bool{false, true} {
			for _, digits := range []string{"124", "125", "1251", "126"} {
				source := digits
				if negative {
					source = "-" + source
				}
				d := MustParse(source + "E-" + strconv.Itoa(len(digits)))
				want, exact := displayRatFixedOracle(t, source, -len(digits), 2, mode)
				got, err := d.FixedWithOptions(2, DisplayOptions{Mode: mode})
				if !exact {
					displayCheckError(t, got, err, "FixedWithOptions", ErrInexact)
				} else if err != nil || got != want {
					t.Fatalf("%s mode %d: %q %v, want %q", source, mode, got, err, want)
				}
			}
		}
	}
}

func TestDisplayFixedRoundsFromEmptyQuotient(t *testing.T) {
	for _, tc := range []struct {
		input      string
		fractional uint64
		mode       RoundingMode
		want       string
	}{
		{"0.9", 0, TiesToEven, "1"},
		{"-0.9", 0, TiesToEven, "-1"},
		{"0.06", 1, TiesToEven, "0.1"},
		{"-0.06", 1, TiesToEven, "-0.1"},
		{"0.01", 0, AwayFromZero, "1"},
		{"-0.01", 0, TowardNegativeInfinity, "-1"},
		{"-0.01", 0, TowardPositiveInfinity, "0"},
	} {
		got, err := MustParse(tc.input).FixedWithOptions(tc.fractional, DisplayOptions{Mode: tc.mode})
		if err != nil || got != tc.want {
			t.Fatalf("%s mode %d: %q %v, want %q", tc.input, tc.mode, got, err, tc.want)
		}
	}
}

func displayRatFixedOracle(t *testing.T, coefficient string, exponent, fractional int, mode RoundingMode) (string, bool) {
	t.Helper()
	q, exact := displayRatRoundedInteger(t, coefficient, exponent+fractional, mode)
	if !exact {
		return "", false
	}
	return displayOracleFixedInteger(q, fractional), true
}

func displayOracleFixedInteger(q *big.Int, fractional int) string {
	negative := q.Sign() < 0
	digits := new(big.Int).Abs(q).String()
	for len(digits) <= fractional {
		digits = "0" + digits
	}
	if fractional > 0 {
		digits = digits[:len(digits)-fractional] + "." + digits[len(digits)-fractional:]
	}
	if negative {
		digits = "-" + digits
	}
	return digits
}

func TestDisplayScientificModesAgainstBigRat(t *testing.T) {
	for _, mode := range []RoundingMode{TiesToEven, TiesAwayFromZero, TiesTowardZero, TowardZero, AwayFromZero, TowardPositiveInfinity, TowardNegativeInfinity, Exact} {
		for _, negative := range []bool{false, true} {
			for _, coefficient := range []string{"124", "125", "1251", "126", "9995", "1000"} {
				source := coefficient
				if negative {
					source = "-" + source
				}
				d := MustParse(source + "E-" + strconv.Itoa(len(coefficient)))
				want, exact := displayRatScientificOracle(t, source, -len(coefficient), 2, mode)
				got, err := d.ScientificWithOptions(2, DisplayOptions{Mode: mode})
				if !exact {
					displayCheckError(t, got, err, "ScientificWithOptions", ErrInexact)
				} else if err != nil || got != want {
					t.Fatalf("%s mode %d: %q %v, want %q", source, mode, got, err, want)
				}
			}
		}
	}
}

func TestDisplayRandomSmallAgainstBigRat(t *testing.T) {
	rng := rand.New(rand.NewSource(23))
	for i := range 160 {
		coefficient := strconv.FormatInt(rng.Int63n(9_999_999_999_999_999)+1, 10)
		if i%2 != 0 {
			coefficient = "-" + coefficient
		}
		exponent := rng.Intn(27) - 13
		fractional := rng.Intn(7)
		precision := rng.Intn(9) + 1
		d := MustParse(coefficient + "E" + strconv.Itoa(exponent))
		for _, mode := range []RoundingMode{TiesToEven, TiesAwayFromZero, TiesTowardZero, TowardZero, AwayFromZero, TowardPositiveInfinity, TowardNegativeInfinity, Exact} {
			wantFixed, exactFixed := displayRatFixedOracle(t, coefficient, exponent, fractional, mode)
			gotFixed, fixedErr := d.FixedWithOptions(uint64(fractional), DisplayOptions{Mode: mode})
			if !exactFixed {
				displayCheckError(t, gotFixed, fixedErr, "FixedWithOptions", ErrInexact)
			} else if fixedErr != nil || gotFixed != wantFixed {
				t.Fatalf("case %d fixed %sE%d f=%d mode=%d: %q %v, want %q", i, coefficient, exponent, fractional, mode, gotFixed, fixedErr, wantFixed)
			}
			wantScientific, exactScientific := displayRatScientificOracle(t, coefficient, exponent, precision, mode)
			gotScientific, scientificErr := d.ScientificWithOptions(uint64(precision), DisplayOptions{Mode: mode})
			if !exactScientific {
				displayCheckError(t, gotScientific, scientificErr, "ScientificWithOptions", ErrInexact)
			} else if scientificErr != nil || gotScientific != wantScientific {
				t.Fatalf("case %d scientific %sE%d p=%d mode=%d: %q %v, want %q", i, coefficient, exponent, precision, mode, gotScientific, scientificErr, wantScientific)
			}
		}
	}
}

func displayRatScientificOracle(t *testing.T, coefficient string, exponent, precision int, mode RoundingMode) (string, bool) {
	t.Helper()
	abs := strings.TrimPrefix(coefficient, "-")
	adjusted := len(abs) - 1 + exponent
	scale := precision - 1 - adjusted
	q, exact := displayRatRoundedInteger(t, coefficient, exponent+scale, mode)
	if !exact {
		return "", false
	}
	digits := new(big.Int).Abs(q).String()
	if len(digits) > precision {
		q.Quo(q, big.NewInt(10))
		adjusted++
		digits = new(big.Int).Abs(q).String()
	}
	for len(digits) < precision {
		digits = "0" + digits
	}
	if precision > 1 {
		digits = digits[:1] + "." + digits[1:]
	}
	sign := "+"
	if adjusted < 0 {
		sign = "-"
		adjusted = -adjusted
	}
	if q.Sign() < 0 {
		digits = "-" + digits
	}
	return digits + "E" + sign + strconv.Itoa(adjusted), true
}

func displayRatRoundedInteger(t *testing.T, coefficient string, exponent int, mode RoundingMode) (*big.Int, bool) {
	t.Helper()
	c, ok := new(big.Int).SetString(coefficient, 10)
	if !ok {
		t.Fatal(coefficient)
	}
	r := new(big.Rat).SetInt(c)
	if exponent < 0 {
		r.Quo(r, new(big.Rat).SetInt(new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(-exponent)), nil)))
	}
	if exponent > 0 {
		r.Mul(r, new(big.Rat).SetInt(new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(exponent)), nil)))
	}
	q, rem := new(big.Int).QuoRem(r.Num(), r.Denom(), new(big.Int))
	if rem.Sign() == 0 {
		return q, true
	}
	if mode == Exact {
		return nil, false
	}
	negative := r.Sign() < 0
	cmp := new(big.Int).Lsh(new(big.Int).Abs(rem), 1).Cmp(r.Denom())
	up := false
	switch mode {
	case AwayFromZero:
		up = true
	case TowardPositiveInfinity:
		up = !negative
	case TowardNegativeInfinity:
		up = negative
	case TiesToEven:
		up = cmp > 0 || cmp == 0 && q.Bit(0) == 1
	case TiesAwayFromZero:
		up = cmp >= 0
	case TiesTowardZero:
		up = cmp > 0
	}
	if up {
		if negative {
			q.Sub(q, big.NewInt(1))
		} else {
			q.Add(q, big.NewInt(1))
		}
	}
	return q, true
}

func TestDisplayFmtTable(t *testing.T) {
	d := MustParse("1234.5")
	for _, tc := range []struct{ format, want string }{
		{"%v", "1234.5"}, {"%s", "1234.5"}, {"%f", "1234.5"}, {"%.2f", "1234.50"},
		{"%e", "1.2345E+3"}, {"%.3e", "1.23E+3"}, {"%.0e", "%!decimal(invalid precision)"},
		{"%10.3e", "   1.23E+3"}, {"%-10.3e", "1.23E+3   "},
		{"%+f", "%!decimal(unsupported format)"}, {"%#e", "%!decimal(unsupported format)"},
		{"% f", "%!decimal(unsupported format)"}, {"%0f", "%!decimal(unsupported format)"},
		{"%+10f", "%!decimal(unsupported format)"}, {"%#v", `decimal.MustParse("1234.5")`},
		{"%.2v", "%!decimal(unsupported format)"}, {"%.2s", "%!decimal(unsupported format)"},
		{"%10.0e", "%!decimal(invalid precision)"}, {"%g", "%!decimal(unsupported format)"},
		{"%q", "%!decimal(unsupported format)"},
	} {
		if got := fmt.Sprintf(tc.format, d); got != tc.want {
			t.Errorf("%q: %q, want %q", tc.format, got, tc.want)
		}
	}
	if got := fmt.Sprintf("%f", New(1, 2)); got != "100" {
		t.Errorf("positive exponent %%f: %q", got)
	}
	if got := fmt.Sprintf("%f", MustParse("1.10")); got != "1.10" {
		t.Errorf("own-scale %%f: %q", got)
	}
	if got := fmt.Sprintf("%e", MustParse("1.2300")); got != "1.2300E+0" {
		t.Errorf("cohort %%e: %q", got)
	}
	if got := fmt.Sprintf("%v", New(1, math.MaxInt32)); !strings.HasPrefix(got, "1E+") {
		t.Errorf("canonical %%v: %q", got)
	}
}

func TestDisplayEngineeringNumericAndImmutable(t *testing.T) {
	for _, d := range []Decimal{New(1, 2), New(1, -1), MustParse("12345"), MustParse("-123.4500"), New(1, math.MinInt32), New(1, math.MaxInt32)} {
		got, err := d.Engineering()
		if err != nil {
			t.Fatal(err)
		}
		// Endpoint outputs can have a wide exponent and may not be reparsable into int32.
		if d.exponent() != math.MinInt32 && d.exponent() != math.MaxInt32 {
			parsed, err := Parse(got)
			if err != nil || !parsed.Equal(d) {
				t.Fatalf("engineering %q -> %q -> %v, %v", d, got, parsed, err)
			}
		}
	}
	limbs := []uint32{123456789, 123456789, 123456789, 123456789, 123456789}
	d := slowDecimal(&slowCoefficient{limbs: limbs}, -2, true)
	before := append([]uint32(nil), limbs...)
	for _, call := range []func() (string, error){d.Engineering, func() (string, error) { return d.Fixed(2) }, func() (string, error) { return d.Scientific(20) }} {
		if _, err := call(); err != nil {
			t.Fatal(err)
		}
	}
	if !reflect.DeepEqual(limbs, before) {
		t.Fatal("display mutated published limbs")
	}
	for _, tc := range []struct {
		d                       Decimal
		scientific, engineering string
	}{
		{New(1, math.MaxInt32), "1E+2147483647", "10E+2147483646"},
		{New(1, math.MinInt32), "1E-2147483648", "10E-2147483649"},
	} {
		if got, err := tc.d.Scientific(1); err != nil || got != tc.scientific {
			t.Fatalf("endpoint Scientific: %q %v, want %q", got, err, tc.scientific)
		}
		if got, err := tc.d.Engineering(); err != nil || got != tc.engineering {
			t.Fatalf("endpoint Engineering: %q %v, want %q", got, err, tc.engineering)
		}
	}
}

func TestDisplayLongCoefficientsAndCarryWidths(t *testing.T) {
	for _, n := range []int{38, 39, 40} {
		d := MustParse(strings.Repeat("9", n) + "E-" + strconv.Itoa(n-1))
		if got, err := d.Fixed(0); err != nil || got != "10" {
			t.Fatalf("%d-digit fixed carry: %q %v", n, got, err)
		}
		want := "1." + strings.Repeat("0", n-2) + "E+1"
		if got, err := d.Scientific(uint64(n - 1)); err != nil || got != want {
			t.Fatalf("%d-digit scientific carry: %q %v, want %q", n, got, err, want)
		}
	}
	for _, n := range []int{1_000, 10_000} {
		coefficient := strings.Repeat("1234567890", n/10)
		d := MustParse(coefficient)
		if got, err := d.Fixed(0); err != nil || got != coefficient {
			t.Fatalf("%d-digit Fixed: length %d, %v", n, len(got), err)
		}
		want := coefficient[:1] + "." + coefficient[1:] + "E+" + strconv.Itoa(n-1)
		if got, err := d.Scientific(uint64(n)); err != nil || got != want {
			t.Fatalf("%d-digit Scientific: length %d, %v", n, len(got), err)
		}
		got, err := d.Engineering()
		if err != nil {
			t.Fatal(err)
		}
		parsed, err := Parse(got)
		if err != nil || !parsed.Equal(d) {
			t.Fatalf("%d-digit Engineering: length %d, %v", n, len(got), err)
		}
	}
}

func TestDisplayConcurrentSharedReaders(t *testing.T) {
	d := MustParse(strings.Repeat("1234567890", 100))
	before, err := d.Text(0)
	if err != nil {
		t.Fatal(err)
	}
	var wg sync.WaitGroup
	errorsSeen := make(chan error, 24)
	for range 24 {
		wg.Go(func() {
			for range 20 {
				if s, err := d.Fixed(0); err != nil || s != before {
					errorsSeen <- fmt.Errorf("Fixed: %d bytes, %v", len(s), err)
					return
				}
				if s, err := d.Scientific(10); err != nil || s != "1.234567890E+999" {
					errorsSeen <- fmt.Errorf("Scientific: %q, %v", s, err)
					return
				}
				if _, err := d.Engineering(); err != nil {
					errorsSeen <- err
					return
				}
			}
		})
	}
	wg.Wait()
	close(errorsSeen)
	for err := range errorsSeen {
		t.Error(err)
	}
	if after, err := d.Text(0); err != nil || after != before {
		t.Fatalf("shared Decimal changed: %v", err)
	}
}

type displayTestState struct {
	width, precision             int
	hasWidth, hasPrecision, left bool
	stop                         bool
	writes                       int
	first                        []byte
	body                         strings.Builder
}

func (s *displayTestState) Width() (int, bool)     { return s.width, s.hasWidth }
func (s *displayTestState) Precision() (int, bool) { return s.precision, s.hasPrecision }
func (s *displayTestState) Flag(c int) bool        { return c == '-' && s.left }
func (s *displayTestState) Write(p []byte) (int, error) {
	s.writes++
	if s.writes == 1 {
		s.first = append([]byte(nil), p...)
	}
	if s.stop {
		return 0, errors.New("stop")
	}
	return s.body.Write(p)
}

func TestDisplayFmtWidthPreflightAndWriteStop(t *testing.T) {
	for _, tc := range []struct {
		width int
		left  bool
		want  string
	}{
		{2, false, "123"}, {2, true, "123"},
		{3, false, "123"}, {3, true, "123"}, {4, false, " 123"}, {4, true, "123 "},
	} {
		state := &displayTestState{width: tc.width, hasWidth: true, left: tc.left}
		New(123, 0).Format(state, 'f')
		if got := state.body.String(); got != tc.want {
			t.Fatalf("width %d left %v: %q, want %q", tc.width, tc.left, got, tc.want)
		}
	}
	stopped := &displayTestState{width: math.MaxInt, hasWidth: true, stop: true}
	New(1, 0).Format(stopped, 'f')
	if stopped.writes != 1 || len(stopped.first) != 4096 || strings.Trim(string(stopped.first), " ") != "" {
		t.Fatalf("extreme width should stop after first bounded padding write: writes=%d first=%d", stopped.writes, len(stopped.first))
	}
	refused := &displayTestState{precision: math.MaxInt, hasPrecision: true, width: 20, hasWidth: true}
	New(1, 0).Format(refused, 'f')
	if got := refused.body.String(); got != "%!decimal(resource limit)" || refused.writes != 1 {
		t.Fatalf("unaddressable precision: %q writes=%d", got, refused.writes)
	}
}

func TestDisplayBoundedRefusalAllocations(t *testing.T) {
	for _, digits := range []int{1_000, 10_000} {
		d := MustParse(strings.Repeat("1234567890", digits/10))
		allocations := testing.AllocsPerRun(10, func() {
			got, err := d.ScientificWithOptions(1, DisplayOptions{Budget: Budget{MaxWork: 1}})
			if got != "" || !errors.Is(err, ErrInsufficientStorage) {
				panic("missing preflight refusal")
			}
		})
		if allocations > 2 {
			t.Fatalf("%d-digit preflight refusal allocated %.0f objects", digits, allocations)
		}
	}
	allocations := testing.AllocsPerRun(10, func() {
		got, err := New(1, -2).FixedWithOptions(math.MaxUint64, DisplayOptions{Budget: Budget{MaxOutputBytes: 8}})
		if got != "" || !errors.Is(err, ErrInsufficientStorage) {
			panic("missing extreme-size refusal")
		}
	})
	if allocations > 2 {
		t.Fatalf("extreme-size refusal allocated %.0f objects", allocations)
	}
}

// displayCorpusRat is the exact value of a display corpus member, built from
// its digit string with math/big (only for small exponents).
func displayCorpusRat(t *testing.T, d Decimal) *big.Rat {
	t.Helper()
	coefficient, ok := new(big.Int).SetString(d.coefficientDigits(), 10)
	if !ok {
		t.Fatalf("bad coefficient %q", d.coefficientDigits())
	}
	if d.negative() {
		coefficient.Neg(coefficient)
	}
	r := new(big.Rat).SetInt(coefficient)
	scale := new(big.Rat).SetInt(new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(max(d.exponent(), -d.exponent()))), nil))
	if d.exponent() >= 0 {
		return r.Mul(r, scale)
	}
	return r.Quo(r, scale)
}

// TestDisplayDirectivesTotalOverExtremeCorpus checks that formatting is
// total: over zero, one and
// all-nines coefficients of 1 to 200 digits (both storage bands), both signs
// and exponents MinInt32, -1, 0, 4000 (whose plain outputs straddle the
// budget) and MaxInt32, the canonical emitter, every
// display directive in every mode (budgeted at 4096 bytes, places up to
// MaxUint64) and the fmt verbs complete without panic. Each call returns text
// within its budget or a *Error with ErrInsufficientStorage (or
// ErrInexact under Exact); fmt returns text or a %!decimal(...) diagnostic.
// Every successful output parses; Text and Engineering parse back Equal, and
// for small exponents a rounded output lies within one unit of its last
// place of the math/big.Rat value.
func TestDisplayDirectivesTotalOverExtremeCorpus(t *testing.T) {
	const budget = 4096
	var corpus []Decimal
	for _, digits := range []int{0, 1, 19, 20, 38, 39, 200} {
		coefficient := "0"
		if digits > 0 {
			coefficient = strings.Repeat("9", digits)
			if digits == 1 {
				coefficient = "1"
			}
		}
		for _, exponent := range []int32{math.MinInt32, -1, 0, 4000, math.MaxInt32} {
			for _, sign := range []string{"", "-"} {
				if digits == 0 && sign == "-" {
					continue
				}
				d := MustParse(sign + coefficient + "E" + strconv.FormatInt(int64(exponent), 10))
				if d.exponent() != exponent {
					t.Fatalf("corpus %s%sE%d parsed at exponent %d", sign, coefficient, exponent, d.exponent())
				}
				corpus = append(corpus, d)
			}
		}
	}
	var successes, refusals int
	guard := func(what string, d Decimal, run func()) {
		t.Helper()
		defer func() {
			if r := recover(); r != nil {
				t.Fatalf("%s on %sE%d panicked: %v", what, d.coefficientDigits(), d.exponent(), r)
			}
		}()
		run()
	}
	small := func(d Decimal) bool { return d.exponent() > -1000 && d.exponent() < 1000 }
	check := func(what string, d Decimal, out string, err error, mode RoundingMode, reparse bool) {
		t.Helper()
		if err != nil {
			var displayErr *Error
			if !errors.As(err, &displayErr) || out != "" ||
				!errors.Is(err, ErrInsufficientStorage) && !(mode == Exact && errors.Is(err, ErrInexact)) {
				t.Fatalf("%s on %sE%d: %q, %v; want text or an *Error refusal", what, d.coefficientDigits(), d.exponent(), out, err)
			}
			refusals++
			return
		}
		successes++
		if len(out) > budget {
			t.Fatalf("%s on %sE%d returned %d bytes past the %d-byte budget", what, d.coefficientDigits(), d.exponent(), len(out), budget)
		}
		parsed, perr := Parse(out)
		if perr != nil {
			if small(d) || !errors.Is(perr, ErrExponentRange) {
				t.Fatalf("%s on %sE%d emitted unparsable %q: %v", what, d.coefficientDigits(), d.exponent(), out, perr)
			}
			return
		}
		if reparse && !parsed.Equal(d) {
			t.Fatalf("%s on %sE%d emitted %q, a different value", what, d.coefficientDigits(), d.exponent(), out)
		}
		if small(d) {
			ulp := new(big.Rat).SetInt(new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(max(parsed.exponent(), -parsed.exponent()))), nil))
			if parsed.exponent() < 0 {
				ulp.Inv(ulp)
			}
			gap := new(big.Rat).Sub(displayCorpusRat(t, parsed), displayCorpusRat(t, d))
			if gap.Abs(gap).Cmp(ulp) >= 0 {
				t.Fatalf("%s on %sE%d emitted %q, a unit or more from the exact value", what, d.coefficientDigits(), d.exponent(), out)
			}
		}
	}
	limit := Budget{MaxOutputBytes: budget}
	for _, d := range corpus {
		guard("Text/String", d, func() {
			out, err := d.Text(budget)
			check("Text", d, out, err, TiesToEven, true)
			if s := d.String(); err == nil && s != out {
				t.Fatalf("String %q differs from Text %q", s, out)
			}
		})
		guard("EngineeringWithBudget", d, func() {
			out, err := d.EngineeringWithBudget(limit)
			check("EngineeringWithBudget", d, out, err, TiesToEven, true)
		})
		for mode := TiesToEven; mode <= Exact; mode++ {
			options := DisplayOptions{Mode: mode, Budget: limit}
			for _, places := range []uint64{0, 2, 40, 5000, math.MaxUint64} {
				guard("FixedWithOptions", d, func() {
					out, err := d.FixedWithOptions(places, options)
					check(fmt.Sprintf("FixedWithOptions(%d, %v)", places, mode), d, out, err, mode, false)
				})
				if places == 0 {
					places = 1
				}
				guard("ScientificWithOptions", d, func() {
					out, err := d.ScientificWithOptions(places, options)
					check(fmt.Sprintf("ScientificWithOptions(%d, %v)", places, mode), d, out, err, mode, false)
				})
			}
		}
		verbs := []string{"%v", "%s", "%e", "%.3e", "%-30v"}
		if small(d) {
			verbs = append(verbs, "%f", "%.2f", "%5.1f", "%.0e", "%x", "%+v", "%20v", "%q", "%.2v")
		}
		for _, verb := range verbs {
			guard("fmt "+verb, d, func() {
				out := strings.TrimSpace(fmt.Sprintf(verb, d))
				if strings.HasPrefix(out, "%!") {
					if !strings.HasPrefix(out, "%!decimal(") || strings.Contains(out, "PANIC") {
						t.Fatalf("fmt %s on %sE%d: undocumented diagnostic %q", verb, d.coefficientDigits(), d.exponent(), out)
					}
					return
				}
				if _, err := Parse(out); err != nil && (small(d) || !errors.Is(err, ErrExponentRange)) {
					t.Fatalf("fmt %s on %sE%d emitted unparsable %q: %v", verb, d.coefficientDigits(), d.exponent(), out, err)
				}
			})
		}
	}
	t.Logf("corpus %d values: %d successes, %d refusals", len(corpus), successes, refusals)
	if len(corpus) < 50 || successes < 2000 || refusals < 500 {
		t.Fatalf("corpus %d values: %d successes, %d refusals; the totality check is vacuous", len(corpus), successes, refusals)
	}
}

// TestDisplayFixedLeavesValueUnchanged checks that display formatting
// leaves the value unchanged: Fixed has no Conditions result, 1.234 at two
// fractional digits emits the hand-derived 1.23 while the value stays 1.234
// at exponent -3, and a slow-band value keeps its limbs and text through
// every display directive.
func TestDisplayFixedLeavesValueUnchanged(t *testing.T) {
	var _ func(Decimal, uint64) (string, error) = Decimal.Fixed
	d := MustParse("1.234")
	out, err := d.Fixed(2)
	if out != "1.23" || err != nil {
		t.Fatalf("1.234.Fixed(2) = %q, %v; want 1.23", out, err)
	}
	if d.String() != "1.234" || d.exponent() != -3 || d.coefficientDigits() != "1234" {
		t.Fatalf("display changed the value to %s at exponent %d", d, d.exponent())
	}
	slow := MustParse("1.234" + strings.Repeat("5", 40))
	if slow.slow == nil {
		t.Fatal("slow-band witness is inline")
	}
	limbs, text := append([]uint32(nil), slow.slow.limbs...), slow.String()
	for _, call := range []func() (string, error){
		func() (string, error) { return slow.Fixed(2) },
		func() (string, error) { return slow.Scientific(3) },
		slow.Engineering,
		func() (string, error) { return fmt.Sprintf("%.1f", slow), nil },
	} {
		if _, err := call(); err != nil {
			t.Fatal(err)
		}
	}
	if got, _ := slow.Fixed(2); got != "1.23" {
		t.Fatalf("slow Fixed(2) = %q, want 1.23", got)
	}
	if !reflect.DeepEqual(slow.slow.limbs, limbs) || slow.String() != text {
		t.Fatal("display mutated the slow-band value")
	}
}

// f4FixedCorpusForTest replicates the F4 fixed2dp corpus of
// benchmarks/portfolio_test.go (f4FormatInputs, seed 20260918): the plain,
// fixed and scientific draws interleave on one source, so all three are
// drawn to keep the fixed inputs identical.
func f4FixedCorpusForTest() []string {
	r := rand.New(rand.NewSource(20260918))
	digits := func(n int) string {
		b := make([]byte, n)
		for i := range b {
			b[i] = byte('0' + r.Intn(10))
		}
		return string(b)
	}
	suffixes := [...]string{".00", ".12", ".123", ".126", ".125", ".135", ".999", ".995"}
	var fixed []string
	for i := range 256 {
		_ = digits(1 + r.Intn(9)) // plain
		f := digits(1+r.Intn(5)) + suffixes[i%len(suffixes)]
		if i%16 >= 8 {
			f = "-" + f
		}
		fixed = append(fixed, f)
		_ = digits(1) + "." + digits(6) + "E-" + strconv.Itoa(r.Intn(6)) // scientific
	}
	return fixed
}

// fixedRatOracle renders input rounded ties-to-even to places with
// big.Rat quotient and remainder, independently of the library; a value
// that rounds to zero has no sign.
func fixedRatOracle(t *testing.T, input string, places int) string {
	t.Helper()
	value, ok := new(big.Rat).SetString(input)
	if !ok {
		t.Fatalf("oracle input %q", input)
	}
	negative := value.Sign() < 0
	value.Abs(value)
	value.Mul(value, new(big.Rat).SetInt(new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(places)), nil)))
	q, rem := new(big.Int).QuoRem(value.Num(), value.Denom(), new(big.Int))
	if c := new(big.Int).Lsh(rem, 1).Cmp(value.Denom()); c > 0 || c == 0 && q.Bit(0) == 1 {
		q.Add(q, big.NewInt(1))
	}
	if negative && q.Sign() != 0 {
		q.Neg(q)
	}
	return displayOracleFixedInteger(q, places)
}

// allocatedBytes is runtime.MemStats.TotalAlloc across f: the least of
// three cold readings with the collector off. TotalAlloc is process-wide,
// and another goroutine's allocation can only add to a reading.
func allocatedBytes(f func()) uint64 {
	least := uint64(math.MaxUint64)
	for range 3 {
		least = min(least, coldAllocated(f))
	}
	return least
}

var sinkDisplayText string

// TestFixedAllocatesExactBytes checks that Fixed(2)
// over the fixed2dp benchmark corpus allocates what string() copies of the same
// outputs allocate under the same tiny-allocator packing (oracle: the
// TotalAlloc of those copies, measured in this test), and a 4-byte and a
// 5-byte result each cost what an exact string of that length costs. A
// strings.Builder.Grow implementation would round 4- to 8-byte requests up
// to the 8-byte class first.
func TestFixedAllocatesExactBytes(t *testing.T) {
	if testing.Short() {
		t.Skip("allocation accounting runs in the full suite")
	}
	corpus := f4FixedCorpusForTest()
	values := make([]Decimal, len(corpus))
	outputs := make([][]byte, len(corpus))
	for i, input := range corpus {
		values[i] = MustParse(input)
		got, err := values[i].Fixed(2)
		if want := fixedRatOracle(t, input, 2); err != nil || got != want {
			t.Fatalf("Fixed(2) of %q = %q, %v; want %q", input, got, err, want)
		}
		outputs[i] = []byte(got)
	}
	const passes = 400
	// Each tiny-allocator block is 16 bytes; a P change during a pass can
	// strand at most one partly used block, so allow one block per 4096
	// results.
	slack := uint64(16 * (1 + passes*len(values)/4096))
	excess := func(name string, got, want uint64, ops int) {
		t.Helper()
		if got > want+slack {
			t.Errorf("%s: %d bytes (%.3f B/op), exact strings %d bytes (%.3f B/op)",
				name, got, float64(got)/float64(ops), want, float64(want)/float64(ops))
		}
	}
	fixed := allocatedBytes(func() {
		for range passes {
			for _, v := range values {
				sinkDisplayText, _ = v.Fixed(2)
			}
		}
	})
	exact := allocatedBytes(func() {
		for range passes {
			for _, b := range outputs {
				sinkDisplayText = string(b)
			}
		}
	})
	excess("F4 fixed2dp corpus", fixed, exact, passes*len(values))
	for _, tc := range []struct{ input, want string }{{"0.001", "0.00"}, {"12.3449", "12.34"}} {
		v := MustParse(tc.input)
		if got, err := v.Fixed(2); err != nil || got != tc.want || got != fixedRatOracle(t, tc.input, 2) {
			t.Fatalf("Fixed(2) of %q = %q, %v; want %q", tc.input, got, err, tc.want)
		}
		const calls = 4096
		text := []byte(tc.want)
		fixed := allocatedBytes(func() {
			for range calls {
				sinkDisplayText, _ = v.Fixed(2)
			}
		})
		exact := allocatedBytes(func() {
			for range calls {
				sinkDisplayText = string(text)
			}
		})
		excess(strconv.Itoa(len(tc.want))+"-byte result "+tc.want, fixed, exact, calls)
	}
}

// plannedFixed is the general Fixed path: planDisplay plus render.
func plannedFixed(d Decimal, places uint64) (string, error) {
	p, err := d.planDisplay(displayFixed, places, DisplayOptions{}, "Fixed")
	if err != nil {
		return "", err
	}
	return p.render(), nil
}

// TestFixedFastPathMatchesPlanner pins the Fixed fast path to the
// planner (planDisplay plus render) and to the independent big.Rat
// ties-to-even oracle fixedRatOracle, fed coefficient and exponent text
// built with strconv. It covers places 0-19 and the deferring 20 and 25,
// every cut 1-19 and the deferring 20, the plan's tie and sign vectors,
// zero at extreme exponents, 2^64-1, scaled products that leave 64 bits,
// two-word and slow values, and FixedWithOptions, which takes the fast path
// only with zero options. Hit and deferral counts guard against a vacuous
// pass.
func TestFixedFastPathMatchesPlanner(t *testing.T) {
	for _, tc := range []struct {
		input  string
		places uint64
		want   string
	}{
		{"0.125", 2, "0.12"}, {"0.135", 2, "0.14"}, {"0.995", 2, "1.00"}, {"9.995", 2, "10.00"},
		{"0.005", 2, "0.00"}, {"0.015", 2, "0.02"}, {"-0.001", 2, "0.00"}, {"-0.005", 2, "0.00"},
		{"-0.0051", 2, "-0.01"}, {"0E+5", 2, "0.00"}, {"0E+2147483647", 0, "0"}, {"-0E-2147483648", 19, "0.0000000000000000000"},
		{"999.995", 2, "1000.00"}, {"-999.995", 2, "-1000.00"}, {"18446744073709551615", 0, "18446744073709551615"},
		{"1.8446744073709551615", 19, "1.8446744073709551615"}, {"1.8446744073709551615", 0, "2"},
		{"-12.3449", 2, "-12.34"}, {"12.345", 0, "12"}, {"0.5", 0, "0"}, {"1.5", 0, "2"}, {"-2.5", 0, "-2"},
		{"7", 3, "7.000"}, {"-7E+1", 1, "-70.0"}, {"0.00", 2, "0.00"},
	} {
		d := MustParse(tc.input)
		got, err := d.Fixed(tc.places)
		general, generalErr := plannedFixed(d, tc.places)
		if err != nil || got != tc.want || generalErr != nil || general != tc.want || fixedRatOracle(t, tc.input, int(tc.places)) != tc.want {
			t.Fatalf("Fixed(%d) of %s = %q, %v; planner %q, %v; want %q", tc.places, tc.input, got, err, general, generalErr, tc.want)
		}
		if _, ok := d.fixedTiesToEven(tc.places); !ok {
			t.Fatalf("Fixed(%d) of %s deferred; the plan vectors are fast-path inputs", tc.places, tc.input)
		}
	}

	hitsByCut := map[int64]int{}
	var scaled, zeros, roundedToZero, deferred int
	check := func(w uint64, e int32, negative bool, places uint64) {
		t.Helper()
		d := inlineDecimal(uint128{lo: w}, e, negative)
		got, err := d.Fixed(places)
		general, generalErr := plannedFixed(d, places)
		if err != nil || generalErr != nil || got != general {
			t.Fatalf("Fixed(%d) of %v = %q, %v; planner %q, %v", places, d, got, err, general, generalErr)
		}
		withOptions, err := d.FixedWithOptions(places, DisplayOptions{})
		if err != nil || withOptions != general {
			t.Fatalf("FixedWithOptions(%d, zero) of %v = %q, %v; want %q", places, d, withOptions, err, general)
		}
		if shift := int64(e) + int64(places); shift > -64 && shift < 64 {
			source := strconv.FormatUint(w, 10) + "e" + strconv.FormatInt(int64(e), 10)
			if negative {
				source = "-" + source
			}
			if want := fixedRatOracle(t, source, int(places)); got != want {
				t.Fatalf("Fixed(%d) of %s = %q; oracle %q", places, source, got, want)
			}
		}
		fast, ok := d.fixedTiesToEven(places)
		if !ok {
			deferred++
			return
		}
		if fast != general {
			t.Fatalf("fast Fixed(%d) of %v = %q; planner %q", places, d, fast, general)
		}
		switch shift := int64(e) + int64(places); {
		case w == 0:
			zeros++
		case shift >= 0:
			scaled++
		default:
			hitsByCut[-shift]++
			if strings.Trim(fast, "-0.") == "" {
				roundedToZero++
			}
		}
	}
	words := []uint64{0, 1, 4, 5, 6, 9, 15, 25, 35, 45, 51, 995, 9995, 999995, 1 << 63, math.MaxUint64}
	for k := 1; k <= 19; k++ {
		words = append(words, pow10Words[k]-1, pow10Words[k], pow10Words[k]+1, pow10Words[k]/2, 3*pow10Words[k]/2, 5*pow10Words[k]/2)
	}
	placesSet := []uint64{0, 1, 2, 3, 5, 9, 10, 18, 19, 20, 25}
	for _, w := range words {
		for e := int32(-45); e <= 3; e++ {
			for _, places := range placesSet {
				check(w, e, w%2 == 1, places)
			}
		}
		for _, e := range []int32{math.MinInt32, -1000, 1000} {
			check(w, e, true, 2)
		}
	}
	// A nonzero value at the largest exponent would render 2^31 digits; zero
	// renders "0.00" at any exponent.
	for _, e := range []int32{math.MaxInt32, math.MaxInt32 - 20, math.MinInt32} {
		for _, places := range placesSet {
			check(0, e, false, places)
		}
	}
	rng := rand.New(rand.NewSource(81))
	for range 40000 {
		bitLength := 1 + rng.Intn(64)
		w := rng.Uint64()>>(64-bitLength) | 1<<(bitLength-1)
		check(w, int32(rng.Intn(48)-42), rng.Intn(2) == 1, uint64(rng.Intn(21)))
	}
	t.Logf("hits by cut %v; scaled %d, zero %d, rounded to zero %d, deferred %d", hitsByCut, scaled, zeros, roundedToZero, deferred)
	for cut := int64(1); cut <= 19; cut++ {
		if hitsByCut[cut] < 100 {
			t.Fatalf("cut %d has %d fast-path hits", cut, hitsByCut[cut])
		}
	}
	if hitsByCut[20] != 0 || scaled < 1000 || zeros < 100 || roundedToZero < 1000 || deferred < 1000 {
		t.Fatalf("vacuous coverage: cut20 %d, scaled %d, zero %d, rounded to zero %d, deferred %d", hitsByCut[20], scaled, zeros, roundedToZero, deferred)
	}

	// Deferrals: places beyond 19, cuts beyond 19, products beyond 64 bits,
	// two-word and slow coefficients.
	for _, tc := range []struct {
		d      Decimal
		places uint64
	}{
		{New(1, 0), 20}, {New(1, 0), 25}, {New(5, -21), 1}, {New(math.MaxInt64, 0), 2},
		{New(2, 18), 2}, {MustParse("18446744073709551616E-2"), 2}, {asSlowBand(New(12345, -3)), 2},
	} {
		if _, ok := tc.d.fixedTiesToEven(tc.places); ok {
			t.Fatalf("fast path served Fixed(%d) of %v", tc.places, tc.d)
		}
	}

	// A mode or a budget keeps the planner's results and error identities.
	d := MustParse("0.125")
	if got, err := d.FixedWithOptions(2, DisplayOptions{Mode: TiesAwayFromZero}); err != nil || got != "0.13" {
		t.Fatalf("TiesAwayFromZero: %q, %v", got, err)
	}
	got, err := MustParse("1.005").FixedWithOptions(2, DisplayOptions{Mode: Exact})
	displayCheckError(t, got, err, "FixedWithOptions", ErrInexact)
	got, err = MustParse("12.34").FixedWithOptions(2, DisplayOptions{Budget: Budget{MaxOutputBytes: 4}})
	displayCheckError(t, got, err, "FixedWithOptions", ErrInsufficientStorage)
	got, err = MustParse("12.34").FixedWithOptions(2, DisplayOptions{Budget: Budget{MaxWork: 8}})
	displayCheckError(t, got, err, "FixedWithOptions", ErrInsufficientStorage)
	if got, err := MustParse("12.34").FixedWithOptions(2, DisplayOptions{Budget: Budget{MaxOutputBytes: 5, MaxWork: 9}}); err != nil || got != "12.34" {
		t.Fatalf("admitted budget: %q, %v", got, err)
	}
	v := MustParse("-123.456")
	if allocs := testing.AllocsPerRun(100, func() { _, _ = v.Fixed(2) }); allocs != 1 {
		t.Fatalf("Fixed allocates %.0f times, want 1", allocs)
	}
}

// TestDisplayRenderAllocatesExactBytes pins the display render: output of at
// most 64 bytes is built on the stack and converted once, so it costs what
// an exact string() copy of it costs (TotalAlloc oracle measured here), one
// allocation; longer output flushes into a builder sized once and matches
// the big.Rat oracle across the 64-byte chunk boundary.
func TestDisplayRenderAllocatesExactBytes(t *testing.T) {
	if testing.Short() {
		t.Skip("allocation accounting runs in the full suite")
	}
	for _, tc := range []struct {
		name   string
		render func() (string, error)
		want   string
	}{
		{"Engineering", MustParse("12.5E+3").Engineering, "12.5E+3"},
		{"Scientific", func() (string, error) { return MustParse("123456").Scientific(3) }, "1.23E+5"},
		{"Fixed mode", func() (string, error) {
			return MustParse("1.5").FixedWithOptions(1, DisplayOptions{Mode: TiesAwayFromZero})
		}, "1.5"},
		{"Fixed planner", func() (string, error) {
			return MustParse("1.5").display(displayFixed, 1, DisplayOptions{Mode: TiesAwayFromZero}, "FixedWithOptions")
		}, "1.5"},
		{"Engineering planner", func() (string, error) {
			return MustParse("12.5E+3").display(displayEngineering, 0, DisplayOptions{}, "Engineering")
		}, "12.5E+3"},
	} {
		got, err := tc.render()
		if err != nil || got != tc.want {
			t.Fatalf("%s = %q, %v; want %q", tc.name, got, err, tc.want)
		}
		if allocs := testing.AllocsPerRun(100, func() { _, _ = tc.render() }); allocs != 1 {
			t.Fatalf("%s allocates %.0f times, want 1", tc.name, allocs)
		}
		const calls = 4096
		text := []byte(tc.want)
		rendered := allocatedBytes(func() {
			for range calls {
				sinkDisplayText, _ = tc.render()
			}
		})
		exact := allocatedBytes(func() {
			for range calls {
				sinkDisplayText = string(text)
			}
		})
		// The renders above also parse; only the rendered text allocates.
		if rendered > exact+64 {
			t.Fatalf("%s: %d bytes, exact strings %d", tc.name, rendered, exact)
		}
	}
	d := MustParse("-12345.678")
	for places := uint64(40); places <= 140; places++ {
		got, err := d.Fixed(places)
		if want := fixedRatOracle(t, "-12345.678", int(places)); err != nil || got != want {
			t.Fatalf("Fixed(%d) = %q, %v; want %q", places, got, err, want)
		}
	}
	long := MustParse("1" + strings.Repeat("0", 70) + "1")
	for digits := uint64(55); digits <= 75; digits++ {
		got, err := long.Scientific(digits)
		want := "1." + strings.Repeat("0", int(digits)-1) + "E+71"
		if digits >= 72 {
			want = "1." + strings.Repeat("0", 70) + "1" + strings.Repeat("0", int(digits)-72) + "E+71"
		}
		if err != nil || got != want {
			t.Fatalf("Scientific(%d) = %q, %v; want %q", digits, got, err, want)
		}
	}
}

// TestFormatStructFieldVerbs checks that fmt passes the + and #
// flags of %+v and %#v down to every field, so a struct holding a Decimal
// must render the field as canonical text (%+v) and as the Go expression
// that rebuilds it (%#v), not as an unsupported-format diagnostic.
func TestFormatStructFieldVerbs(t *testing.T) {
	type order struct {
		Price Decimal
		Qty   int
	}
	price := MustParse("-1.250")
	for _, tc := range []struct{ format, want string }{
		{"%+v", "{Price:-1.250 Qty:3}"},
		{"%#v", `decimal.order{Price:decimal.MustParse("-1.250"), Qty:3}`},
	} {
		got := fmt.Sprintf(tc.format, order{price, 3})
		if got != tc.want {
			t.Errorf("Sprintf(%q) = %s; want %s", tc.format, got, tc.want)
		}
	}
	for _, tc := range []struct {
		format string
		value  Decimal
		want   string
	}{
		{"%+v", price, "-1.250"},
		{"%+v", MustParse("1E+3"), "1E+3"},
		{"%#v", price, `decimal.MustParse("-1.250")`},
		{"%#v", Decimal{}, `decimal.MustParse("0")`},
		{"%+8v", price, "  -1.250"},
		{"%#v", MustParse("12345678901234567890123456789012345678901234567890"), `decimal.MustParse("12345678901234567890123456789012345678901234567890")`},
	} {
		if got := fmt.Sprintf(tc.format, tc.value); got != tc.want {
			t.Errorf("Sprintf(%q, %v) = %q; want %q", tc.format, tc.value, got, tc.want)
		}
		if back := strings.TrimSuffix(strings.TrimPrefix(fmt.Sprintf("%#v", tc.value), `decimal.MustParse("`), `")`); !rebuilds(back, tc.value) {
			t.Errorf("%%#v of %v does not rebuild it: %s", tc.value, back)
		}
	}
	// The remaining flags stay outside the closed verb set.
	for _, format := range []string{"%+f", "% v", "%08v", "%#e", "%q"} {
		if got := fmt.Sprintf(format, price); got != "%!decimal(unsupported format)" {
			t.Errorf("Sprintf(%q) = %q; want the unsupported-format diagnostic", format, got)
		}
	}
}

func rebuilds(text string, want Decimal) bool {
	v, err := Parse(text)
	return err == nil && sameCohort(v, want)
}

// TestDisplayAppendFormsMatchStrings checks that AppendFixed,
// AppendScientific and AppendEngineering append exactly the text of
// FixedWithOptions, ScientificWithOptions and EngineeringWithBudget after
// any prefix, return dst unchanged with the same error on refusal, and
// allocate nothing into a buffer with room, on both the planner and the
// direct path.
func TestDisplayAppendFormsMatchStrings(t *testing.T) {
	r := rand.New(rand.NewSource(87))
	values := []Decimal{Zero(), New(-5, -3), MustParse("123.456"), MustParse("-9.995"), MustParse("1E+30"),
		MustParse("12345678901234567890123456789012345678901234567890E-20"), New(math.MaxInt64, -10)}
	for range 300 {
		values = append(values, New(r.Int63n(1<<62)-(1<<61), int32(r.Intn(60)-30)))
	}
	modes := []RoundingMode{TiesToEven, TiesAwayFromZero, TowardZero, Exact}
	prefix := []byte("x=")
	directPaths := 0
	for _, d := range values {
		for _, places := range []uint64{0, 1, 2, 5, 19, 25} {
			for _, mode := range modes {
				for _, budget := range []Budget{{}, {MaxOutputBytes: 6}, {MaxWork: 8}} {
					opts := DisplayOptions{Mode: mode, Budget: budget}
					want, wantErr := d.FixedWithOptions(places, opts)
					got, gotErr := d.AppendFixed(slices.Clone(prefix), places, opts)
					checkAppended(t, "AppendFixed", d, prefix, got, gotErr, want, wantErr)
					if places != 0 {
						want, wantErr = d.ScientificWithOptions(places, opts)
						got, gotErr = d.AppendScientific(slices.Clone(prefix), places, opts)
						checkAppended(t, "AppendScientific", d, prefix, got, gotErr, want, wantErr)
					}
					if opts == (DisplayOptions{}) {
						if _, ok := d.fixedTiesToEven(places); ok {
							directPaths++
						}
					}
				}
			}
		}
		for _, budget := range []Budget{{}, {MaxOutputBytes: 4}} {
			want, wantErr := d.EngineeringWithBudget(budget)
			got, gotErr := d.AppendEngineering(slices.Clone(prefix), budget)
			checkAppended(t, "AppendEngineering", d, prefix, got, gotErr, want, wantErr)
		}
	}
	if directPaths < 100 {
		t.Fatalf("the direct path served only %d calls", directPaths)
	}
	buf := make([]byte, 0, 256)
	for _, d := range []Decimal{MustParse("123.456"), MustParse("12345678901234567890123456789012345678901234567890E-20")} {
		if allocs := testing.AllocsPerRun(20, func() {
			buf, _ = d.AppendFixed(buf[:0], 2, DisplayOptions{})
			buf, _ = d.AppendScientific(buf[:0], 5, DisplayOptions{Mode: TowardZero})
			buf, _ = d.AppendEngineering(buf[:0], Budget{})
		}); allocs != 0 {
			t.Fatalf("appending %v into a buffer with room allocated %v times", d, allocs)
		}
	}
}

func checkAppended(t *testing.T, op string, d Decimal, prefix, got []byte, gotErr error, want string, wantErr error) {
	t.Helper()
	if wantErr != nil {
		var e *Error
		if !bytes.Equal(got, prefix) || !errors.As(gotErr, &e) || e.Op != op || e.Code != wantErr.(*Error).Code {
			t.Fatalf("%s(%v) refusal = %q, %v; want prefix unchanged and %v", op, d, got, gotErr, wantErr)
		}
		return
	}
	if gotErr != nil || string(got) != string(prefix)+want {
		t.Fatalf("%s(%v) = %q, %v; want %q", op, d, got, gotErr, string(prefix)+want)
	}
}

// TestScientificInlineMatchesPlanner pins the one-word Scientific path to
// the planner.
func TestScientificInlineMatchesPlanner(t *testing.T) {
	rng := randv2.New(randv2.NewPCG(41, 43))
	taken, carries := 0, 0
	for range 100000 {
		var w uint64
		switch rng.IntN(6) {
		case 0:
			w = rng.Uint64() >> uint(rng.IntN(64))
		case 1:
			// all nines, a half, or just around a half below a carry
			n := 1 + rng.IntN(19)
			w = pow10Words[n] - 1
			if n > 2 && rng.IntN(2) == 0 {
				w -= uint64(rng.IntN(6)) * pow10Words[rng.IntN(n-1)]
			}
		case 2:
			w = uint64(rng.IntN(10)) * pow10Words[rng.IntN(19)]
			w += 5 * pow10Words[rng.IntN(18)]
		case 3:
			w = 0
		case 4:
			w = ^uint64(0) - uint64(rng.IntN(10))
		default:
			w = rng.Uint64N(100_000_000)
		}
		e := int32(rng.IntN(61) - 30)
		switch rng.IntN(20) {
		case 0:
			e = 2147483647
		case 1:
			e = -2147483648
		}
		d := inlineDecimal(uint128{lo: w}, e, rng.IntN(2) == 0)
		places := uint64(1 + rng.IntN(19))
		if rng.IntN(50) == 0 {
			places = uint64(rng.IntN(25))
		}
		got, gerr := d.Scientific(places)
		want, werr := d.display(displayScientific, places, DisplayOptions{}, "ScientificWithOptions")
		if (gerr == nil) != (werr == nil) || got != want {
			t.Fatalf("%v Scientific(%d): %q, %v; planner %q, %v", d, places, got, gerr, want, werr)
		}
		got2, gerr2 := d.ScientificWithOptions(places, DisplayOptions{})
		got3, gerr3 := d.AppendScientific([]byte("ab"), places, DisplayOptions{})
		if got2 != want || (gerr2 == nil) != (werr == nil) || (gerr3 == nil) != (werr == nil) || werr == nil && string(got3) != "ab"+want || werr != nil && string(got3) != "ab" {
			t.Fatalf("%v Scientific(%d): options %q, append %q; planner %q, %v", d, places, got2, got3, want, werr)
		}
		var buf [scientificInlineMax]byte
		if i, ok := d.scientificTiesToEven(&buf, places); ok {
			taken++
			if w != 0 && uint64(wordDigits(w)) > places && len(want) > 0 && string(buf[i:]) == want {
				if d2 := want[len(want)-1]; d2 != 0 && want[0] != '-' && want[0] == '1' && (w/pow10Words[wordDigits(w)-1]) == 9 {
					carries++
				}
			}
		}
	}
	if taken < 50000 || carries < 100 {
		t.Fatalf("vacuous path coverage: %d taken, %d carries", taken, carries)
	}
}

// TestDisplayRefusesUnaddressableOutput checks that a digit count the
// runtime cannot allocate is refused, not attempted: beyond the target's
// largest object an allocation panics, and no exported function may.
func TestDisplayRefusesUnaddressableOutput(t *testing.T) {
	if math.MaxInt == math.MaxInt32 {
		t.Skip("a 32-bit int already bounds the digit count below the largest object")
	}
	one := New(1, 0)
	slow := MustParse("123456789012345678901234567890123456789012345678901234567890")
	for _, places := range []uint64{displayLimit() - 1, displayLimit(), 1 << 49, 1 << 62, math.MaxInt - 2} {
		for _, d := range []Decimal{one, one.Neg(), slow, Zero()} {
			for name, call := range map[string]func() (int, error){
				"Fixed": func() (int, error) { s, err := d.Fixed(places); return len(s), err },
				"FixedWithOptions": func() (int, error) {
					s, err := d.FixedWithOptions(places, DisplayOptions{Mode: TowardZero})
					return len(s), err
				},
				"Scientific": func() (int, error) { s, err := d.Scientific(places); return len(s), err },
				"ScientificWithOptions": func() (int, error) {
					s, err := d.ScientificWithOptions(places, DisplayOptions{})
					return len(s), err
				},
				"AppendFixed":      func() (int, error) { b, err := d.AppendFixed(nil, places, DisplayOptions{}); return len(b), err },
				"AppendScientific": func() (int, error) { b, err := d.AppendScientific(nil, places, DisplayOptions{}); return len(b), err },
			} {
				var detail *Error
				if n, err := call(); !errors.Is(err, ErrInsufficientStorage) || !errors.As(err, &detail) || detail.Op != name || n != 0 {
					t.Fatalf("%v.%s(%d) = %d bytes, %v; want the storage refusal", d, name, places, n, err)
				}
			}
		}
	}
	// A prefix counts against the same limit.
	prefix := make([]byte, 16)
	if out, err := one.AppendFixed(prefix, displayLimit()-10, DisplayOptions{}); !errors.Is(err, ErrInsufficientStorage) || len(out) != len(prefix) {
		t.Fatalf("AppendFixed onto a prefix = %d bytes, %v", len(out), err)
	}
}
