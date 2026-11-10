// SPDX-License-Identifier: Apache-2.0

package decimal_test

import (
	"encoding/binary"
	"encoding/json"
	"errors"
	"fmt"
	"hash/maphash"
	"math"
	"math/big"
	"strings"

	decimal "github.com/0xCarbon/decimal"
)

func ExampleDecimal_mapKeys() {
	entries := make(map[string]int)
	for i, value := range []decimal.Decimal{decimal.MustParse("1.2300"), decimal.MustParse("1.23")} {
		key, err := value.Reduce().Text(0)
		if err != nil {
			panic(err) // handle refusal before inserting or querying a key
		}
		entries[key] = i
	}
	fmt.Println(len(entries), entries["1.23"])
	// Output: 1 1
}

func ExampleHasher_mapKeys() {
	seed := maphash.MakeSeed() // one seed per consumer-owned table
	pair := decimal.Hasher{}
	digest := func(value decimal.Decimal) uint64 {
		var h maphash.Hash
		h.SetSeed(seed)
		pair.Hash(&h, value)
		return h.Sum64()
	}
	left, right := decimal.MustParse("1.2300"), decimal.MustParse("1.23")
	fmt.Println(digest(left) == digest(right), pair.Equal(left, right))
	// Output: true true
}

func Example() {
	price := decimal.MustParse("19.99")
	quantity := decimal.FromInt64(3)
	subtotal, err := price.Mul(quantity) // exact: 59.97
	if err != nil {
		panic(err)
	}
	rate := decimal.MustParse("0.0825")
	tax, err := subtotal.Mul(rate) // exact: 4.947525
	if err != nil {
		panic(err)
	}
	tax, _, err = tax.Quantize(-2, decimal.TiesAwayFromZero) // round to cents
	if err != nil {
		panic(err)
	}
	total, err := subtotal.Add(tax)
	if err != nil {
		panic(err)
	}
	fmt.Println(subtotal, tax, total)
	// Output: 59.97 4.95 64.92
}

func ExampleParse() {
	for _, text := range []string{"1.10", "-0.005", "12E+3", "1e-7", "abc"} {
		d, err := decimal.Parse(text)
		if err != nil {
			fmt.Println(text, "->", err)
			continue
		}
		fmt.Println(text, "->", d, d.Exponent())
	}
	// Output:
	// 1.10 -> 1.10 -2
	// -0.005 -> -0.005 -3
	// 12E+3 -> 1.2E+4 3
	// 1e-7 -> 1E-7 -7
	// abc -> decimal: Parse: conversion syntax: abc
}

func ExampleDecimal_Equal() {
	a, b := decimal.MustParse("1.10"), decimal.MustParse("1.1")
	fmt.Println(a.Equal(b), a.Compare(b), a, b, a.Reduce())
	// Output: true 0 1.10 1.1 1.1
}

func ExampleDecimal_Quantize() {
	for _, mode := range []decimal.RoundingMode{decimal.TiesToEven, decimal.TiesAwayFromZero, decimal.TowardZero} {
		d, conditions, err := decimal.MustParse("2.345").Quantize(-2, mode)
		fmt.Println(mode, d, conditions, err)
	}
	_, _, err := decimal.MustParse("2.345").Quantize(-2, decimal.Exact)
	fmt.Println(err)
	// Output:
	// TiesToEven 2.34 Inexact|Rounded|Decreased <nil>
	// TiesAwayFromZero 2.35 Inexact|Rounded|Increased <nil>
	// TowardZero 2.34 Inexact|Rounded|Decreased <nil>
	// decimal: Quantize: condition Inexact
}

// ExampleRoundingMode_monetary rounds an invoice line to cents. The zero
// RoundingMode is TiesToEven, so monetary code names TiesAwayFromZero
// explicitly instead of relying on the default.
func ExampleRoundingMode_monetary() {
	line, _ := decimal.MustParse("0.715").Mul(decimal.FromInt64(3)) // exact: 2.145

	var unset decimal.RoundingMode // the default mode
	even, _, _ := line.Quantize(-2, unset)
	fmt.Println(line, unset, even)

	cents, conditions, err := line.Quantize(-2, decimal.TiesAwayFromZero)
	fmt.Println(cents, conditions, err)

	refund, _, _ := line.Neg().Quantize(-2, decimal.TiesAwayFromZero)
	fmt.Println(refund)
	// Output:
	// 2.145 TiesToEven 2.14
	// 2.15 Inexact|Rounded|Increased <nil>
	// -2.15
}

func ExampleDecimal_AddWithContext() {
	ctx := decimal.Decimal64Context() // 16 digits, TiesToEven
	third := decimal.MustParse("0.3333333333333333")
	sum, conditions, err := third.AddWithContext(decimal.MustParse("0.00000000000000005"), ctx)
	fmt.Println(sum, conditions, err)

	trapping, _ := ctx.WithTraps(decimal.Inexact)
	_, _, err = third.AddWithContext(decimal.MustParse("0.00000000000000005"), trapping)
	fmt.Println(err, errors.Is(err, decimal.ErrInexact))
	// Output:
	// 0.3333333333333334 Inexact|Rounded|Increased <nil>
	// decimal: AddWithContext: condition Inexact true
}

func ExampleDecimal_Fixed() {
	d := decimal.MustParse("-1234.5678")
	fixed, _ := d.Fixed(2)
	scientific, _ := d.Scientific(3)
	engineering, _ := decimal.MustParse("12345").Engineering()
	fmt.Println(fixed, scientific, engineering)
	fmt.Printf("%v|%.1f|%.2e|%12s|\n", d, d, d, d)
	// Output:
	// -1234.57 -1.23E+3 12.345E+3
	// -1234.5678|-1234.6|-1.2E+3|  -1234.5678|
}

func ExampleDecimal_MarshalJSON() {
	var order struct {
		Amount decimal.Decimal `json:"amount"`
		Fee    decimal.Decimal `json:"fee"`
	}
	if err := json.Unmarshal([]byte(`{"amount": 10.50, "fee": "0.25"}`), &order); err != nil {
		panic(err)
	}
	out, _ := json.Marshal(order)
	fmt.Println(string(out))
	// Output: {"amount":10.50,"fee":0.25}
}

func ExampleParseToExponent() {
	price, conditions, _ := decimal.ParseToExponent("19.995", -2, decimal.TiesToEven)
	fmt.Println(price, conditions)
	tiny, _, _ := decimal.ParseToExponent([]byte("1e-99999999999"), -2, decimal.TowardPositiveInfinity)
	fmt.Println(tiny)
	_, err := decimal.Parse("1e-99999999999")
	fmt.Println(errors.Is(err, decimal.ErrExponentRange))
	// Output:
	// 20.00 Inexact|Rounded|Increased
	// 0.01
	// true
}

func ExampleDecimal_DivToExponent() {
	total := decimal.MustParse("100.00")
	count := decimal.FromInt64(3)
	avg, conditions, _ := total.DivToExponent(count, -6, decimal.TiesToEven)
	fmt.Println(avg, conditions)
	_, err := total.Div(count)
	fmt.Println(errors.Is(err, decimal.ErrInexact))
	// Output:
	// 33.333333 Inexact|Rounded|Decreased
	// true
}

func ExampleDecimal_Rem() {
	x, y := decimal.MustParse("10.5"), decimal.MustParse("3")
	q, _ := x.Quo(y)
	r, _ := x.Rem(y)
	near, _ := x.RemNear(y)
	fmt.Println(q, r, near)
	p2, _ := decimal.NewContext(2, decimal.TiesToEven, nil, 0)
	_, _, err := decimal.MustParse("1234").RemWithContext(y, p2)
	fmt.Println(errors.Is(err, decimal.ErrDivisionImpossible))
	// Output:
	// 3 1.5 -1.5
	// true
}

func ExampleFromRatWithContext() {
	third := big.NewRat(1, 3)
	down, _ := decimal.NewContext(7, decimal.TowardNegativeInfinity, nil, 0)
	up, _ := decimal.NewContext(7, decimal.TowardPositiveInfinity, nil, 0)
	lo, lc, _ := decimal.FromRatWithContext(third, down)
	hi, hc, _ := decimal.FromRatWithContext(third, up)
	fmt.Println(lo, lc, hi, hc)
	_, err := decimal.FromRat(third)
	fmt.Println(errors.Is(err, decimal.ErrInexact))
	exact, _ := decimal.FromRat(big.NewRat(3, 40))
	back, _ := exact.Rat(nil)
	fmt.Println(exact, back)
	// Output:
	// 0.3333333 Inexact|Rounded|Decreased 0.3333334 Inexact|Rounded|Increased
	// true
	// 0.075 3/40
}

func ExampleDecimal_Float64Rounded() {
	d := decimal.MustParse("0.1")
	lo, lc, _ := d.Float64Rounded(decimal.TowardNegativeInfinity)
	hi, hc, _ := d.Float64Rounded(decimal.TowardPositiveInfinity)
	fmt.Println(lo, lc)
	fmt.Println(hi, hc)
	cmp, _ := d.CompareFloat64(0.1)
	fmt.Println(cmp)
	exact, _ := decimal.FromFloat64Exact(0.1)
	cast, _, _ := decimal.FromFloat64ToExponent(2.675, -2, decimal.TiesToEven)
	fmt.Println(exact, cast)
	// Output:
	// 0.09999999999999999 Inexact|Rounded|Decreased
	// 0.1 Inexact|Rounded|Increased
	// -1
	// 0.1000000000000000055511151231257827021181583404541015625 2.67
}

func ExampleNullDecimal() {
	var price decimal.NullDecimal
	_ = price.Scan([]byte("19.90")) // a NUMERIC column as a driver delivers it
	fmt.Println(price.Decimal, price.Valid)
	_ = price.Scan(nil) // SQL NULL
	v, _ := price.Value()
	fmt.Println(price.Valid, v)
	var d decimal.Decimal
	_ = d.Scan(0.1) // a float column scans as its exact binary value
	fmt.Println(d)
	// Output:
	// 19.90 true
	// false <nil>
	// 0.1000000000000000055511151231257827021181583404541015625
}

func ExampleNewTwosComplement() {
	// A Parquet FIXED_LEN_BYTE_ARRAY(16) DECIMAL(38,2) value: big-endian
	// two's complement coefficient, scale out of band.
	lane := []byte{0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfb, 0x2e}
	d, _ := decimal.NewTwosComplement(lane, binary.BigEndian, -2)
	fmt.Println(d)
	out, _ := d.AppendTwosComplement(nil, 4, binary.LittleEndian)
	fmt.Printf("% x\n", out)
	// Output:
	// -12.34
	// 2e fb ff ff
}

func ExampleDecimal_BigInt() {
	d, _ := decimal.FromBigInt(new(big.Int).Lsh(big.NewInt(1), 100))
	n, err := d.BigInt(nil)
	fmt.Println(d, n, err)
	_, err = decimal.MustParse("0.5").BigInt(nil)
	fmt.Println(errors.Is(err, decimal.ErrNonIntegral))
	// Output:
	// 1267650600228229401496703205376 1267650600228229401496703205376 <nil>
	// true
}

func ExampleDecimal_Int64() {
	n, err := decimal.MustParse("4.200E+2").Int64()
	fmt.Println(n, err)
	_, err = decimal.MustParse("4.2").Int64()
	fmt.Println(err, errors.Is(err, decimal.ErrNonIntegral))
	// Output:
	// 420 <nil>
	// decimal: Int64: nonintegral value true
}

// driverDecimal models a driver value that keeps a coefficient and scale.
type driverDecimal struct {
	Width, Scale uint8
	Value        *big.Int
}

// String models a driver's convenience conversion that discards scale.
func (v driverDecimal) String() string {
	text := new(big.Rat).SetFrac(v.Value, new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(v.Scale)), nil)).FloatString(int(v.Scale))
	if strings.Contains(text, ".") {
		text = strings.TrimRight(strings.TrimRight(text, "0"), ".")
	}
	return text
}

type driverDecimalScanner struct{ decimal.NullDecimal }

func (n *driverDecimalScanner) Scan(src any) error {
	if src == nil {
		n.NullDecimal = decimal.NullDecimal{}
		return nil
	}
	v, ok := src.(driverDecimal)
	if !ok {
		return n.NullDecimal.Scan(src)
	}
	if v.Value == nil {
		return errors.New("driver decimal has nil coefficient")
	}
	var d decimal.Decimal
	if err := d.Compose(0, v.Value.Sign() < 0, new(big.Int).Abs(v.Value).Bytes(), -int32(v.Scale)); err != nil {
		return err
	}
	n.NullDecimal = decimal.NullDecimal{Decimal: d, Valid: true}
	return nil
}

func ExampleNullDecimal_driverDecimal() {
	var value driverDecimalScanner
	for _, src := range []any{
		driverDecimal{Width: 3, Scale: 2, Value: big.NewInt(110)},
		driverDecimal{Width: 10, Scale: 10, Value: big.NewInt(-5000000000)},
	} {
		if err := value.Scan(src); err != nil {
			panic(err)
		}
		fmt.Println(value.Decimal)
	}
	fmt.Println(value.Scan(driverDecimal{}) != nil, value.Decimal)
	_ = value.Scan(nil)
	fmt.Println(value.Valid)
	_ = value.Scan("2.00")
	fmt.Println(value.Decimal)
	// Output:
	// 1.10
	// -0.5000000000
	// true -0.5000000000
	// false
	// 2.00
}

// ExampleContext_sqlDecimal stores values in a NUMERIC(5,2) column: Quantize
// to the column's exponent under a context whose precision is the column's,
// so one call rounds to the scale and refuses a value that needs more digits.
func ExampleContext_sqlDecimal() {
	// NUMERIC(5,2): five digits, two after the point, ties away from zero.
	column, err := decimal.NewContext(5, decimal.TiesAwayFromZero, nil, 0)
	if err != nil {
		panic(err)
	}
	for _, text := range []string{"123.456", "7", "-0.005", "999.995", "1234.5"} {
		stored, conditions, err := decimal.MustParse(text).QuantizeWithContext(-2, column)
		if err != nil {
			fmt.Println(text, "->", err, errors.Is(err, decimal.ErrInvalidOperation))
			continue
		}
		fmt.Println(text, "->", stored, conditions)
	}

	// Arithmetic is exact; the assignment rounds once.
	price, quantity := decimal.MustParse("19.99"), decimal.MustParse("0.333")
	line, _ := price.Mul(quantity) // exact: 6.65667
	stored, conditions, _ := line.QuantizeWithContext(-2, column)
	fmt.Println(line, "->", stored, conditions)

	// A quotient at MySQL's division scale (the dividend's scale 2 plus
	// div_precision_increment 4), then assigned to the column: two roundings,
	// as the engine performs them.
	sum, _ := decimal.Sum(decimal.MustParse("10.00"), decimal.MustParse("20.00"), decimal.MustParse("20.00"))
	quotient, conditions, _ := sum.DivToExponent(decimal.FromInt64(3), -2-4, decimal.TiesAwayFromZero)
	fmt.Println(sum, "/ 3 ->", quotient, conditions)
	stored, conditions, _ = quotient.QuantizeWithContext(-2, column)
	fmt.Println(quotient, "->", stored, conditions)
	// Output:
	// 123.456 -> 123.46 Inexact|Rounded|Increased
	// 7 -> 7.00 0
	// -0.005 -> -0.01 Inexact|Rounded|Decreased
	// 999.995 -> decimal: QuantizeWithContext: invalid operation true
	// 1234.5 -> decimal: QuantizeWithContext: invalid operation true
	// 6.65667 -> 6.66 Inexact|Rounded|Increased
	// 50.00 / 3 -> 16.666667 Inexact|Rounded|Increased
	// 16.666667 -> 16.67 Inexact|Rounded|Increased
}

// ExampleDecimal_numericKey builds a map key that a Decimal and a float64
// share exactly when they are equal as rationals.
// Every finite nonzero decimal c·10^e and binary m·2^k is uniquely
// sign·u·2^a·5^b with u coprime to 10; the key spells that form.
func ExampleDecimal_numericKey() {
	key := func(negative bool, magnitude *big.Int, a, b int64) string {
		if magnitude.Sign() == 0 {
			return "0" // every zero, including a negative zero float64
		}
		u := new(big.Int).Rsh(magnitude, magnitude.TrailingZeroBits())
		a += int64(magnitude.TrailingZeroBits())
		five, q, r := big.NewInt(5), new(big.Int), new(big.Int)
		for q.QuoRem(u, five, r); r.Sign() == 0; q.QuoRem(u, five, r) {
			u.Set(q)
			b++
		}
		sign := "+"
		if negative {
			sign = "-"
		}
		return fmt.Sprintf("%s%s*2^%d*5^%d", sign, u, a, b)
	}
	decimalKey := func(d decimal.Decimal) string {
		// The reduced sign, coefficient and exponent; Reduce keeps the
		// coefficient short and changes no key.
		_, negative, coefficient, exponent := decimal.SQLDecimal{Decimal: d.Reduce()}.Decompose(nil)
		return key(negative, new(big.Int).SetBytes(coefficient), int64(exponent), int64(exponent))
	}
	floatKey := func(f float64) string { // finite f only
		r := new(big.Rat).SetFloat64(f) // exact: numerator / 2^t
		return key(r.Sign() < 0, new(big.Int).Abs(r.Num()), -int64(r.Denom().BitLen()-1), 0)
	}

	fmt.Println(decimalKey(decimal.MustParse("1.00")), floatKey(1))
	fmt.Println(decimalKey(decimal.MustParse("-2.50E+2")), floatKey(-250))
	fmt.Println(decimalKey(decimal.MustParse("0.375")), floatKey(0.375))
	fmt.Println(decimalKey(decimal.MustParse("0.1")) == floatKey(0.1))
	fmt.Println(decimalKey(decimal.MustParse("0.00")), floatKey(math.Copysign(0, -1)))
	// Output:
	// +1*2^0*5^0 +1*2^0*5^0
	// -1*2^1*5^3 -1*2^1*5^3
	// +3*2^-3*5^0 +3*2^-3*5^0
	// false
	// 0 0
}

// ExampleNew_minorUnits moves between integer minor units (cents) and
// Decimal: New places the exponent, and Int64 of the value scaled by 100
// returns the cents exactly or fails instead of truncating.
func ExampleNew_minorUnits() {
	price := decimal.New(1999, -2) // 1999 cents
	total, err := price.Mul(decimal.FromInt64(3))
	if err != nil {
		panic(err)
	}
	cents, err := total.Mul(decimal.FromInt64(100)) // exact: 5997.00
	if err != nil {
		panic(err)
	}
	n, err := cents.Int64()
	fmt.Println(price, total, n, err)

	third, _, _ := total.DivToExponent(decimal.FromInt64(7), -4, decimal.TiesToEven) // 8.5671
	scaled, _ := third.Mul(decimal.FromInt64(100))
	_, err = scaled.Int64() // 856.7100 is not integral
	fmt.Println(third, errors.Is(err, decimal.ErrNonIntegral))
	// Output:
	// 19.99 59.97 5997 <nil>
	// 8.5671 true
}
