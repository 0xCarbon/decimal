# Decimal cookbook

Recipes for common tasks. Every code block here is the body of a runnable
example in [example_test.go](../example_test.go); `go test` compiles it and
checks its printed output, and a test keeps this page equal to it.

## Rounding money

Rounding is always explicit, and the zero `RoundingMode` is `TiesToEven`:
`Context{}`, every preset and a `Quantize` call given an unset mode round a
tie to the even digit (banker's rounding is TiesToEven). Monetary rounding
should not rely on that default. Name the mode, usually `TiesAwayFromZero`
(commercial rounding is TiesAwayFromZero), at the point where an amount is
rounded to cents:

<!-- example: ExampleRoundingMode_monetary -->
```go
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
```

The exact product 2.145 is a tie at the cent. `TiesToEven` gives 2.14, and
`TiesAwayFromZero` gives 2.15, and −2.15 for the refund. The returned
conditions report exactness and the direction of each rounding. The
source is `ExampleRoundingMode_monetary`. The `RoundingMode` documentation
has a worked table of every mode, including the negative ties −2.35 and
−2.45.

## Keys for maps

`Decimal` is not comparable, so it cannot be a map key: 1.10 and 1.1 are
one number and must be one key. Two recipes cover decimal-only keys.
The first keys a `map[string]V` by the canonical text of the
reduced value; handle the error before using the key, because `String`
returns a diagnostic, not a number, when the text cannot be produced:

<!-- example: ExampleDecimal_mapKeys -->
```go
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
```

The second hashes the numeric value with `Hasher` and a `maphash.Hash`
the caller owns, for a hash table of the caller's own design:

<!-- example: ExampleHasher_mapKeys -->
```go
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
```

### Keys that span decimal and float64

Some systems, SQL engines among them, compare a `DECIMAL` and a `DOUBLE`
by exact value and need one key for both. A double is an exact binary
rational m·2^k, and a decimal is c·10^e = c·2^e·5^e. Every finite nonzero
number of either kind is uniquely sign·u·2^a·5^b with u an integer not
divisible by 2 or 5, so a key built from (sign, u, a, b) is equal exactly
when the two numbers are equal. The decimal side starts from the reduced
sign, coefficient and exponent, which `SQLDecimal.Decompose` returns for
`d.Reduce()`; the
double side from `big.Rat.SetFloat64`, which is exact:

<!-- example: ExampleDecimal_numericKey -->
```go
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
```

0.1 as a decimal and 0.1 as a double get different keys, because the
double is 3602879701896397/2^55. The key's work grows with the coefficient
length (the decomposition converts the coefficient to bytes, and the loop
divides out factors of 5), so bound untrusted values first, for example
with `CoefficientDigits`. Compare with `CompareFloat64` when you need an
order rather than a key.
