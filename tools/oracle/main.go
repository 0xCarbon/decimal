// SPDX-License-Identifier: Apache-2.0

// Command oracle is the seeded rational differential: every rounding
// operation of the library is run through the public API on seeded random
// and constructed-tie inputs in every mode, and each result, its exponent or digit count, and its
// Inexact, Rounded and direction bits are compared with an exact
// math/big reference (reference.go). The harness supplies the target
// exponent or precision and the mode; the reference never infers them.
//
// The tests run the fixed seed below. The command runs deeper searches with
// other seeds:
//
//	go run ./tools/oracle [-seed N] [-random R] [-ties T] [-op NAME] [-laws L]
//
// It prints per-operation counts and every disagreement, and exits 1 on any
// disagreement, 2 on a usage error.
package main

import (
	"errors"
	"flag"
	"fmt"
	"hash/fnv"
	"math"
	"math/big"
	"math/rand/v2"
	"os"
	"slices"
	"strconv"
	"strings"

	"github.com/0xCarbon/decimal"
)

// defaultSeed is the fixed seed of the test run, so every run sees the same
// inputs. Each operation derives its stream from it
// and its name, so adding an operation leaves the others' inputs unchanged.
const defaultSeed = 0xDEC055B

// Test-run sizes per operation and mode: seeded random inputs and constructed
// ties (exact ties, ties with a tail above, and near-ties below).
const (
	defaultRandom = 48
	defaultTies   = 36
)

// libModes maps the reference modes to the library's constants by name;
// TestModeMappingByName pins the names.
var libModes = [modeCount]decimal.RoundingMode{
	decimal.TiesToEven, decimal.TiesAwayFromZero, decimal.TiesTowardZero, decimal.TowardZero,
	decimal.AwayFromZero, decimal.TowardPositiveInfinity, decimal.TowardNegativeInfinity, decimal.Exact,
}

// input is one generated case. Unused fields are zero.
type input struct {
	x, y, z string   // decimal operands as text
	r       *big.Rat // rational operand
	f       float64  // binary64 operand
	n       int      // integer power
	k       int      // target exponent
	p       int      // precision (significant digits)
	tie     bool     // constructed tie or near-tie
}

// output is what the library returned.
type output struct {
	text  string
	f     float64
	conds decimal.Conditions
	err   error
}

// expect is the reference's verdict for one case.
type expect struct {
	r        rounded
	f        float64 // expected double for float results
	isFloat  bool
	exponent *int // required stored exponent
	digits   int  // maximum coefficient digits (precision operations)
	// rounded, when set, is whether an exact result must report Rounded
	// (zero digits dropped from its ideal cohort); nil leaves it unchecked.
	rounded *bool
	invalid bool // the rounded coefficient exceeds p: InvalidOperation refusal
}

// opSpec is one operation under test.
type opSpec struct {
	name string
	gen  func(g *gen, tie bool) input
	lib  func(in input, m decimal.RoundingMode) output
	ref  func(in input, m mode) expect
	// digitTarget marks precision (significant-digit) operations; the
	// sticky fault truncates their x operand below digit p+1.
	digitTarget bool
}

func main() {
	if err := run(); err != nil {
		fmt.Fprintln(os.Stderr, "oracle:", err)
		if errors.Is(err, errMismatch) {
			os.Exit(1)
		}
		os.Exit(2)
	}
}

var errMismatch = errors.New("differential disagreement")

func run() error {
	seed := flag.Uint64("seed", defaultSeed, "base seed")
	random := flag.Int("random", defaultRandom, "random inputs per operation and mode")
	ties := flag.Int("ties", defaultTies, "constructed ties per operation and mode")
	only := flag.String("op", "", "run one operation by name")
	lawCases := flag.Int("laws", 0, "also run the property laws this many times each (seed + 1)")
	flag.Parse()
	if flag.NArg() != 0 || *random < 0 || *ties < 0 {
		return errors.New("usage: oracle [-seed N] [-random R] [-ties T] [-op NAME] [-laws L]")
	}
	selected := ops
	if *only != "" {
		i := slices.IndexFunc(ops, func(o opSpec) bool { return o.name == *only })
		if i < 0 {
			return fmt.Errorf("unknown operation %q", *only)
		}
		selected = ops[i : i+1]
	}
	bad := 0
	for _, op := range selected {
		st := runOp(op, *seed, *random, *ties, faultNone)
		fmt.Printf("%-28s checks %6d  ties %5d  inexact %6d  mismatches %d\n", op.name, st.checks, st.ties, st.inexact, len(st.mismatches))
		for _, m := range st.mismatches {
			fmt.Println("  ", m)
		}
		bad += len(st.mismatches)
	}
	fmt.Printf("oracle: seed %#x, %d random and %d tie inputs per operation and mode\n", *seed, *random, *ties)
	if *lawCases > 0 {
		v := runLaws(*seed+1, *lawCases, libraryOps)
		for _, l := range laws {
			fmt.Printf("law %-46s cases %6d  violations %d\n", l.name, *lawCases, len(v[l.name]))
			for _, msg := range v[l.name] {
				fmt.Println("  ", msg)
			}
			bad += len(v[l.name])
		}
	}
	if bad > 0 {
		return fmt.Errorf("%w: %d", errMismatch, bad)
	}
	return nil
}

// stats summarizes one operation's run.
type stats struct {
	checks, ties, inexact, exact int
	mismatches                   []string
}

// fault is a deliberately defective use of the library, for the negative
// controls: the checker must report each one.
type fault int

const (
	faultNone      fault = iota
	faultTieSwap         // a confusable ties mode is used
	faultTruncate        // TowardZero is used instead of the mode
	faultSticky          // the operand is cut below the guard digit
	faultDirection       // Increased and Decreased are swapped
	faultULP             // results ending in 3 are one unit too large
)

// runOp runs one operation over every mode with its derived seed.
func runOp(op opSpec, seed uint64, random, ties int, fl fault) stats {
	h := fnv.New64a()
	h.Write([]byte(op.name))
	g := &gen{rng: rand.New(rand.NewPCG(seed, h.Sum64()))}
	var st stats
	for m := range modeCount {
		for i := range random + ties {
			tie := i >= random
			in := op.gen(g, tie)
			exp := op.ref(in, m)
			callMode, callIn := libModes[m], in
			switch fl {
			case faultTieSwap:
				callMode = libModes[map[mode]mode{tiesToEven: tiesAwayFromZero, tiesAwayFromZero: tiesToEven, tiesTowardZero: tiesAwayFromZero}[m]]
				if m > tiesTowardZero {
					callMode = libModes[m]
				}
			case faultTruncate:
				if m != exactOnly {
					callMode = decimal.TowardZero
				}
			case faultSticky:
				callIn = dropSticky(op, in)
			}
			out := op.lib(callIn, callMode)
			switch fl {
			case faultDirection:
				if d := out.conds & (decimal.Increased | decimal.Decreased); d != 0 {
					out.conds ^= decimal.Increased | decimal.Decreased
				}
			case faultULP:
				out = plusULP(out)
			}
			st.checks++
			if tie {
				st.ties++
			}
			if exp.r.inexact {
				st.inexact++
			} else {
				st.exact++
			}
			if msg := verify(exp, out); msg != "" {
				st.mismatches = append(st.mismatches, fmt.Sprintf("%s %v %s: %s", op.name, m, describe(in), msg))
			}
		}
	}
	return st
}

func describe(in input) string {
	var parts []string
	if in.x != "" {
		parts = append(parts, "x="+in.x)
	}
	if in.y != "" {
		parts = append(parts, "y="+in.y)
	}
	if in.z != "" {
		parts = append(parts, "z="+in.z)
	}
	if in.r != nil {
		parts = append(parts, "r="+in.r.String())
	}
	if in.f != 0 {
		parts = append(parts, "f="+strconv.FormatFloat(in.f, 'g', -1, 64))
	}
	parts = append(parts, fmt.Sprintf("n=%d k=%d p=%d", in.n, in.k, in.p))
	return strings.Join(parts, " ")
}

const directionBits = decimal.Increased | decimal.Decreased

// verify compares one library output with the reference verdict and
// describes a disagreement; the empty string is agreement.
func verify(exp expect, out output) string {
	switch {
	case exp.r.refused:
		if ce, ok := errors.AsType[*decimal.Error](out.err); !ok || ce.Condition&decimal.Inexact == 0 {
			return fmt.Sprintf("want the Exact refusal (Inexact), got %s %v %v", out.text, out.conds, out.err)
		}
		return ""
	case exp.invalid:
		if oe, ok := errors.AsType[*decimal.Error](out.err); !ok || oe.Condition&decimal.InvalidOperation == 0 {
			return fmt.Sprintf("want InvalidOperation (coefficient exceeds p), got %s %v %v", out.text, out.conds, out.err)
		}
		return ""
	case out.err != nil:
		return fmt.Sprintf("unexpected refusal %v, want %s", out.err, exp.r.value.RatString())
	}
	if exp.isFloat {
		if math.Float64bits(out.f) != math.Float64bits(exp.f) {
			return fmt.Sprintf("got %v, want %v", out.f, exp.f)
		}
	} else {
		v, digits, e, ok := parseText(out.text)
		switch {
		case !ok:
			return fmt.Sprintf("unreadable result text %q", out.text)
		case v.Cmp(exp.r.value) != 0:
			return fmt.Sprintf("got %s, want %s", out.text, exp.r.value.RatString())
		case exp.exponent != nil && e != *exp.exponent:
			return fmt.Sprintf("got %s at exponent %d, want exponent %d", out.text, e, *exp.exponent)
		case exp.digits > 0 && digits > exp.digits:
			return fmt.Sprintf("got %s with %d digits, want at most %d", out.text, digits, exp.digits)
		}
	}
	c := out.conds
	if extra := c &^ (decimal.Inexact | decimal.Rounded | directionBits); extra != 0 {
		return fmt.Sprintf("unexpected conditions %v", extra)
	}
	if got := c&decimal.Inexact != 0; got != exp.r.inexact {
		return fmt.Sprintf("Inexact %v, want %v (conditions %v)", got, exp.r.inexact, c)
	}
	if exp.r.inexact && c&decimal.Rounded == 0 {
		return fmt.Sprintf("Inexact without Rounded (%v)", c)
	}
	if !exp.r.inexact && exp.rounded != nil && (c&decimal.Rounded != 0) != *exp.rounded {
		return fmt.Sprintf("exact result: Rounded %v, want %v (conditions %v)", c&decimal.Rounded != 0, *exp.rounded, c)
	}
	if got := c.Direction(); got != exp.r.dir {
		return fmt.Sprintf("direction %d, want %d (conditions %v)", got, exp.r.dir, c)
	}
	return ""
}

// dropSticky cuts an operand below the guard digit of its target, the
// dropped-sticky defect class: digit operations keep p+1
// significant digits of x; exponent operations keep digits down to k-1.
func dropSticky(op opSpec, in input) input {
	if in.x == "" {
		return in
	}
	v, _, _, ok := parseText(in.x)
	if !ok || v.Sign() == 0 {
		return in
	}
	keep := in.k - 1
	if op.digitTarget {
		keep = adjusted(v) - in.p
	}
	cut := roundToExponent(v, keep, towardZero).value
	in.x = ratText(cut)
	return in
}

// plusULP adds one unit in the last place to results whose last digit is 3.
func plusULP(out output) output {
	if out.err != nil {
		return out
	}
	if out.text == "" {
		if math.Float64bits(out.f)&7 == 3 {
			out.f = math.Nextafter(out.f, math.Inf(1))
		}
		return out
	}
	v, _, e, ok := parseText(out.text)
	mant, _, _ := strings.Cut(strings.ToUpper(out.text), "E")
	if !ok || !strings.HasSuffix(mant, "3") {
		return out
	}
	out.text = ratText(new(big.Rat).Add(v, pow10(e)))
	return out
}

// ratText writes a terminating rational as decimal text (coefficient E
// exponent). It panics on a non-terminating rational: generators only
// build terminating ones.
func ratText(r *big.Rat) string {
	den := new(big.Int).Set(r.Denom())
	twos, fives := 0, 0
	for den.Bit(0) == 0 {
		den.Rsh(den, 1)
		twos++
	}
	five := big.NewInt(5)
	for new(big.Int).Mod(den, five).Sign() == 0 {
		den.Quo(den, five)
		fives++
	}
	if den.Cmp(bigOne) != 0 {
		panic("ratText: non-terminating rational " + r.String())
	}
	s := max(twos, fives)
	coeff := new(big.Rat).Mul(r, pow10(s))
	return coeff.Num().String() + "E-" + strconv.Itoa(s)
}

// gen draws inputs from one seeded stream.
type gen struct{ rng *rand.Rand }

// digitCount favors short coefficients and hits the 19/38-digit band edges.
func (g *gen) digitCount() int {
	switch r := g.rng.IntN(20); {
	case r < 11:
		return 1 + g.rng.IntN(8)
	case r < 16:
		return []int{9, 10, 18, 19, 20, 21}[g.rng.IntN(6)]
	default:
		return []int{37, 38, 39, 40, 45}[g.rng.IntN(5)]
	}
}

func (g *gen) digits(n int) string {
	b := make([]byte, n)
	for i := range b {
		b[i] = byte('0' + g.rng.IntN(10))
	}
	if n > 0 && b[0] == '0' {
		b[0] = byte('1' + g.rng.IntN(9))
	}
	return string(b)
}

func (g *gen) sign() string {
	if g.rng.IntN(2) == 0 {
		return "-"
	}
	return ""
}

// decimal draws a random decimal text; one in twenty is a zero.
func (g *gen) decimal(expLo, expHi int) string {
	e := expLo + g.rng.IntN(expHi-expLo+1)
	if g.rng.IntN(20) == 0 {
		return "0E" + strconv.Itoa(e)
	}
	c := g.digits(g.digitCount())
	if g.rng.IntN(8) == 0 {
		c += strings.Repeat("0", 1+g.rng.IntN(3))
	}
	return g.sign() + c + "E" + strconv.Itoa(e)
}

// tieTail draws the digits from the tie digit on: 5 alone (an exact tie),
// 5, zeros and a 1 (just above half), or 4 and nines (just below half).
func (g *gen) tieTail() string {
	switch g.rng.IntN(3) {
	case 1:
		return "5" + strings.Repeat("0", g.rng.IntN(20)) + "1"
	case 2:
		return "4" + strings.Repeat("9", 1+g.rng.IntN(20))
	}
	return "5"
}

// tieAt draws a value that ties, or nearly ties, at exponent k: the tie
// digit sits at 10^(k-1) after an optional prefix.
func (g *gen) tieAt(k int) string {
	prefix := ""
	if g.rng.IntN(4) != 0 {
		prefix = g.digits(1 + g.rng.IntN(12))
	}
	tail := g.tieTail()
	return g.sign() + prefix + tail + "E" + strconv.Itoa(k-len(tail))
}

// tieDigits draws a value that ties, or nearly ties, at p significant
// digits: p leading digits, then the tie digit.
func (g *gen) tieDigits(p, expLo, expHi int) string {
	e := expLo + g.rng.IntN(expHi-expLo+1)
	return g.sign() + g.digits(p) + g.tieTail() + "E" + strconv.Itoa(e)
}

func mustRat(s string) *big.Rat {
	v, _, _, ok := parseText(s)
	if !ok {
		panic("bad generated text " + s)
	}
	return v
}

func (g *gen) precision() int { return []int{1, 2, 3, 5, 7, 9, 16, 19, 20, 34, 38, 39}[g.rng.IntN(12)] }

// Reference helpers shared by the op table.

// expAt is an exponent-target verdict. For a source with a stored exponent
// (src, hasSrc), an exact result reports Rounded exactly when the target
// drops digits from it (k > src) and the value is nonzero; without a
// source cohort an exact result never reports Rounded.
func expAt(r rounded, k int) expect {
	kk := k
	f := false
	return expect{r: r, exponent: &kk, rounded: &f}
}

func expAtFrom(r rounded, k, src int) expect {
	e := expAt(r, k)
	// A zero coefficient drops no digits (GDA): an exact zero never rounds.
	*e.rounded = k > src && r.value.Sign() != 0
	return e
}

// expDigits is a precision-target verdict without an ideal exponent: the
// value and at most p digits, and for an inexact result exactly p digits at
// adjusted(value) - p + 1.
func expDigits(r rounded, p int) expect {
	e := expect{r: r, digits: p}
	if r.inexact && r.value.Sign() != 0 {
		k := adjusted(r.value) - p + 1
		e.exponent = &k
	}
	return e
}

// expDigitsIdeal adds the ideal-exponent rule for an exact result: the
// exponent nearest the ideal among those that represent the value in at
// most p digits, min(max(ideal, adjusted - p + 1), reduced), with Rounded
// exactly when it lies above the ideal (zeros dropped).
func expDigitsIdeal(r rounded, p, ideal int) expect {
	e := expDigits(r, p)
	if r.inexact {
		return e
	}
	k := ideal
	if r.value.Sign() != 0 {
		k = min(max(ideal, adjusted(r.value)-p+1), reducedExponent(r.value))
	}
	f := k > ideal
	e.exponent, e.rounded = &k, &f
	return e
}

// reducedExponent is the largest k with x·10^-k an integer (x terminating,
// nonzero).
func reducedExponent(x *big.Rat) int {
	k := adjusted(x)
	for {
		v := new(big.Rat).Mul(x, pow10(-k))
		if v.IsInt() {
			return k
		}
		k--
	}
}

// fitsOrInvalid marks an exponent-target result whose coefficient exceeds a
// finite precision p as the InvalidOperation refusal, as Quantize does.
func fitsOrInvalid(e expect, p int) expect {
	if p == 0 || e.r.refused {
		return e
	}
	c := new(big.Rat).Abs(e.r.value)
	c.Mul(c, pow10(-*e.exponent))
	if len(c.Num().String()) > p && c.Sign() != 0 {
		e.invalid = true
	}
	return e
}

func ctx(p int, m decimal.RoundingMode) decimal.Context {
	c, err := decimal.NewContext(uint32(p), m, nil, 0)
	if err != nil {
		panic(err)
	}
	return c
}

func parse(s string) decimal.Decimal {
	d, err := decimal.Parse(s)
	if err != nil {
		panic(fmt.Sprintf("generated text %q: %v", s, err))
	}
	return d
}

func dec(d decimal.Decimal, c decimal.Conditions, err error) output {
	if err != nil {
		return output{conds: c, err: err}
	}
	return output{text: d.String(), conds: c}
}
