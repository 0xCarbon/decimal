// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"math"
	"strconv"
)

// RoundingMode selects a decimal rounding rule for instructed operations.
// The zero value is TiesToEven, so Context{} and every preset round ties to
// even unless a mode is chosen. Monetary rounding should name its mode
// explicitly, usually TiesAwayFromZero, the commercial rounding of prices
// and invoices. Exact refuses a value-changing round.
//
// Worked table: each operand rounded to one decimal place, as
// d.Quantize(-1, mode) returns it. The ties are 2.35, 2.45, −2.35 and
// −2.45; "refused" is Exact's *Error.
//
//	mode                      2.30   2.34   2.35   2.45   2.36  -2.34  -2.35  -2.45  -2.36
//	TiesToEven                 2.3    2.3    2.4    2.4    2.4   -2.3   -2.4   -2.4   -2.4
//	TiesAwayFromZero           2.3    2.3    2.4    2.5    2.4   -2.3   -2.4   -2.5   -2.4
//	TiesTowardZero             2.3    2.3    2.3    2.4    2.4   -2.3   -2.3   -2.4   -2.4
//	TowardZero                 2.3    2.3    2.3    2.4    2.3   -2.3   -2.3   -2.4   -2.3
//	AwayFromZero               2.3    2.4    2.4    2.5    2.4   -2.4   -2.4   -2.5   -2.4
//	TowardPositiveInfinity     2.3    2.4    2.4    2.5    2.4   -2.3   -2.3   -2.4   -2.3
//	TowardNegativeInfinity     2.3    2.3    2.3    2.4    2.3   -2.4   -2.4   -2.5   -2.4
//	Exact                      2.3 refused refused refused refused refused refused refused refused
type RoundingMode uint8

const (
	// TiesToEven rounds to the nearest value and a tie to the even digit
	// (banker's rounding is TiesToEven): 2.35 → 2.4, 2.45 → 2.4,
	// −2.35 → −2.4. It is the zero value and the default of every context.
	TiesToEven RoundingMode = iota
	// TiesAwayFromZero rounds to the nearest value and a tie away from zero
	// (commercial rounding is TiesAwayFromZero): 2.45 → 2.5, −2.35 → −2.4,
	// −2.45 → −2.5. Select it explicitly for monetary rounding.
	TiesAwayFromZero
	// TiesTowardZero rounds to the nearest value and a tie toward zero:
	// 2.35 → 2.3, 2.36 → 2.4, −2.35 → −2.3.
	TiesTowardZero
	// TowardZero truncates: 2.36 → 2.3, −2.35 → −2.3, −2.36 → −2.3.
	TowardZero
	// AwayFromZero rounds any discarded nonzero digit away from zero:
	// 2.34 → 2.4, −2.34 → −2.4, −2.35 → −2.4.
	AwayFromZero
	// TowardPositiveInfinity rounds up (ceiling): 2.34 → 2.4, −2.35 → −2.3,
	// −2.36 → −2.3.
	TowardPositiveInfinity
	// TowardNegativeInfinity rounds down (floor): 2.36 → 2.3, −2.34 → −2.4,
	// −2.35 → −2.4.
	TowardNegativeInfinity
	// Exact refuses a value-changing round with a *Error trapping
	// Inexact: 2.30 → 2.3, while 2.35 and −2.35 are refused.
	Exact
)

var roundingModeNames = [...]string{
	"TiesToEven", "TiesAwayFromZero", "TiesTowardZero", "TowardZero",
	"AwayFromZero", "TowardPositiveInfinity", "TowardNegativeInfinity", "Exact",
}

// String returns the mode's identifier, or RoundingMode(n) for an unknown mode.
func (m RoundingMode) String() string {
	if int(m) < len(roundingModeNames) {
		return roundingModeNames[m]
	}
	return "RoundingMode(" + strconv.Itoa(int(m)) + ")"
}

// ExponentGuards gives optional adjusted-exponent bounds to NewContext.
// Emin and Emax are inclusive bounds on adjusted exponents; a nonnil pointer
// selects guards even when both endpoints are zero. NewContext copies the pair.
type ExponentGuards struct {
	// Emin is the smallest normal adjusted exponent.
	Emin int32
	// Emax is the largest adjusted exponent; a larger result overflows.
	Emax int32
}

// Context is an immutable, explicit decimal arithmetic configuration: a
// precision, rounding mode, optional exponent guards, traps and a resource
// Budget. Its zero value has unlimited precision, TiesToEven, no exponent
// guards, no traps and no budget, so every XWithContext form called with
// Context{} computes what the bare exact X computes; Context{}.WithBudget(b)
// is that exact computation under a quota. Constructors and derivation
// return values with private scalar state; Context is safe to copy and share
// across goroutines.
type Context struct {
	precision uint32
	rounding  RoundingMode
	guards    ExponentGuards
	guarded   bool
	traps     Conditions
	// The budget axes context operations read, split so that the
	// arithmetic kernels read theirs as one register-sized field.
	arith      limits
	inputBytes uint64
}

// trappableConditions is the GDA exceptional-condition inventory that
// contexts may trap; declaredConditions adds the result-direction attributes,
// which are reported but never trappable.
const (
	trappableConditions Conditions = (Underflow << 1) - 1
	declaredConditions  Conditions = (Decreased << 1) - 1
)

func invalidContext(op string) (Context, error) {
	return Context{}, newError(op, ErrInvalidContext)
}

// NewContext constructs an explicit decimal context. Precision zero means
// exact, unlimited working precision and requires absent guards. A nonnil
// guard pair must have Emin <= Emax and Etiny = Emin-(precision-1) within the
// int32 stored-exponent domain. Unknown modes or trap bits are invalid.
// Failure returns Context{} and *Error with InvalidContext identity.
func NewContext(precision uint32, rounding RoundingMode, guards *ExponentGuards, traps Conditions) (Context, error) {
	return newContext(precision, rounding, guards, traps, "NewContext")
}

func newContext(precision uint32, rounding RoundingMode, guards *ExponentGuards, traps Conditions, op string) (Context, error) {
	if rounding > Exact || traps&^trappableConditions != 0 {
		return invalidContext(op)
	}
	c := Context{precision: precision, rounding: rounding, traps: traps}
	if guards == nil {
		return c, nil
	}
	if precision == 0 || guards.Emin > guards.Emax {
		return invalidContext(op)
	}
	etiny := int64(guards.Emin) - (int64(precision) - 1)
	if etiny < math.MinInt32 || etiny > math.MaxInt32 {
		return invalidContext(op)
	}
	c.guards = *guards
	c.guarded = true
	return c, nil
}

// Precision returns the working significant-digit precision.
func (c Context) Precision() uint32 { return c.precision }

// Rounding returns the context's rounding mode.
func (c Context) Rounding() RoundingMode { return c.rounding }

// ExponentGuards returns the copied guard pair and whether it is present.
func (c Context) ExponentGuards() (ExponentGuards, bool) { return c.guards, c.guarded }

// Traps returns the selected condition trap set.
func (c Context) Traps() Conditions { return c.traps }

// Budget returns the context's resource budget: the MaxInputBytes,
// MaxDigits and MaxWork axes, the ones context operations read. The zero
// Budget is unlimited.
func (c Context) Budget() Budget {
	return Budget{MaxInputBytes: c.inputBytes, MaxDigits: c.arith.MaxDigits, MaxWork: c.arith.MaxWork}
}

// guardsOf is the context's guard pair as NewContext takes it.
func (c Context) guardsOf() *ExponentGuards {
	if !c.guarded {
		return nil
	}
	g := c.guards
	return &g
}

// WithPrecision derives a context with precision p, validated as NewContext
// validates it against the guards; 0 is unlimited and needs no guards. The
// receiver is not mutated; failure returns Context{} and an
// ErrInvalidContext error.
func (c Context) WithPrecision(p uint32) (Context, error) {
	return c.derived(newContext(p, c.rounding, c.guardsOf(), c.traps, "Context.WithPrecision"))
}

// WithRounding derives a context with rounding mode m. An unknown mode
// returns Context{} and an ErrInvalidContext error.
func (c Context) WithRounding(m RoundingMode) (Context, error) {
	return c.derived(newContext(c.precision, m, c.guardsOf(), c.traps, "Context.WithRounding"))
}

// WithGuards derives a context with the adjusted-exponent guards g,
// validated as NewContext validates them.
func (c Context) WithGuards(g ExponentGuards) (Context, error) {
	return c.derived(newContext(c.precision, c.rounding, &g, c.traps, "Context.WithGuards"))
}

// derived carries c's budget onto a successfully rebuilt context.
func (c Context) derived(out Context, err error) (Context, error) {
	if err != nil {
		return Context{}, err
	}
	out.arith, out.inputBytes = c.arith, c.inputBytes
	return out, nil
}

// withLimits is c with arithmetic budget axes l, for kernels that charge a
// derived budget.
func (c Context) withLimits(l limits) Context {
	c.arith = l
	return c
}

// WithoutGuards derives a context with no exponent guards; it cannot fail.
func (c Context) WithoutGuards() Context {
	c.guards, c.guarded = ExponentGuards{}, false
	return c
}

// WithBudget derives a context whose operations refuse, with
// ErrInsufficientStorage and before allocating, any call the budget does
// not admit. It keeps the MaxInputBytes, MaxDigits and MaxWork axes;
// MaxInputDigits and MaxOutputBytes bound only integer conversion and
// display, which take a Budget directly. Every budget is valid; the
// receiver is not mutated.
func (c Context) WithBudget(b Budget) Context {
	c.arith = b.arith()
	c.inputBytes = b.MaxInputBytes
	return c
}

// WithTraps derives a context with an independently selected trap set. It
// never mutates the receiver. Unknown condition bits return Context{} and a
// typed InvalidContext error; any GDA exceptional condition bit is permitted,
// but the result-direction attributes Increased and Decreased are not.
func (c Context) WithTraps(traps Conditions) (Context, error) {
	if traps&^trappableConditions != 0 {
		return invalidContext("Context.WithTraps")
	}
	c.traps = traps
	return c, nil
}

// Decimal32Context returns a fresh 7-digit numerical context with Emin -95
// and Emax 96, TiesToEven and no traps. It does not impose an IEEE encoding,
// exceptional value set or clamping.
func Decimal32Context() Context {
	return Context{precision: 7, guards: ExponentGuards{Emin: -95, Emax: 96}, guarded: true}
}

// Decimal64Context returns a fresh 16-digit numerical context with Emin -383
// and Emax 384, TiesToEven and no traps. It adds no encoding or clamping.
func Decimal64Context() Context {
	return Context{precision: 16, guards: ExponentGuards{Emin: -383, Emax: 384}, guarded: true}
}

// Decimal128Context returns a fresh 34-digit numerical context with Emin
// -6143 and Emax 6144, TiesToEven and no traps. It adds no encoding or
// clamping.
func Decimal128Context() Context {
	return Context{precision: 34, guards: ExponentGuards{Emin: -6143, Emax: 6144}, guarded: true}
}
