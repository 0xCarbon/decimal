// SPDX-License-Identifier: Apache-2.0

package decimal

// Neg returns d with its sign reversed. Zero remains unsigned, and the
// coefficient and exponent are preserved.
func (d Decimal) Neg() Decimal { return d.negated() }

// Abs returns the magnitude of d without changing its coefficient or exponent.
func (d Decimal) Abs() Decimal {
	d = d.withNegative(false)
	return d
}

// Sign returns -1, 0, or +1 according to the numeric sign of d.
func (d Decimal) Sign() int {
	if d.isZero() {
		return 0
	}
	if d.negative() {
		return -1
	}
	return 1
}

// IsZero reports whether d is a zero at any exponent.
func (d Decimal) IsZero() bool { return d.isZero() }

// Min returns the numerically smaller operand. For equal values it returns
// the smaller-exponent positive or zero cohort, or larger-exponent negative
// cohort.
func (d Decimal) Min(other Decimal) Decimal {
	switch d.Compare(other) {
	case -1:
		return d
	case 1:
		return other
	}
	if d.negative() {
		if d.exponent() >= other.exponent() {
			return d
		}
		return other
	}
	if d.exponent() <= other.exponent() {
		return d
	}
	return other
}

// Max returns the numerically larger operand. For equal values it returns
// the larger-exponent positive or zero cohort, or smaller-exponent negative
// cohort.
func (d Decimal) Max(other Decimal) Decimal {
	switch d.Compare(other) {
	case -1:
		return other
	case 1:
		return d
	}
	if d.negative() {
		if d.exponent() <= other.exponent() {
			return d
		}
		return other
	}
	if d.exponent() >= other.exponent() {
		return d
	}
	return other
}
