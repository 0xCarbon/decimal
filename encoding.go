// SPDX-License-Identifier: Apache-2.0

package decimal

import (
	"database/sql/driver"
	"math"
)

// UnmarshalText parses raw decimal bytes and replaces d only on success.
// It owns the parsed coefficient, never retains the caller's byte slice and
// copies it only into an *Error.
func (d *Decimal) UnmarshalText(text []byte) error {
	if d == nil {
		return newError("UnmarshalText", ErrInvalidOperation)
	}
	parsed, err := parseWithBudget(text, textLimits{}, "UnmarshalText")
	if err != nil {
		return err
	}
	*d = parsed
	return nil
}

// Value returns the checked canonical decimal text as a string driver value.
func (d Decimal) Value() (driver.Value, error) {
	text, err := d.Text(0)
	if err != nil {
		return nil, err
	}
	return text, nil
}

// AppendText implements encoding.TextAppender. It appends the checked
// canonical text to b; on refusal it returns b unchanged and the error.
func (d Decimal) AppendText(b []byte) ([]byte, error) {
	if d.slow == nil {
		return d.appendInlineText(b, 0)
	}
	return d.appendSlowText(b)
}

// MarshalText returns the checked canonical decimal text as owned bytes.
func (d Decimal) MarshalText() ([]byte, error) {
	return d.marshalCanonical()
}

// marshalCanonical returns exactly sized owned canonical text bytes: one
// exact allocation, filled once.
func (d Decimal) marshalCanonical() ([]byte, error) {
	if d.slow == nil {
		if d.words.hi == 0 {
			n := wordDigits(d.words.lo)
			text := make([]byte, d.inlineTextSize(n))
			d.emitWordText(text, n)
			return text, nil
		}
		c := splitWide(d.words)
		text := make([]byte, d.inlineTextSize(c.n))
		d.emitWideText(text, c)
		return text, nil
	}
	layout, err := d.slowTextLayout(0, math.MaxInt)
	if err != nil {
		return nil, err
	}
	text := make([]byte, layout.size)
	layout.emit(text, nil)
	return text, nil
}
