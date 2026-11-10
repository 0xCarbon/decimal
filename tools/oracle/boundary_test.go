// SPDX-License-Identifier: Apache-2.0

package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"math/big"
	"os"
	"strings"
	"testing"
)

// TestRoundingBoundaryVectors runs the committed Cartesian boundary axis, with
// math/big reconstructing exact operands and the independent reference
// checking value, cohort, conditions and direction through public Div.
func TestRoundingBoundaryVectors(t *testing.T) {
	vs, err := loadBoundaries("../../testdata/boundaries/rounding.json")
	if err != nil {
		t.Fatal(err)
	}
	for _, v := range vs {
		t.Run(v.ID, func(t *testing.T) {
			name := "DivToExponent"
			if v.Target == "digits" {
				name = "DivWithContext"
			}
			var op opSpec
			for _, candidate := range ops {
				if candidate.name == name {
					op = candidate
				}
			}
			if op.lib == nil {
				t.Fatal("missing operation", name)
			}
			var m mode
			for i, n := range modeNames {
				if n == v.Mode {
					m = mode(i)
				}
			}
			in := input{x: v.X, y: v.Y, k: v.Exponent, p: v.Precision}
			if msg := verify(op.ref(in, m), op.lib(in, libModes[m])); msg != "" {
				t.Fatal(msg)
			}
		})
	}
}

// TestBoundaryInventoryControl rejects missing or duplicate rows and false
// axis labels, so the inventory cannot shrink or drift unnoticed.
func TestBoundaryInventoryControl(t *testing.T) {
	vs, err := loadBoundaries("../../testdata/boundaries/rounding.json")
	if err != nil {
		t.Fatal(err)
	}
	for _, mutate := range []func([]boundaryVector) []boundaryVector{
		func(v []boundaryVector) []boundaryVector { return v[:len(v)-1] },
		func(v []boundaryVector) []boundaryVector { v[0] = v[1]; return v },
		func(v []boundaryVector) []boundaryVector { v[0].X = "1"; return v },
		func(v []boundaryVector) []boundaryVector { v[0].Y = "2"; return v },
		func(v []boundaryVector) []boundaryVector { v[0].Precision++; return v },
		func(v []boundaryVector) []boundaryVector {
			for i := range v {
				if v[i].Magnitude == "band-full" {
					v[i].Y += "0E-1"
					break
				}
			}
			return v
		},
	} {
		copy := append([]boundaryVector{}, vs...)
		if validateBoundaries(mutate(copy)) == nil {
			t.Fatal("invalid boundary inventory accepted")
		}
	}
}

type boundaryVector struct {
	ID          string `json:"id"`
	Mode        string `json:"mode"`
	Target      string `json:"target"`
	Sign        int    `json:"sign"`
	Information string `json:"information"`
	Carry       string `json:"carry"`
	Magnitude   string `json:"magnitude"`
	X           string `json:"x"`
	Y           string `json:"y"`
	Exponent    int    `json:"exponent"`
	Precision   int    `json:"precision"`
}

type boundaryFile struct {
	SchemaVersion int              `json:"schema_version"`
	Vectors       []boundaryVector `json:"vectors"`
}

func loadBoundaries(path string) ([]boundaryVector, error) {
	b, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	var f boundaryFile
	d := json.NewDecoder(bytes.NewReader(b))
	d.DisallowUnknownFields()
	if err = d.Decode(&f); err != nil {
		return nil, err
	}
	if d.Decode(new(any)) != io.EOF {
		return nil, fmt.Errorf("boundary trailing data")
	}
	if f.SchemaVersion != 1 {
		return nil, fmt.Errorf("boundary schema %d", f.SchemaVersion)
	}
	if err = validateBoundaries(f.Vectors); err != nil {
		return nil, err
	}
	return f.Vectors, nil
}

// validateBoundaries checks every axis against independent rational
// arithmetic, as well as exact Cartesian coverage; labels alone do not
// show that an operand reaches a rounding boundary.
func validateBoundaries(vs []boundaryVector) error {
	if len(vs) != 2048 {
		return fmt.Errorf("boundary count %d, want2048", len(vs))
	}
	seen := map[string]bool{}
	for _, v := range vs {
		modeOK := false
		for _, name := range modeNames {
			if v.Mode == name {
				modeOK = true
			}
		}
		if !modeOK || v.Target != "scale" && v.Target != "digits" || v.Sign != -1 && v.Sign != 1 || v.Exponent != -2 {
			return fmt.Errorf("invalid boundary axis %s", v.ID)
		}
		sign := "positive"
		if v.Sign < 0 {
			sign = "negative"
		}
		id := strings.Join([]string{v.Mode, v.Target, sign, v.Information, v.Carry, v.Magnitude}, "/")
		if id != v.ID || seen[id] {
			return fmt.Errorf("duplicate or mislabeled boundary %s", v.ID)
		}
		seen[id] = true
		x, xOK := new(big.Rat).SetString(v.X)
		y, yOK := new(big.Rat).SetString(v.Y)
		if !xOK || !yOK || y.Sign() <= 0 || x.Sign() != v.Sign {
			return fmt.Errorf("invalid boundary operands %s", id)
		}
		anchor := new(big.Int)
		switch v.Magnitude {
		case "small":
			anchor.SetInt64(1)
		case "band-full":
			anchor.Lsh(big.NewInt(1), 128).Sub(anchor, big.NewInt(1))
		case "band-boundary":
			anchor.Lsh(big.NewInt(1), 128)
		case "large":
			anchor.Exp(big.NewInt(10), big.NewInt(180), nil).Add(anchor, big.NewInt(7))
		default:
			return fmt.Errorf("magnitude %s", id)
		}
		// A numerically equal recohort can cross the coefficient band.
		if v.Y != anchor.String() || y.Cmp(new(big.Rat).SetInt(anchor)) != 0 {
			return fmt.Errorf("wrong magnitude anchor %s", id)
		}
		scaled := new(big.Rat).Quo(new(big.Rat).Abs(new(big.Rat).Quo(x, y)), pow10(v.Exponent))
		q, rem := new(big.Int).QuoRem(scaled.Num(), scaled.Denom(), new(big.Int))
		wantQ := int64(12)
		wantP := 2
		switch v.Carry {
		case "ordinary":
		case "group-carry":
			wantQ = 999999999
			wantP = 9
		case "guard-carry-8":
			wantQ = 99999999
			wantP = 8
		case "guard-carry-10":
			wantQ = 9999999999
			wantP = 10
		default:
			return fmt.Errorf("carry %s", id)
		}
		if q.Cmp(big.NewInt(wantQ)) != 0 || v.Precision != wantP {
			return fmt.Errorf("wrong retained digits %s", id)
		}
		frac := new(big.Rat).SetFrac(rem, scaled.Denom())
		var want *big.Rat
		switch v.Information {
		case "below-half":
			want = big.NewRat(4999, 10000)
		case "tie-exact":
			want = big.NewRat(1, 2)
		case "tie-tail":
			want = big.NewRat(5001, 10000)
		case "above-half":
			want = big.NewRat(3, 5)
		default:
			return fmt.Errorf("information class %s", id)
		}
		if frac.Cmp(want) != 0 {
			return fmt.Errorf("wrong guard/sticky information %s", id)
		}
	}
	// Valid enums, unique keys and the Cartesian cardinality imply that every
	// combination exists. No axis may be removed without this check failing.
	return nil
}
