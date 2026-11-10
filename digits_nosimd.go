// SPDX-License-Identifier: Apache-2.0

//go:build !goexperiment.simd

package decimal

import "math"

// vectorSpanMin disables the vector dispatch when portable SIMD is not built.
const vectorSpanMin = math.MaxInt

func vectorDigitSpanBytes(b []byte) int { return swarDigitSpan(b) }
