# Correct-rounding claims and how they are checked

An operation documented as correctly rounded returns, under a finite
context, the exact mathematical result rounded once in the context's mode,
with exact Conditions, including the direction. This page lists every such
claim made in the package documentation and the README. Each row names the
argument the claim rests on, the test that checks that reduction or
enclosure, and the named cases that validate the public results against an
independent oracle; all of them run in every `go test` of the package.
No claim is an error bound; the decTest corpus and the random
differentials are additional spot checks. A test, `TestCorrectRoundingClaimsCiteReference`,
keeps this table complete against the documentation.

| Operations | Argument | Checker | Named cases |
| --- | --- | --- | --- |
| `Decimal.Sqrt`, `Decimal.SqrtWithContext` | Reduction: the integer root r = ⌊√N⌋ of the scaled coefficient and its exact remainder decide whether the root is below, at or above the half-way point. | `TestSqrtKernelClass` | `TestSqrtAgainstBigOracle`, `TestSqrtTieCorpus`, `TestSqrtExactRoots`, `TestSqrtDeepStickyDigits` |
| `Decimal.Pow`, `Decimal.PowWithContext` | Enclosure: truncated powers rounded down and up bracket the power; a shared (p+1)-digit prefix is accepted, otherwise the exact path decides. | `TestPowDirectedEnclosure`, `TestPowDigitBracket` | `TestPowAgainstBigOracle`, `TestPowZivMatchesExact`, `TestPowWitnesses` |
| `Decimal.Exp`, `Decimal.Ln`, `Decimal.Log10`, `Decimal.PowDecimal` | Enclosure: certified directed bounds with analytic tails, at a working precision that doubles until the bounds prove the rounding; exact results decided separately. | `TestEnclosurePrimitivesAreDirected`, `TestSeriesKernelsEncloseOracle` | `TestExpMatchesOracleInEveryMode`, `TestLnLog10MatchOracleInEveryMode`, `TestPowDecimalExactCohortsAndTies`, `TestPowDecimalMatchesPowOnInt32`, `TestEvaluationRefinesAmbiguousStages` |
| `Decimal.Sin`, `Decimal.Cos`, `Decimal.Tan` | Reduction: the argument interval is reduced modulo π/2 against a certified π (the table, or Machin's formula beyond it), sin and cos are enclosed by their alternating Taylor series with the next term bounding the tail, tan is the interval quotient, and the working precision doubles until the bounds prove the rounding. | `TestEnclosurePrimitivesAreDirected`, `TestLogConstantTables`, `TestTrigonometricKernelsEncloseOracle`, `TestTrigonometricKernelsEncloseBesideLimbBoundaries`, `TestAlternatingSeriesEnclosesAcrossLimbBoundary` | `TestTrigonometricMatchesOracleInEveryMode`, `TestTrigonometricExactCasesAndDomains`, `TestTrigonometricTinyArguments`, `TestTrigonometricLargeArgumentsAndSaturation`, `TestCosineEnclosesWideReducedIntervals` |
| `Decimal.Asin`, `Decimal.Acos`, `Decimal.Atan`, `Decimal.Atan2` | Enclosure: atan by π/2 − atan(1/a) above one and two half-angle steps down to at most tan(π/16), then its alternating series; asin a = 2·atan(a/(1+√((1−a)(1+a)))), acos from 2·atan(√((1−x)/(1+x))) with π − acos(−x) below zero, and atan2 from the atan of the smaller over the larger magnitude with the certified π; no reduction modulo π/2; the working precision doubles until the bounds prove the rounding. | `TestEnclosurePrimitivesAreDirected`, `TestLogConstantTables`, `TestTrigonometricKernelsEncloseOracle`, `TestTrigonometricKernelsEncloseBesideLimbBoundaries` | `TestTrigonometricMatchesOracleInEveryMode`, `TestTrigonometricExactCasesAndDomains`, `TestTrigonometricTinyArguments` |
| `Decimal.Sinh`, `Decimal.Cosh`, `Decimal.Tanh`, `Decimal.Asinh`, `Decimal.Acosh`, `Decimal.Atanh` | Enclosure, without reduction modulo π/2: sinh and cosh by their positive Taylor series up to 1/2 with the tail bounded by the last term over 7, and above it (E ∓ 1/E)/2 from the exp enclosure E; tanh as sinh/cosh up to 1/2 and (1 − t)/(1 + t) with t = e^(−2a) above; asinh a = 2·atanh(a/(1+√(1+a²))) up to 1/2 and ln(a + √(a²+1)) above; acosh x = 2·asinh(√((x−1)/2)); atanh by its series up to 1/2 and ½·ln((1+a)/(1−a)) above, with the enclosed logarithm; the working precision doubles until the bounds prove the rounding. | `TestEnclosurePrimitivesAreDirected`, `TestSeriesKernelsEncloseOracle`, `TestHyperbolicKernelsEncloseOracle`, `TestPositiveSeriesEnclosesTailCriticalArguments`, `TestPositiveSumAbsorbsRatioRounding` | `TestTrigonometricMatchesOracleInEveryMode`, `TestTrigonometricExactCasesAndDomains`, `TestTrigonometricTinyArguments`, `TestTrigonometricLargeArgumentsAndSaturation` |

Each operation's bare form returns the exact value or refuses; its
WithContext form carries the claim, with or without a budget on the
context.
