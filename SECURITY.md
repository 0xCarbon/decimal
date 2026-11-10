# Security policy

## Supported versions

| Version | Supported |
| --- | --- |
| 1.0.x | yes |

## Reporting a vulnerability

Report vulnerabilities privately through
[GitHub security advisories](https://github.com/0xCarbon/decimal/security/advisories/new)
("Report a vulnerability" on the repository's Security tab) or email
[fabio@bealore.com](mailto:fabio@bealore.com). Do not open a public issue.
Include the input, the call and what you observed; a failing Go test is
ideal. We aim to acknowledge reports within three business days and to
agree on a disclosure date with you.

## Threat model

Decimal is a numeric library. Its attack surface is untrusted input:

- text given to `Parse`, `ParseWithContext`, `ParseToExponent`,
  `UnmarshalText` and `UnmarshalJSON`;
- values given to `Scan` by a database driver;
- operands derived from such input and passed to arithmetic, rounding,
  display and conversion.

The library's guarantees, and therefore what counts as a vulnerability:

- **No panics.** No exported function or method panics on any input,
  except `MustParse`, which is documented to panic and is meant for
  literals. A panic reachable from any other entry point is a bug.
- **Bounded work and memory.** Coefficients are unbounded, so every
  operation whose work depends on input size has a budgeted form: the
  context forms read `Context.WithBudget`, and the `…WithBudget` forms
  (`ParseToExponentWithBudget`, `ParseJSONWithBudget`, `ScanWithBudget`,
  `SumWithBudget`, …) take a `Budget`. A budget is checked before
  allocating. A budgeted call that does work or allocates memory beyond
  what its budget admits is a vulnerability. The unbudgeted forms have no
  caller limit; services handling untrusted input should use the budgeted
  forms.
- **No silent wrong results.** A result that differs from the documented
  semantics without an error (a wrong value, cohort or condition) is a
  bug, and may be a vulnerability where it affects money or access
  decisions.
- **No retained input.** Decoders copy what they keep; they never retain
  or modify the caller's buffer.

The library has no network, file or process access, no `unsafe` and no
cgo.
