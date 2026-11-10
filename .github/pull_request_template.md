## What and why

Describe the change and link the issue it addresses.

## Checklist

- [ ] `make check` passes (both build profiles).
- [ ] A bug fix comes with a test that fails without it.
- [ ] Performance changes include an interleaved A/B `tools/benchcmp`
      comparison with command, Go version, CPU and raw output.
- [ ] No new dependencies, `unsafe`, cgo or assembly.
- [ ] User-visible changes have a CHANGELOG entry.
