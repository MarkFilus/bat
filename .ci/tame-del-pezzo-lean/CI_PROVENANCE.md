# verification provenance

- lean toolchain: `leanprover/lean4:v4.32.1`
- mathlib commit: `520045ab14e26149ee970e2e617ca04b09bde5d6`
- primary check: `lake build TameDelPezzo`
- dependency ledger: `lake env lean Audit.lean`
- additional environment checks: leanchecker and nanoda
- `nanoda-allow-sorry: false`
- source gate rejects `sorry`, `admit`, and project-defined `axiom` declarations

ci builds only the lean library, rather than compiling native objects for all
of mathlib. the finite propositions remain checked during elaboration by
`decide` or `native_decide` and are listed in `Audit.lean`.
