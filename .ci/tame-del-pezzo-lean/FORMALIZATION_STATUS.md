# formalization status

## exact machine-checked result

Lean proves the following implication.

> Let `S` be the finite singular locus of a characteristic-three candidate and
> `G` the finite singular locus of a characteristic-zero surface. If there is
> an injection `S → G`, if the generic Picard rank is `ρ`, and if
> `#G ≤ 2ρ + 2`, then `#S ≤ 2ρ + 2`. In particular, when `ρ = 1`, `#S ≤ 4`, so
> five, seven, and eight singularities are impossible.

The hypotheses are fields of `CharZeroBridge`. They are assumptions presented
to Lean, not theorems smuggled in as project axioms.

## coverage ledger

| component | status |
|---|---|
| cardinality transfer along an injection | proved in Lean |
| general transfer `#special ≤ 2ρ+2` | proved in Lean |
| rank-one consequence `#special ≤ 4` | proved in Lean |
| exclusion of five, seven, and eight points | proved in Lean |
| executable cyclic closed formula | defined in Lean |
| executable coordinate-kernel enumeration | independently defined in Lean |
| all-orders complementary-divisor criterion | proved in Lean |
| executable formula equivalent to the all-orders lcm criterion | proved in Lean |
| independent implementation agreement through order 16 | pure kernel proof over 1,495 cases |
| implementation agreement through order 48 | independent Python exact regression over 38,023 cases |
| primary sweep through order 256 | independent Python exact regression over 5,625,215 cases |
| characteristic-three sextic derivative and degree | proved in Lean |
| sextic separability and six distinct geometric roots | proved in Lean |
| six roots plus two coordinate points have cardinality eight | proved in Lean |
| near-miss intersection and Picard arithmetic | proved in Lean |
| tame divisor arithmetic | proved in Lean |
| smooth mixed-characteristic lift of the weighted stack | not formalized |
| persistence and injectivity of coarse singularities | not formalized |
| persistence of stabilizer orders and tangent characters | not formalized |
| Néron--Severi specialization | not formalized |
| rational stack/coarse Picard comparison | not formalized |
| generic coarse fiber is rank-one klt del Pezzo | not formalized |
| characteristic-zero bound `#Sing ≤ 2ρ+2` | explicit bridge hypothesis; not formalized |

## assurance levels

### kernel checked

The all-orders cyclic criterion, the abstract singularity reduction, the pure
bounded cross-check, the sextic root count, and the near-miss arithmetic are
Lean declarations checked by the kernel. Their axiom ledger contains only the
standard logical principles used by mathlib (`propext`, `Quot.sound`, and, where
needed, `Classical.choice`).

### independent environment checks

CI runs `leanchecker` and `nanoda`. The latter is an independent Lean type
checker implemented in Rust. The source gate rejects proof placeholders and
project-defined axioms before either checker runs.

### regression computation

The 38,023- and 5,625,215-case sweeps are deliberately kept outside theorem
statements. This avoids introducing `native_decide` proof axioms into the
trusted Lean environment. Their role is implementation regression and
cross-language reproduction, not logical justification of the all-orders
formula.

## honesty statement

This is not yet a formal proof of the geometric no-go theorem. It is a
machine-checked reduction plus exact local and finite certificates. The first
unsupported mathematical step remains construction of the mixed-characteristic
geometric bridge represented by `CharZeroBridge`.
