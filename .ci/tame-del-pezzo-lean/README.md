# tame del Pezzo obstruction — Lean certificate

This project machine-checks the exact combinatorial and logical core of a
proposed obstruction to tame weighted constructions in characteristic three.
It also certifies the arithmetic of an explicit eight-point near miss.

It does **not** claim an end-to-end formalization of the algebraic geometry.
The mixed-characteristic bridge is an explicit input structure rather than a
hidden axiom or proof placeholder.

## Pinned environment

- Lean `v4.32.1`
- mathlib commit `520045ab14e26149ee970e2e617ca04b09bde5d6`

## Reproduce

```bash
lake update
lake exe cache get
lake build TameDelPezzo
lake env lean Audit.lean
python3 scripts/regression.py
```

The CI workflow additionally runs Lean's bundled `leanchecker` and the
independent Rust checker `nanoda`. Source gates reject `sorry`, `admit`, local
`axiom` declarations, and native-decision proof axioms in the trusted library.

## Principal checked declarations

### Conditional singularity bound

- `card_special_le_two_mul_rho_add_two`
- `card_special_le_four`
- `not_five_singularities`
- `not_seven_singularities`
- `not_eight_singularities`

These prove that an injective persistence map into a characteristic-zero
singular locus transfers the bound `#Sing ≤ 2ρ + 2`; rank one gives at most
four singularities.

### All-orders cyclic criterion

- `CyclicQuotient.cstSmoothPrimary_eq_true_iff_lcm`

For every positive cyclic order `r`, Lean proves

```text
cstSmoothPrimary r a b = true
  ↔ lcm (gcd r a) (gcd r b) = r.
```

This replaces bounded testing of the primary formula by a theorem valid for
all orders. A separately implemented coordinate-kernel enumeration is still
kernel-checked on all 1,495 character pairs through order 16.

### Eight-point near miss

- `NearMiss.binarySextic_six_distinct_geometric_roots`
- `NearMiss.visibleSingularPoints_card`
- `NearMiss.eight_point_near_miss_not_rank_one`

Lean proves that `t^6+t+1` over characteristic three has six distinct roots
over an algebraic closure, that adjoining two coordinate points gives eight
points, and that the candidate arithmetic yields Picard rank six rather than
one.

## Independent regression certificate

`scripts/regression.py` compares the closed cyclic formula with direct
coordinate-kernel enumeration for 38,023 representations through order 48.
It separately sweeps 5,625,215 representations through order 256 and writes a
hashed JSON certificate. This regression is independent exact computation;
the all-orders Lean theorem is the proof of the primary criterion.

## Formalization boundary

See `FORMALIZATION_STATUS.md`. The remaining work is the actual geometric
bridge: tame stack lifting, inertia persistence, Néron--Severi specialization,
stack/coarse Picard comparison, the generic klt del Pezzo conclusion, and a
formal characteristic-zero singularity bound.
