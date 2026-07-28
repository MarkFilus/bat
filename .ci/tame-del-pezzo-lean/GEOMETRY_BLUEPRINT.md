# blueprint for an end-to-end formal proof

The current Lean theorem starts from a `CharZeroBridge`. An end-to-end proof
must construct that value from weighted-projective input rather than assume its
fields.

## 1. Weighted stack model

Develop the quotient-stack presentation of weighted projective space and of a
quasi-smooth hypersurface or complete intersection. Required outputs:

- a smooth proper two-dimensional Deligne--Mumford stack;
- explicit stabilizers at geometric points;
- tameness when every weight is prime to characteristic three;
- a coarse moduli surface and its quotient singularities.

## 2. Mixed-characteristic lift

For an arbitrary algebraically closed field of characteristic three:

- construct a Cohen ring;
- lift the weighted equations and coefficients;
- preserve expected codimension and stack smoothness after localization;
- obtain a smooth proper family with characteristic-zero generic fiber.

## 3. Inertia and singularity persistence

Formalize finite étale rigidified inertia strata for a tame stack family and
prove that exact stabilizer orders and tangent characters persist. Combine this
with a cyclic Chevalley--Shephard--Todd theorem to construct the injection

```text
special coarse singularities ↪ generic coarse singularities.
```

The arithmetic core of the cyclic criterion is already formalized here for all
positive cyclic orders.

## 4. Picard specialization

Develop the required Néron--Severi specialization theorem for the smooth proper
stack family, then compare rational stack and coarse Néron--Severi groups in the
presence of divisorial inertia. The target is:

```text
ρ(special coarse) = 1  ⇒  ρ(generic coarse) = 1.
```

## 5. Generic coarse del Pezzo surface

Prove that the characteristic-zero coarse fiber is normal and klt, that its
anticanonical class is ample, and that its geometric Picard rank is one.

## 6. Characteristic-zero singularity bound

Formalize either the general inequality

```text
#Sing(X) ≤ 2 ρ(X) + 2
```

for the relevant characteristic-zero klt del Pezzo surfaces, or the rank-one
corollary `#Sing(X) ≤ 4`.

## recommended order

1. formalize the cyclic quotient/CST statement above the arithmetic theorem;
2. formalize finite tame quotient stacks and coarse local models;
3. add inertia persistence;
4. add Picard comparison and specialization;
5. formalize the characteristic-zero surface bound;
6. instantiate `CharZeroBridge` and invoke `card_special_le_four`.

The main infrastructure gap is not elementary arithmetic; it is algebraic
stacks, coarse spaces, and mixed-characteristic specialization in mathlib.
