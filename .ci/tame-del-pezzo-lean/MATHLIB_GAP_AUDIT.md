# mathlib infrastructure gap audit

This project is pinned to mathlib commit
`520045ab14e26149ee970e2e617ca04b09bde5d6`.

## infrastructure already present

The pinned library contains substantial scheme-level algebraic geometry,
including fibers, spreading out, étale sites and morphisms, proper morphisms,
smooth group schemes, residue fields, and valuative criteria. These components
are relevant foundations for a future mixed-characteristic proof.

Representative modules include:

- `Mathlib/AlgebraicGeometry/Fiber.lean`
- `Mathlib/AlgebraicGeometry/SpreadingOut.lean`
- `Mathlib/AlgebraicGeometry/Morphisms/Etale.lean`
- `Mathlib/AlgebraicGeometry/Morphisms/Proper.lean`
- `Mathlib/AlgebraicGeometry/Group/Smooth.lean`
- `Mathlib/AlgebraicGeometry/Sites/Etale.lean`

## missing named infrastructure

Repository-wide identifier and path searches found no existing declarations or
modules named for:

- algebraic stacks;
- Deligne--Mumford stacks;
- coarse moduli spaces;
- rigidified inertia;
- Cohen rings;
- Néron--Severi groups;
- klt singularities or del Pezzo surfaces.

This is a search audit, not a logical proof that no useful lower-level lemma
exists. It does show why an honest end-to-end formalization cannot be produced
by merely connecting a few current high-level declarations.

## consequence for this certificate

The current trusted Lean development formalizes everything after the geometric
bridge has supplied:

1. finite special and generic singular loci;
2. an injective persistence map between them;
3. the generic geometric Picard rank;
4. the characteristic-zero inequality `#Sing ≤ 2ρ+2`.

Constructing those fields from a tame weighted complete intersection requires
new reusable formal infrastructure. `GEOMETRY_BLUEPRINT.md` separates that work
into weighted stacks, mixed-characteristic lifting, inertia persistence, Picard
specialization, coarse klt del Pezzo geometry, and the characteristic-zero
surface bound.
