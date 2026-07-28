import TameDelPezzo.NearMissMarkedPoints

/-!
# Eight distinct weighted orbits

The marked points are affine representatives for points of weighted projective
space with weights `(2,2,5,7)`. This file defines the weighted scalar action and
proves that the eight marked representatives lie in eight distinct nonzero
orbits. Thus the earlier cardinality-eight statement is not merely a count of
different affine tuples.

This quotient is only the set-theoretic weighted orbit quotient. It does not
supply the algebraic stack or coarse moduli space still missing from mathlib.
-/

namespace TameDelPezzo.NearMiss

/-- Weighted scalar multiplication for weights `(2,2,5,7)`. -/
noncomputable def weightedScale (λ : GeometricField)
    (point : Coordinate → GeometricField) : Coordinate → GeometricField :=
  fun coordinate => λ ^ coordinateWeight coordinate * point coordinate

/-- The identity scalar fixes every affine representative. -/
theorem weightedScale_one (point : Coordinate → GeometricField) :
    weightedScale 1 point = point := by
  funext coordinate
  simp [weightedScale]

/-- Successive weighted scalings multiply their scalar parameters. -/
theorem weightedScale_mul (μ λ : GeometricField)
    (point : Coordinate → GeometricField) :
    weightedScale μ (weightedScale λ point) = weightedScale (μ * λ) point := by
  funext coordinate
  simp [weightedScale, mul_pow, mul_assoc]

/-- Two nonzero representatives are related when one is a nonzero weighted scaling of the other. -/
def WeightedOrbitRelated
    (point₁ point₂ : Coordinate → GeometricField) : Prop :=
  ∃ λ : GeometricField, λ ≠ 0 ∧ weightedScale λ point₁ = point₂

/-- Weighted-orbit relatedness is reflexive. -/
theorem weightedOrbitRelated_refl (point : Coordinate → GeometricField) :
    WeightedOrbitRelated point point :=
  ⟨1, one_ne_zero, weightedScale_one point⟩

/-- Weighted-orbit relatedness is symmetric. -/
theorem weightedOrbitRelated_symm {point₁ point₂ : Coordinate → GeometricField}
    (h : WeightedOrbitRelated point₁ point₂) :
    WeightedOrbitRelated point₂ point₁ := by
  rcases h with ⟨λ, hλ, hscale⟩
  refine ⟨λ⁻¹, inv_ne_zero hλ, ?_⟩
  rw [← hscale, weightedScale_mul]
  simp [hλ, weightedScale_one]

/-- Weighted-orbit relatedness is transitive. -/
theorem weightedOrbitRelated_trans
    {point₁ point₂ point₃ : Coordinate → GeometricField}
    (h₁₂ : WeightedOrbitRelated point₁ point₂)
    (h₂₃ : WeightedOrbitRelated point₂ point₃) :
    WeightedOrbitRelated point₁ point₃ := by
  rcases h₁₂ with ⟨λ, hλ, hscale₁⟩
  rcases h₂₃ with ⟨μ, hμ, hscale₂⟩
  refine ⟨μ * λ, mul_ne_zero hμ hλ, ?_⟩
  rw [← hscale₂, ← hscale₁, weightedScale_mul]

/-- The setoid of weighted scalar orbits. -/
def weightedOrbitSetoid : Setoid (Coordinate → GeometricField) where
  r := WeightedOrbitRelated
  iseqv := ⟨weightedOrbitRelated_refl, weightedOrbitRelated_symm,
    weightedOrbitRelated_trans⟩

/-- Set-theoretic weighted projective orbits. -/
abbrev WeightedOrbit := Quotient weightedOrbitSetoid

/-- Send an affine representative to its weighted orbit. -/
def weightedOrbitClass
    (point : Coordinate → GeometricField) : WeightedOrbit :=
  Quotient.mk weightedOrbitSetoid point

/-- The exact scalar stabilizer equation for a chart point `(t,1,0,0)`. -/
theorem weightedScale_chartPoint_eq_iff (λ t : GeometricField) :
    weightedScale λ (chartPoint t) = chartPoint t ↔ λ ^ 2 = 1 := by
  constructor
  · intro h
    have hx1 := congr_fun h Coordinate.x1
    simpa [weightedScale, coordinateWeight, chartPoint] using hx1
  · intro hλ
    funext coordinate
    cases coordinate <;>
      simp [weightedScale, coordinateWeight, chartPoint, hλ]

/-- The exact scalar stabilizer equation for `(0,0,1,0)`. -/
theorem weightedScale_yCoordinatePoint_eq_iff (λ : GeometricField) :
    weightedScale λ (coordinatePoint false) = coordinatePoint false ↔
      λ ^ 5 = 1 := by
  constructor
  · intro h
    have hy := congr_fun h Coordinate.y
    simpa [weightedScale, coordinateWeight, coordinatePoint] using hy
  · intro hλ
    funext coordinate
    cases coordinate <;>
      simp [weightedScale, coordinateWeight, coordinatePoint, hλ]

/-- The exact scalar stabilizer equation for `(0,0,0,1)`. -/
theorem weightedScale_zCoordinatePoint_eq_iff (λ : GeometricField) :
    weightedScale λ (coordinatePoint true) = coordinatePoint true ↔
      λ ^ 7 = 1 := by
  constructor
  · intro h
    have hz := congr_fun h Coordinate.z
    simpa [weightedScale, coordinateWeight, coordinatePoint] using hz
  · intro hλ
    funext coordinate
    cases coordinate <;>
      simp [weightedScale, coordinateWeight, coordinatePoint, hλ]

/-- A weighted orbit cannot identify two different marked-point indices. -/
theorem markedPoint_orbit_related_imp_eq {p q : MarkedPointIndex}
    (h : WeightedOrbitRelated (markedPoint p) (markedPoint q)) : p = q := by
  rcases h with ⟨λ, hλ, hscale⟩
  cases p with
  | inl t =>
      cases q with
      | inl u =>
          have hx1 := congr_fun hscale Coordinate.x1
          have hλtwo : λ ^ 2 = 1 := by
            simpa [weightedScale, coordinateWeight, markedPoint, chartPoint] using hx1
          have hx0 := congr_fun hscale Coordinate.x0
          have htu : (t : GeometricField) = (u : GeometricField) := by
            simpa [weightedScale, coordinateWeight, markedPoint, chartPoint,
              hλtwo] using hx0
          exact congrArg Sum.inl (Subtype.ext htu)
      | inr b =>
          have hx1 := congr_fun hscale Coordinate.x1
          cases b <;>
            simp [weightedScale, coordinateWeight, markedPoint, chartPoint,
              coordinatePoint, hλ] at hx1
  | inr b =>
      cases q with
      | inl t =>
          have hx1 := congr_fun hscale Coordinate.x1
          cases b <;>
            simp [weightedScale, coordinateWeight, markedPoint, chartPoint,
              coordinatePoint] at hx1
      | inr c =>
          cases b <;> cases c
          · rfl
          · have hy := congr_fun hscale Coordinate.y
            simp [weightedScale, coordinateWeight, markedPoint, coordinatePoint,
              hλ] at hy
          · have hz := congr_fun hscale Coordinate.z
            simp [weightedScale, coordinateWeight, markedPoint, coordinatePoint,
              hλ] at hz
          · rfl

/-- The map from the eight marked indices to weighted orbits. -/
def markedWeightedOrbit (p : MarkedPointIndex) : WeightedOrbit :=
  weightedOrbitClass (markedPoint p)

/-- The eight marked indices determine eight different weighted orbits. -/
theorem markedWeightedOrbit_injective : Function.Injective markedWeightedOrbit := by
  intro p q h
  apply markedPoint_orbit_related_imp_eq
  exact Quotient.exact h

/-- Every marked representative is a regular point of the punctured affine cone. -/
theorem markedPoint_punctured_cone_regular (p : MarkedPointIndex) :
    ¬ ∀ coordinate,
      MvPolynomial.eval (markedPoint p)
        (MvPolynomial.pderiv coordinate (nearMissEquation GeometricField)) = 0 :=
  nearMissEquation_punctured_cone_regular (markedPoint p)
    (markedPoint_on_nearMissEquation p) (markedPoint_ne_zero p)

/-- Compact weighted-orbit certificate for the near miss. -/
theorem eight_distinct_regular_weighted_orbits :
    Fintype.card MarkedPointIndex = 8 ∧
      Function.Injective markedWeightedOrbit ∧
      (∀ p, markedPoint p ≠ 0) ∧
      (∀ p, MvPolynomial.eval (markedPoint p)
        (nearMissEquation GeometricField) = 0) ∧
      (∀ p, ¬ ∀ coordinate,
        MvPolynomial.eval (markedPoint p)
          (MvPolynomial.pderiv coordinate (nearMissEquation GeometricField)) = 0) := by
  exact ⟨markedPointIndex_card, markedWeightedOrbit_injective,
    markedPoint_ne_zero, markedPoint_on_nearMissEquation,
    markedPoint_punctured_cone_regular⟩

end TameDelPezzo.NearMiss
