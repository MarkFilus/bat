import TameDelPezzo.BinarySextic
import TameDelPezzo.NearMissEquation

/-!
# Eight explicit marked points on the near-miss hypersurface

The six roots of `t^6+t+1` give points `(t:1:0:0)`. Two further coordinate
points are `(0:0:1:0)` and `(0:0:0:1)`. This file proves in Lean that these are
eight distinct nonzero affine-cone representatives satisfying the explicit
weighted equation.

This is a statement about marked affine representatives. Identifying their
weighted-projective stabilizers and proving that their coarse images are
singular still belongs to the unformalized stack/coarse-space layer.
-/

namespace TameDelPezzo.NearMiss

open MvPolynomial Polynomial

/-- Algebraic closure used for the geometric points. -/
abbrev GeometricField := AlgebraicClosure (ZMod 3)

/-- The chart point `(t,1,0,0)`. -/
def chartPoint (t : GeometricField) : Coordinate → GeometricField
  | .x0 => t
  | .x1 => 1
  | .y => 0
  | .z => 0

/-- The two coordinate points, indexed by a Boolean. -/
def coordinatePoint : Bool → Coordinate → GeometricField
  | false, .y => 1
  | false, _ => 0
  | true, .z => 1
  | true, _ => 0

/-- Evaluation of the weighted equation on the `x1 = 1` chart. -/
theorem eval_nearMissEquation_chartPoint (t : GeometricField) :
    eval (chartPoint t) (nearMissEquation GeometricField) = t ^ 6 + t + 1 := by
  simp [chartPoint, nearMissEquation]

/-- Every root of the binary sextic produces a point on the hypersurface. -/
theorem chartPoint_on_nearMissEquation
    (t : binarySextic.rootSet GeometricField) :
    eval (chartPoint t) (nearMissEquation GeometricField) = 0 := by
  rw [eval_nearMissEquation_chartPoint]
  simpa [binarySextic] using
    (Polynomial.aeval_eq_zero_of_mem_rootSet t.property)

/-- The chart parametrization is injective. -/
theorem chartPoint_injective : Function.Injective chartPoint := by
  intro s t h
  have hx0 := congr_fun h Coordinate.x0
  simpa [chartPoint] using hx0

/-- A chart point is never the affine origin because its `x1` coordinate is one. -/
theorem chartPoint_ne_zero (t : GeometricField) : chartPoint t ≠ 0 := by
  intro h
  have hx1 := congr_fun h Coordinate.x1
  simpa [chartPoint] using hx1

/-- Both coordinate points satisfy the weighted equation. -/
theorem coordinatePoint_on_nearMissEquation (b : Bool) :
    eval (coordinatePoint b) (nearMissEquation GeometricField) = 0 := by
  cases b <;> simp [coordinatePoint, nearMissEquation]

/-- The two coordinate points are distinct. -/
theorem coordinatePoint_injective : Function.Injective coordinatePoint := by
  intro b c h
  cases b <;> cases c
  · rfl
  · have hy := congr_fun h Coordinate.y
    simp [coordinatePoint] at hy
  · have hy := congr_fun h Coordinate.y
    simp [coordinatePoint] at hy
  · rfl

/-- Neither coordinate point is the affine origin. -/
theorem coordinatePoint_ne_zero (b : Bool) : coordinatePoint b ≠ 0 := by
  cases b
  · intro h
    have hy := congr_fun h Coordinate.y
    simpa [coordinatePoint] using hy
  · intro h
    have hz := congr_fun h Coordinate.z
    simpa [coordinatePoint] using hz

/-- Index type for the six chart points and two coordinate points. -/
abbrev MarkedPointIndex := binarySextic.rootSet GeometricField ⊕ Bool

/-- The eight explicit affine representatives. -/
def markedPoint : MarkedPointIndex → Coordinate → GeometricField
  | Sum.inl t => chartPoint t
  | Sum.inr b => coordinatePoint b

/-- The index type has cardinality eight. -/
theorem markedPointIndex_card : Fintype.card MarkedPointIndex = 8 := by
  unfold MarkedPointIndex
  rw [Fintype.card_sum, binarySextic_six_distinct_geometric_roots]
  decide

/-- All eight marked representatives satisfy the equation. -/
theorem markedPoint_on_nearMissEquation (p : MarkedPointIndex) :
    eval (markedPoint p) (nearMissEquation GeometricField) = 0 := by
  cases p with
  | inl t => exact chartPoint_on_nearMissEquation t
  | inr b => exact coordinatePoint_on_nearMissEquation b

/-- All eight marked representatives are nonzero. -/
theorem markedPoint_ne_zero (p : MarkedPointIndex) : markedPoint p ≠ 0 := by
  cases p with
  | inl t => exact chartPoint_ne_zero t
  | inr b => exact coordinatePoint_ne_zero b

/-- The eight marked affine representatives are pairwise distinct. -/
theorem markedPoint_injective : Function.Injective markedPoint := by
  intro p q h
  cases p with
  | inl t =>
      cases q with
      | inl u =>
          apply Sum.inl_injective
          apply Subtype.ext
          exact chartPoint_injective h
      | inr b =>
          have hx1 := congr_fun h Coordinate.x1
          simp [markedPoint, chartPoint, coordinatePoint] at hx1
  | inr b =>
      cases q with
      | inl t =>
          have hx1 := congr_fun h Coordinate.x1
          simp [markedPoint, chartPoint, coordinatePoint] at hx1
      | inr c =>
          apply Sum.inr_injective
          exact coordinatePoint_injective h

/--
A compact certificate: eight indices, an injective realization, equation
vanishing, and avoidance of the affine origin.
-/
theorem eight_distinct_nonzero_affine_solutions :
    Fintype.card MarkedPointIndex = 8 ∧
      Function.Injective markedPoint ∧
      (∀ p, eval (markedPoint p) (nearMissEquation GeometricField) = 0) ∧
      (∀ p, markedPoint p ≠ 0) := by
  exact ⟨markedPointIndex_card, markedPoint_injective,
    markedPoint_on_nearMissEquation, markedPoint_ne_zero⟩

end TameDelPezzo.NearMiss
