import Mathlib

/-!
# The explicit eight-point near-miss equation

This module formalizes the weighted equation

`y*z + x0^6 + x0*x1^5 + x1^6 = 0` in `P(2,2,5,7)`

over characteristic three. It proves weighted homogeneity, computes the formal
partial derivatives, and proves that the affine Jacobian system has no
nonzero solution. This is the exact quasi-smoothness calculation behind the
near miss; it does not formalize weighted-projective coarse-space geometry.
-/

namespace TameDelPezzo.NearMiss

open MvPolynomial

/-- Coordinates of the weighted affine cone. -/
inductive Coordinate
  | x0 | x1 | y | z
  deriving DecidableEq, Fintype, Repr

/-- The weights `(2,2,5,7)`. -/
def coordinateWeight : Coordinate → Nat
  | .x0 => 2
  | .x1 => 2
  | .y => 5
  | .z => 7

/-- The explicit weighted-degree-twelve hypersurface equation. -/
noncomputable def nearMissEquation (K : Type*) [CommSemiring K] :
    MvPolynomial Coordinate K :=
  X Coordinate.y * X Coordinate.z +
  X Coordinate.x0 ^ 6 +
  X Coordinate.x0 * X Coordinate.x1 ^ 5 +
  X Coordinate.x1 ^ 6

/-- Every monomial in the equation has weighted degree twelve. -/
theorem nearMissEquation_isWeightedHomogeneous
    (K : Type*) [CommSemiring K] :
    IsWeightedHomogeneous coordinateWeight (nearMissEquation K) 12 := by
  have hx0 : IsWeightedHomogeneous coordinateWeight
      (X Coordinate.x0 : MvPolynomial Coordinate K) 2 := by
    simpa [coordinateWeight] using
      (isWeightedHomogeneous_X (R := K) coordinateWeight Coordinate.x0)
  have hx1 : IsWeightedHomogeneous coordinateWeight
      (X Coordinate.x1 : MvPolynomial Coordinate K) 2 := by
    simpa [coordinateWeight] using
      (isWeightedHomogeneous_X (R := K) coordinateWeight Coordinate.x1)
  have hy : IsWeightedHomogeneous coordinateWeight
      (X Coordinate.y : MvPolynomial Coordinate K) 5 := by
    simpa [coordinateWeight] using
      (isWeightedHomogeneous_X (R := K) coordinateWeight Coordinate.y)
  have hz : IsWeightedHomogeneous coordinateWeight
      (X Coordinate.z : MvPolynomial Coordinate K) 7 := by
    simpa [coordinateWeight] using
      (isWeightedHomogeneous_X (R := K) coordinateWeight Coordinate.z)
  have hyz : IsWeightedHomogeneous coordinateWeight
      (X Coordinate.y * X Coordinate.z : MvPolynomial Coordinate K) 12 := by
    convert hy.mul hz using 1
  have hx0six : IsWeightedHomogeneous coordinateWeight
      (X Coordinate.x0 ^ 6 : MvPolynomial Coordinate K) 12 := by
    convert hx0.pow 6 using 1 <;> norm_num
  have hx0x1five : IsWeightedHomogeneous coordinateWeight
      (X Coordinate.x0 * X Coordinate.x1 ^ 5 : MvPolynomial Coordinate K) 12 := by
    convert hx0.mul (hx1.pow 5) using 1 <;> norm_num
  have hx1six : IsWeightedHomogeneous coordinateWeight
      (X Coordinate.x1 ^ 6 : MvPolynomial Coordinate K) 12 := by
    convert hx1.pow 6 using 1 <;> norm_num
  simpa [nearMissEquation] using
    (((hyz.add hx0six).add hx0x1five).add hx1six)

/-- In characteristic three, the `x0` derivative is `x1^5`. -/
theorem nearMissEquation_pderiv_x0
    (K : Type*) [CommSemiring K] [CharP K 3] :
    pderiv Coordinate.x0 (nearMissEquation K) = X Coordinate.x1 ^ 5 := by
  have h6 : (6 : MvPolynomial Coordinate K) = 0 :=
    (CharP.cast_eq_zero_iff _ 3 6).2 (by norm_num)
  simp [nearMissEquation, h6]

/-- The `y` derivative is `z`. -/
theorem nearMissEquation_pderiv_y
    (K : Type*) [CommSemiring K] :
    pderiv Coordinate.y (nearMissEquation K) = X Coordinate.z := by
  simp [nearMissEquation]

/-- The `z` derivative is `y`. -/
theorem nearMissEquation_pderiv_z
    (K : Type*) [CommSemiring K] :
    pderiv Coordinate.z (nearMissEquation K) = X Coordinate.y := by
  simp [nearMissEquation]

/-- In characteristic three, the remaining derivative is `2*x0*x1^4`. -/
theorem nearMissEquation_pderiv_x1
    (K : Type*) [CommSemiring K] [CharP K 3] :
    pderiv Coordinate.x1 (nearMissEquation K) =
      2 * X Coordinate.x0 * X Coordinate.x1 ^ 4 := by
  have h6 : (6 : MvPolynomial Coordinate K) = 0 :=
    (CharP.cast_eq_zero_iff _ 3 6).2 (by norm_num)
  have h5 : (5 : MvPolynomial Coordinate K) = 2 := by
    calc
      (5 : MvPolynomial Coordinate K) = (5 % 3 : Nat) :=
        CharP.cast_eq_mod (R := MvPolynomial Coordinate K) 3 5
      _ = 2 := by norm_num
  simp [nearMissEquation, h6, h5]
  ring

/--
On the hypersurface, simultaneous vanishing of three of the formal partial
derivatives already forces the affine-cone origin.
-/
theorem nearMissEquation_jacobian_zero_only_at_origin
    {K : Type*} [Field K] [CharP K 3]
    (point : Coordinate → K)
    (hEquation : eval point (nearMissEquation K) = 0)
    (hDx0 : eval point (pderiv Coordinate.x0 (nearMissEquation K)) = 0)
    (hDy : eval point (pderiv Coordinate.y (nearMissEquation K)) = 0)
    (hDz : eval point (pderiv Coordinate.z (nearMissEquation K)) = 0) :
    ∀ coordinate, point coordinate = 0 := by
  rw [nearMissEquation_pderiv_x0] at hDx0
  rw [nearMissEquation_pderiv_y] at hDy
  rw [nearMissEquation_pderiv_z] at hDz
  have hx1pow : point Coordinate.x1 ^ 5 = 0 := by simpa using hDx0
  have hx1 : point Coordinate.x1 = 0 := eq_zero_of_pow_eq_zero hx1pow
  have hz : point Coordinate.z = 0 := by simpa using hDy
  have hy : point Coordinate.y = 0 := by simpa using hDz
  have hx0pow : point Coordinate.x0 ^ 6 = 0 := by
    simpa [nearMissEquation, hx1, hy, hz] using hEquation
  have hx0 : point Coordinate.x0 = 0 := eq_zero_of_pow_eq_zero hx0pow
  intro coordinate
  cases coordinate <;> assumption

/--
The punctured affine cone is Jacobian-regular: every nonzero solution has at
least one nonvanishing formal partial derivative.
-/
theorem nearMissEquation_punctured_cone_regular
    {K : Type*} [Field K] [CharP K 3]
    (point : Coordinate → K)
    (hEquation : eval point (nearMissEquation K) = 0)
    (hNonzero : point ≠ 0) :
    ¬ ∀ coordinate,
      eval point (pderiv coordinate (nearMissEquation K)) = 0 := by
  intro hAll
  apply hNonzero
  funext coordinate
  exact nearMissEquation_jacobian_zero_only_at_origin point hEquation
    (hAll Coordinate.x0) (hAll Coordinate.y) (hAll Coordinate.z) coordinate

end TameDelPezzo.NearMiss
