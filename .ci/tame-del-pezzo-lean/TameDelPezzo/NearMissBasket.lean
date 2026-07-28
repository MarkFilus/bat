import TameDelPezzo.CyclicQuotient
import TameDelPezzo.NearMissMarkedPoints

/-!
# Exact local basket data for the near miss

This module records the cyclic tangent-character data predicted by the weighted
quotient charts:

* the six chart points have type `1/2(1,1)`;
* `(0:0:1:0)` has type `1/5(2,2)`;
* `(0:0:0:1)` has type `1/7(2,2)`.

Lean checks that every order is prime to characteristic three and that every
listed representation fails the cyclic pseudoreflection smoothness test. It
also checks the exact correction arithmetic used in the Picard-rank diagnosis.

The assignment of these representations to coarse weighted-projective local
charts remains geometric input; this file does not pretend that coarse moduli
spaces are already formalized in mathlib.
-/

namespace TameDelPezzo.NearMiss

open TameDelPezzo.CyclicQuotient

/-- A cyclic surface tangent representation `1/r(a,b)`. -/
structure CyclicTangentType where
  order : Nat
  firstCharacter : Nat
  secondCharacter : Nat
  deriving DecidableEq, Repr

/-- The local cyclic data attached to each of the eight marked points. -/
noncomputable def markedCyclicTangentType : MarkedPointIndex → CyclicTangentType
  | Sum.inl _ => ⟨2, 1, 1⟩
  | Sum.inr false => ⟨5, 2, 2⟩
  | Sum.inr true => ⟨7, 2, 2⟩

/-- The six binary-sextic points carry the `1/2(1,1)` data. -/
theorem chartPoint_cyclic_type (t : binarySextic.rootSet GeometricField) :
    markedCyclicTangentType (Sum.inl t) = ⟨2, 1, 1⟩ := rfl

/-- The `y` coordinate point carries the `1/5(2,2)` data. -/
theorem yCoordinatePoint_cyclic_type :
    markedCyclicTangentType (Sum.inr false) = ⟨5, 2, 2⟩ := rfl

/-- The `z` coordinate point carries the `1/7(2,2)` data. -/
theorem zCoordinatePoint_cyclic_type :
    markedCyclicTangentType (Sum.inr true) = ⟨7, 2, 2⟩ := rfl

/-- Every listed stabilizer order is positive. -/
theorem markedCyclicTangentType_order_positive (p : MarkedPointIndex) :
    0 < (markedCyclicTangentType p).order := by
  cases p with
  | inl t => norm_num [markedCyclicTangentType]
  | inr b => cases b <;> norm_num [markedCyclicTangentType]

/-- Every listed stabilizer is tame in characteristic three. -/
theorem markedCyclicTangentType_tame (p : MarkedPointIndex) :
    Nat.Coprime (markedCyclicTangentType p).order 3 := by
  cases p with
  | inl t => decide
  | inr b => cases b <;> decide

/-- Every listed tangent representation gives a singular cyclic quotient. -/
theorem markedCyclicTangentType_singular (p : MarkedPointIndex) :
    cstSmoothPrimary
      (markedCyclicTangentType p).order
      (markedCyclicTangentType p).firstCharacter
      (markedCyclicTangentType p).secondCharacter = false := by
  cases p with
  | inl t => decide
  | inr b => cases b <;> decide

/-- The six chart indices have cardinality six. -/
theorem chart_basket_multiplicity :
    Fintype.card (binarySextic.rootSet GeometricField) = 6 :=
  binarySextic_six_distinct_geometric_roots

/-- Correction attached to a scalar cyclic type `1/r(1,1)`. -/
def scalarResolutionCorrection (r : Nat) : Rat :=
  ((r : Rat) - 2) ^ 2 / r

/-- An `A₁ = 1/2(1,1)` point contributes zero to this correction. -/
theorem orderTwo_scalarResolutionCorrection :
    scalarResolutionCorrection 2 = 0 := by
  norm_num [scalarResolutionCorrection]

/-- The order-five scalar correction is `9/5`. -/
theorem orderFive_scalarResolutionCorrection :
    scalarResolutionCorrection 5 = 9 / 5 := by
  norm_num [scalarResolutionCorrection]

/-- The order-seven scalar correction is `25/7`. -/
theorem orderSeven_scalarResolutionCorrection :
    scalarResolutionCorrection 7 = 25 / 7 := by
  norm_num [scalarResolutionCorrection]

/-- The two noncanonical scalar corrections sum to `188/35`. -/
theorem noncanonical_correction_sum :
    scalarResolutionCorrection 5 + scalarResolutionCorrection 7 = 188 / 35 := by
  norm_num [scalarResolutionCorrection]

/-- Subtracting those corrections from `48/35` gives resolution square `-4`. -/
theorem correction_recovers_resolution_square :
    (48 : Rat) / 35 -
      (scalarResolutionCorrection 5 + scalarResolutionCorrection 7) = -4 := by
  norm_num [scalarResolutionCorrection]

end TameDelPezzo.NearMiss
