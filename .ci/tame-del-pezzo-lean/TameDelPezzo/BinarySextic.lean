import Mathlib

namespace TameDelPezzo.NearMiss

open Polynomial

def binarySextic : (ZMod 3)[X] := X ^ 6 + X + 1

theorem binarySextic_derivative : derivative binarySextic = 1 := by
  have h6 : (6 : ZMod 3) = 0 := by native_decide
  simp [binarySextic, derivative_X_pow, h6]

theorem binarySextic_natDegree : binarySextic.natDegree = 6 := by
  native_decide

theorem binarySextic_separable : binarySextic.Separable := by
  rw [Polynomial.separable_def, binarySextic_derivative]
  exact isCoprime_one_right

theorem binarySextic_six_distinct_geometric_roots :
    Fintype.card (binarySextic.rootSet (AlgebraicClosure (ZMod 3))) = 6 := by
  rw [Polynomial.card_rootSet_eq_natDegree binarySextic_separable
    (IsAlgClosed.splits _), binarySextic_natDegree]

end TameDelPezzo.NearMiss
