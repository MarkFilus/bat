import Mathlib

namespace TameDelPezzo.NearMiss

open Polynomial

noncomputable def binarySextic : (ZMod 3)[X] := X ^ 6 + X + 1

theorem binarySextic_derivative : derivative binarySextic = 1 := by
  simp [binarySextic]
  norm_num

theorem binarySextic_natDegree : binarySextic.natDegree = 6 := by
  change ((X ^ 6 + X + C 1 : (ZMod 3)[X])).natDegree = 6
  rw [natDegree_add_C]
  rw [natDegree_add_eq_left_of_natDegree_lt]
  · simp
  · norm_num

theorem binarySextic_separable : binarySextic.Separable := by
  rw [Polynomial.separable_def, binarySextic_derivative]
  exact isCoprime_one_right

theorem binarySextic_six_distinct_geometric_roots :
    Fintype.card (binarySextic.rootSet (AlgebraicClosure (ZMod 3))) = 6 := by
  rw [Polynomial.card_rootSet_eq_natDegree binarySextic_separable
    (IsAlgClosed.splits _), binarySextic_natDegree]

end TameDelPezzo.NearMiss
