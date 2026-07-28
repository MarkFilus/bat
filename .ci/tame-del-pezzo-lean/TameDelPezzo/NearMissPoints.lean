import TameDelPezzo.BinarySextic
import TameDelPezzo.NearMiss

namespace TameDelPezzo.NearMiss

/-- Six sextic points together with the two coordinate points. -/
def visibleSingularPoints : Type :=
  binarySextic.rootSet (AlgebraicClosure (ZMod 3)) ⊕ Fin 2

/-- The concrete point type has exactly eight elements. -/
theorem visibleSingularPoints_card :
    Fintype.card visibleSingularPoints = 8 := by
  simp [visibleSingularPoints, binarySextic_six_distinct_geometric_roots]

/-- The near miss simultaneously has eight visible points and Picard rank six. -/
theorem eight_points_but_rank_six :
    Fintype.card visibleSingularPoints = 8 ∧ (14 - 8 : Nat) = 6 := by
  exact ⟨visibleSingularPoints_card, coarse_picard_rank⟩

/-- It therefore cannot satisfy the rank-one hypothesis of the target problem. -/
theorem eight_point_near_miss_not_rank_one :
    Fintype.card visibleSingularPoints = 8 ∧ (14 - 8 : Nat) ≠ 1 := by
  exact ⟨visibleSingularPoints_card, rank_is_not_one⟩

end TameDelPezzo.NearMiss
