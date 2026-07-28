import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

namespace TameDelPezzo.NearMiss

theorem fano_index : 2 + 2 + 5 + 7 - 12 = 4 := by norm_num

theorem hyperplane_square :
    (12 : ℚ) / (2 * 2 * 5 * 7) = 3 / 35 := by norm_num

theorem canonical_square :
    (4 : ℚ)^2 * (3 / 35) = 48 / 35 := by norm_num

theorem resolved_canonical_square :
    (48 : ℚ) / 35 - 9 / 5 - 25 / 7 = -4 := by norm_num

theorem resolution_picard_rank : 10 - (-4 : ℤ) = 14 := by norm_num

theorem coarse_picard_rank : 14 - 8 = 6 := by norm_num

theorem six_vanishes_mod_three : (6 : ZMod 3) = 0 := by norm_num

theorem one_survives_mod_three : (1 : ZMod 3) ≠ 0 := by norm_num

theorem rank_is_not_one : (6 : Nat) ≠ 1 := by norm_num

end TameDelPezzo.NearMiss
