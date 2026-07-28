import Mathlib

namespace TameDelPezzo.TameArithmetic

theorem divisor_coprime_three {r w : Nat} (hdiv : r ∣ w)
    (hw : Nat.Coprime w 3) : Nat.Coprime r 3 := by
  exact hw.of_dvd_left hdiv

theorem near_miss_weights_tame :
    Nat.Coprime 2 3 ∧ Nat.Coprime 2 3 ∧ Nat.Coprime 5 3 ∧ Nat.Coprime 7 3 := by
  decide

end TameDelPezzo.TameArithmetic
