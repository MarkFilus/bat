import Mathlib

namespace TameDelPezzo

structure CharZeroBridge where
  specialSing : Type
  genericSing : Type
  specialFinite : Fintype specialSing
  genericFinite : Fintype genericSing
  persist : specialSing → genericSing
  persist_injective : Function.Injective persist
  rho : Nat
  rho_eq_one : rho = 1
  charZeroBound : Fintype.card genericSing ≤ 2 * rho + 2

attribute [instance] CharZeroBridge.specialFinite CharZeroBridge.genericFinite

theorem card_special_le_four (B : CharZeroBridge) :
    Fintype.card B.specialSing ≤ 4 := by
  calc
    Fintype.card B.specialSing ≤ Fintype.card B.genericSing :=
      Fintype.card_le_of_injective B.persist B.persist_injective
    _ ≤ 2 * B.rho + 2 := B.charZeroBound
    _ = 4 := by simp [B.rho_eq_one]

theorem not_seven_singularities (B : CharZeroBridge) :
    ¬ 7 ≤ Fintype.card B.specialSing := by
  have h := card_special_le_four B
  omega

theorem not_eight_singularities (B : CharZeroBridge) :
    ¬ 8 ≤ Fintype.card B.specialSing := by
  have h := card_special_le_four B
  omega

theorem card_special_le_four_of_generic_bound
    {S G : Type} [Fintype S] [Fintype G]
    (persist : S → G) (hinj : Function.Injective persist)
    (hgeneric : Fintype.card G ≤ 4) :
    Fintype.card S ≤ 4 := by
  exact (Fintype.card_le_of_injective persist hinj).trans hgeneric

end TameDelPezzo
