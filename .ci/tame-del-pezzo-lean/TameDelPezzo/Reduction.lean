import Mathlib

namespace TameDelPezzo

/--
The exact abstract bridge required from mixed-characteristic geometry.
No geometric theorem is hidden in this structure: persistence, Picard rank,
and the characteristic-zero inequality are explicit fields.
-/
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

/-- Persistence transfers the full characteristic-zero `2ρ+2` bound. -/
theorem card_special_le_two_mul_rho_add_two (B : CharZeroBridge) :
    Fintype.card B.specialSing ≤ 2 * B.rho + 2 := by
  exact (Fintype.card_le_of_injective B.persist B.persist_injective).trans
    B.charZeroBound

/-- At geometric Picard rank one, the special fiber has at most four singularities. -/
theorem card_special_le_four (B : CharZeroBridge) :
    Fintype.card B.specialSing ≤ 4 := by
  calc
    Fintype.card B.specialSing ≤ 2 * B.rho + 2 :=
      card_special_le_two_mul_rho_add_two B
    _ = 4 := by simp [B.rho_eq_one]

/-- Equivalently, five or more singularities are impossible. -/
theorem not_five_singularities (B : CharZeroBridge) :
    ¬ 5 ≤ Fintype.card B.specialSing := by
  have h := card_special_le_four B
  omega

/-- The benchmark's seven-point threshold is impossible under the bridge. -/
theorem not_seven_singularities (B : CharZeroBridge) :
    ¬ 7 ≤ Fintype.card B.specialSing := by
  exact fun h => not_five_singularities B (by omega)

/-- The benchmark's eight-point target is impossible under the bridge. -/
theorem not_eight_singularities (B : CharZeroBridge) :
    ¬ 8 ≤ Fintype.card B.specialSing := by
  exact fun h => not_five_singularities B (by omega)

/-- Direct finite-set form when a four-point generic bound is already available. -/
theorem card_special_le_four_of_generic_bound
    {S G : Type} [Fintype S] [Fintype G]
    (persist : S → G) (hinj : Function.Injective persist)
    (hgeneric : Fintype.card G ≤ 4) :
    Fintype.card S ≤ 4 := by
  exact (Fintype.card_le_of_injective persist hinj).trans hgeneric

end TameDelPezzo
