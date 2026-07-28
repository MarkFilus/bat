import TameDelPezzo.CyclicQuotient

/-!
# Complementary divisors reverse gcd and lcm

For positive `r`, the involution `x ↦ r / x` on divisors of `r` reverses
`gcd` and `lcm`. This proves the number-theoretic content of the primary cyclic
pseudoreflection test for every cyclic order, replacing bounded evidence by an
all-orders theorem.
-/

namespace TameDelPezzo.CyclicQuotient

/-- Dividing twice by complementary divisors returns the original divisor. -/
theorem complementary_divisor_involution {r x : Nat} (hr : 0 < r) (hx : x ∣ r) :
    r / (r / x) = x := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
    omega
  have hxle : x ≤ r := Nat.le_of_dvd hr hx
  have hquot : 0 < r / x := Nat.div_pos hxle (Nat.pos_of_ne_zero hx0)
  apply Nat.div_eq_of_eq_mul_left hquot
  simpa [Nat.mul_comm] using (Nat.div_mul_cancel hx).symm

/-- The complementary-divisor map sends gcd to lcm. -/
theorem lcm_eq_div_gcd_complements {r x y : Nat} (hr : 0 < r)
    (hx : x ∣ r) (hy : y ∣ r) :
    x.lcm y = r / ((r / x).gcd (r / y)) := by
  have hqx : r / x ∣ r := ⟨x, (Nat.div_mul_cancel hx).symm⟩
  have hqy : r / y ∣ r := ⟨y, (Nat.div_mul_cancel hy).symm⟩
  have h := Nat.div_lcm_eq_div_gcd hqx hqy
  rw [complementary_divisor_involution hr hx,
    complementary_divisor_involution hr hy] at h
  exact h

/-- Complementary divisors are coprime exactly when the originals span `r`. -/
theorem coprime_complements_iff_lcm_eq {r x y : Nat} (hr : 0 < r)
    (hx : x ∣ r) (hy : y ∣ r) :
    Nat.Coprime (r / x) (r / y) ↔ x.lcm y = r := by
  rw [Nat.coprime_iff_gcd_eq_one]
  have hdual := lcm_eq_div_gcd_complements hr hx hy
  constructor
  · intro hgcd
    rw [hdual, hgcd]
    simp
  · intro hlcm
    have hquot : r / ((r / x).gcd (r / y)) = r := by
      rw [← hdual, hlcm]
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
      omega
    have hxle : x ≤ r := Nat.le_of_dvd hr hx
    have hcomplement : 0 < r / x := Nat.div_pos hxle (Nat.pos_of_ne_zero hx0)
    have hgcdpos : 0 < (r / x).gcd (r / y) :=
      Nat.gcd_pos_of_pos_left _ hcomplement
    have hgcdle : (r / x).gcd (r / y) ≤ 1 := by
      by_contra h
      have hgt : 1 < (r / x).gcd (r / y) := by omega
      have hlt := Nat.div_lt_self hr hgt
      omega
    omega

/-- Conceptual form of the cyclic smoothness condition, for every positive order. -/
theorem primary_coprime_iff_stabilizer_lcm {r a b : Nat} (hr : 0 < r) :
    Nat.Coprime (r / Nat.gcd r a) (r / Nat.gcd r b) ↔
      Nat.lcm (Nat.gcd r a) (Nat.gcd r b) = r :=
  coprime_complements_iff_lcm_eq hr (Nat.gcd_dvd_left r a) (Nat.gcd_dvd_left r b)

/-- The executable boolean is exactly the coprimality proposition. -/
theorem cstSmoothPrimary_eq_true_iff_coprime {r a b : Nat} :
    cstSmoothPrimary r a b = true ↔
      Nat.Coprime (r / Nat.gcd r a) (r / Nat.gcd r b) := by
  simp [cstSmoothPrimary, Nat.coprime_iff_gcd_eq_one]

/-- The executable test is equivalent to the all-orders stabilizer-lcm criterion. -/
theorem cstSmoothPrimary_eq_true_iff_lcm {r a b : Nat} (hr : 0 < r) :
    cstSmoothPrimary r a b = true ↔
      Nat.lcm (Nat.gcd r a) (Nat.gcd r b) = r := by
  rw [cstSmoothPrimary_eq_true_iff_coprime,
    primary_coprime_iff_stabilizer_lcm hr]

end TameDelPezzo.CyclicQuotient
