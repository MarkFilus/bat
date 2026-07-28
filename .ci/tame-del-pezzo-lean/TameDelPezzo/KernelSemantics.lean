import TameDelPezzo.CyclicQuotient

/-!
# Semantics of cyclic coordinate kernels

For a cyclic action of order `r` with character `a`, the kernel exponents are
exactly the multiples of `r / gcd r a`. This identifies the direct enumerator
with the standard generator description rather than treating it as opaque code.
-/

namespace TameDelPezzo.CyclicQuotient

/-- A character kills exponent `k` exactly when its kernel generator divides `k`. -/
theorem character_vanishes_iff_generator_dvd {r a k : Nat} (hr : 0 < r) :
    (a * k) % r = 0 ↔ r / Nat.gcd r a ∣ k := by
  let d := Nat.gcd r a
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left a hr
  have hdr : d ∣ r := Nat.gcd_dvd_left r a
  have hda : d ∣ a := Nat.gcd_dvd_right r a
  have hcop : Nat.Coprime (r / d) (a / d) :=
    Nat.coprime_div_gcd_div_gcd hdpos
  rw [← Nat.dvd_iff_mod_eq_zero]
  constructor
  · intro hdiv
    have hdiv' := hdiv
    rw [← Nat.div_mul_cancel hdr, ← Nat.div_mul_cancel hda] at hdiv'
    have hscaled : (r / d) * d ∣ ((a / d) * k) * d := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hdiv'
    have hreduced : r / d ∣ (a / d) * k :=
      (Nat.mul_dvd_mul_iff_right hdpos).mp hscaled
    exact hcop.dvd_of_dvd_mul_left hreduced
  · intro hk
    change r / d ∣ k at hk
    rcases hk with ⟨t, rfl⟩
    refine ⟨(a / d) * t, ?_⟩
    calc
      a * (r / d * t) = (a / d * d) * (r / d * t) := by
        rw [Nat.div_mul_cancel hda]
      _ = (r / d * d) * (a / d * t) := by ring
      _ = r * (a / d * t) := by
        rw [Nat.div_mul_cancel hdr]

/-- Boolean form used by the direct coordinate-kernel implementation. -/
theorem inCoordinateKernel_eq_true_iff {r a b k : Nat} (hr : 0 < r) :
    inCoordinateKernel r a b k = true ↔
      r / Nat.gcd r a ∣ k ∨ r / Nat.gcd r b ∣ k := by
  simp [inCoordinateKernel, character_vanishes_iff_generator_dvd hr]

/-- Each first-coordinate kernel generator is detected by the enumerator. -/
theorem first_kernel_generator_is_enumerated {r a b : Nat} (hr : 0 < r) :
    inCoordinateKernel r a b (r / Nat.gcd r a) = true := by
  rw [inCoordinateKernel_eq_true_iff hr]
  exact Or.inl (dvd_refl _)

/-- Each second-coordinate kernel generator is detected by the enumerator. -/
theorem second_kernel_generator_is_enumerated {r a b : Nat} (hr : 0 < r) :
    inCoordinateKernel r a b (r / Nat.gcd r b) = true := by
  rw [inCoordinateKernel_eq_true_iff hr]
  exact Or.inr (dvd_refl _)

end TameDelPezzo.CyclicQuotient
