import TameDelPezzo.KernelSemantics
import TameDelPezzo.ComplementaryDivisors

/-!
# All-orders proof for a direct coordinate-kernel enumerator

This file turns the direct finite enumeration of pseudoreflection exponents into
an exact theorem. The exponent `r` is inserted explicitly as the neutral
fallback generator; all exponents below `r` that fix either tangent coordinate
are then included. Their gcd is proved to be the gcd of the two exact coordinate
kernel generators.
-/

namespace TameDelPezzo.CyclicQuotient

/-- Exponents used by the semantic direct enumerator. -/
def coordinateKernelExponents (r a b : Nat) : Finset Nat :=
  insert r <| (Finset.range r).filter fun k => inCoordinateKernel r a b k = true

/-- Gcd of every exponent lying in either coordinate kernel, together with `r`. -/
def reflectionGeneratorGCDFinset (r a b : Nat) : Nat :=
  (coordinateKernelExponents r a b).gcd id

/-- The resulting direct-enumeration smoothness test. -/
def cstSmoothFinset (r a b : Nat) : Bool :=
  reflectionGeneratorGCDFinset r a b == 1

/-- Exact membership description for the enumerated exponent set. -/
theorem mem_coordinateKernelExponents {r a b k : Nat} (hr : 0 < r) :
    k ∈ coordinateKernelExponents r a b ↔
      k = r ∨ (k < r ∧
        (r / Nat.gcd r a ∣ k ∨ r / Nat.gcd r b ∣ k)) := by
  simp [coordinateKernelExponents, inCoordinateKernel_eq_true_iff hr, eq_comm]

/-- The first coordinate-kernel generator divides the cyclic order. -/
theorem first_kernel_generator_dvd_order {r a : Nat} :
    r / Nat.gcd r a ∣ r := by
  exact ⟨Nat.gcd r a, (Nat.div_mul_cancel (Nat.gcd_dvd_left r a)).symm⟩

/-- The second copy of the same elementary divisor fact. -/
theorem second_kernel_generator_dvd_order {r b : Nat} :
    r / Nat.gcd r b ∣ r := by
  exact ⟨Nat.gcd r b, (Nat.div_mul_cancel (Nat.gcd_dvd_left r b)).symm⟩

/-- The first exact kernel generator occurs in the enumerated exponent set. -/
theorem first_kernel_generator_mem {r a b : Nat} (hr : 0 < r) :
    r / Nat.gcd r a ∈ coordinateKernelExponents r a b := by
  rw [mem_coordinateKernelExponents hr]
  by_cases h : r / Nat.gcd r a = r
  · exact Or.inl h
  · right
    constructor
    · have hle := Nat.le_of_dvd hr
        (first_kernel_generator_dvd_order (r := r) (a := a))
      omega
    · exact Or.inl (dvd_refl _)

/-- The second exact kernel generator occurs in the enumerated exponent set. -/
theorem second_kernel_generator_mem {r a b : Nat} (hr : 0 < r) :
    r / Nat.gcd r b ∈ coordinateKernelExponents r a b := by
  rw [mem_coordinateKernelExponents hr]
  by_cases h : r / Nat.gcd r b = r
  · exact Or.inl h
  · right
    constructor
    · have hle := Nat.le_of_dvd hr
        (second_kernel_generator_dvd_order (r := r) (b := b))
      omega
    · exact Or.inr (dvd_refl _)

/--
The direct enumerator's gcd is exactly the gcd of the two coordinate-kernel
generators, for every positive cyclic order.
-/
theorem reflectionGeneratorGCDFinset_eq_gcd {r a b : Nat} (hr : 0 < r) :
    reflectionGeneratorGCDFinset r a b =
      Nat.gcd (r / Nat.gcd r a) (r / Nat.gcd r b) := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · exact Finset.gcd_dvd (first_kernel_generator_mem hr)
    · exact Finset.gcd_dvd (second_kernel_generator_mem hr)
  · apply Finset.dvd_gcd
    intro k hk
    rw [mem_coordinateKernelExponents hr] at hk
    rcases hk with hkEq | ⟨_, hk⟩
    · subst k
      exact Nat.dvd_trans (Nat.gcd_dvd_left _ _)
        (first_kernel_generator_dvd_order (r := r) (a := a))
    · rcases hk with hka | hkb
      · exact Nat.dvd_trans (Nat.gcd_dvd_left _ _) hka
      · exact Nat.dvd_trans (Nat.gcd_dvd_right _ _) hkb

/-- The semantic direct enumerator is true exactly under the coprimality test. -/
theorem cstSmoothFinset_eq_true_iff_coprime {r a b : Nat} (hr : 0 < r) :
    cstSmoothFinset r a b = true ↔
      Nat.Coprime (r / Nat.gcd r a) (r / Nat.gcd r b) := by
  rw [cstSmoothFinset, reflectionGeneratorGCDFinset_eq_gcd hr]
  simp [Nat.coprime_iff_gcd_eq_one]

/-- The semantic direct enumerator satisfies the stabilizer-lcm criterion. -/
theorem cstSmoothFinset_eq_true_iff_lcm {r a b : Nat} (hr : 0 < r) :
    cstSmoothFinset r a b = true ↔
      Nat.lcm (Nat.gcd r a) (Nat.gcd r b) = r := by
  rw [cstSmoothFinset_eq_true_iff_coprime hr,
    primary_coprime_iff_stabilizer_lcm hr]

/-- The closed formula and direct finite-set enumerator agree for every positive order. -/
theorem cstSmoothPrimary_eq_cstSmoothFinset {r a b : Nat} (hr : 0 < r) :
    cstSmoothPrimary r a b = cstSmoothFinset r a b := by
  apply Bool.eq_iff_iff.mpr
  rw [cstSmoothPrimary_eq_true_iff_lcm hr,
    cstSmoothFinset_eq_true_iff_lcm hr]

end TameDelPezzo.CyclicQuotient
