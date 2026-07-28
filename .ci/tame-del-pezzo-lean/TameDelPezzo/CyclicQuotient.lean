import Mathlib

/-!
# Cyclic quotient calculations

The boolean `cstSmoothPrimary` implements the closed cyclic
Chevalley--Shephard--Todd test. `cstSmoothEnumerated` is a deliberately separate
implementation that enumerates coordinate-kernel elements and computes the gcd
of their exponents.

Only the bounded comparison through order 16 is stored as a kernel proof in
this module. Larger sweeps are runtime regression checks, not theorem axioms.
The all-orders proof is in `ComplementaryDivisors.lean`.
-/

namespace TameDelPezzo.CyclicQuotient

/-- Closed-form smoothness test for the effective cyclic tangent action. -/
def cstSmoothPrimary (r a b : Nat) : Bool :=
  Nat.gcd (r / Nat.gcd r a) (r / Nat.gcd r b) == 1

/-- Does exponent `k` act trivially on at least one tangent coordinate? -/
def inCoordinateKernel (r a b k : Nat) : Bool :=
  ((a * k) % r == 0) || ((b * k) % r == 0)

/-- Gcd of the exponents belonging to the two coordinate kernels. -/
def reflectionGeneratorGCD (r a b : Nat) : Nat :=
  ((List.range r).filter (fun k => inCoordinateKernel r a b k)).foldl Nat.gcd r

/-- Independent enumeration-based smoothness test. -/
def cstSmoothEnumerated (r a b : Nat) : Bool :=
  reflectionGeneratorGCD r a b == 1

/-- Compare both implementations for every character pair through `bound`. -/
def implementationsAgreeUpTo (bound : Nat) : Bool :=
  (List.range (bound + 1)).all fun r =>
    if r < 2 then true
    else
      (List.range r).all fun a =>
        (List.range r).all fun b =>
          cstSmoothPrimary r a b == cstSmoothEnumerated r a b

/-- Number of character pairs with cyclic orders from two through `bound`. -/
def representationCount (bound : Nat) : Nat :=
  ((List.range (bound + 1)).filter (fun r => 2 ≤ r)).foldl
    (fun acc r => acc + r * r) 0

/-- Number classified smooth by the primary formula through `bound`. -/
def smoothCount (bound : Nat) : Nat :=
  ((List.range (bound + 1)).filter (fun r => 2 ≤ r)).foldl
    (fun acc r =>
      acc + ((List.range r).foldl
        (fun accA a =>
          accA + ((List.range r).foldl
            (fun accB b => if cstSmoothPrimary r a b then accB + 1 else accB) 0)) 0)) 0

/-- Small edge cases checked by ordinary kernel reduction. -/
theorem edge_mu6_2_3 : cstSmoothPrimary 6 2 3 = true := by decide
theorem edge_mu5_1_1 : cstSmoothPrimary 5 1 1 = false := by decide
theorem edge_mu5_0_1 : cstSmoothPrimary 5 0 1 = true := by decide
theorem edge_mu2_1_1 : cstSmoothPrimary 2 1 1 = false := by decide
theorem edge_trivial_mu7 : cstSmoothPrimary 7 0 0 = true := by decide

/-- A pure-kernel exhaustive comparison on all 1,495 pairs through order 16. -/
theorem kernel_agreement_through_16 : implementationsAgreeUpTo 16 = true := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
    decide

/-- Exact size of the pure-kernel comparison. -/
theorem kernel_representation_count : representationCount 16 = 1495 := by
  decide

end TameDelPezzo.CyclicQuotient
