import Mathlib

namespace TameDelPezzo.CyclicQuotient

def cstSmoothPrimary (r a b : Nat) : Bool :=
  Nat.gcd (r / Nat.gcd r a) (r / Nat.gcd r b) == 1

def inCoordinateKernel (r a b k : Nat) : Bool :=
  ((a * k) % r == 0) || ((b * k) % r == 0)

def reflectionGeneratorGCD (r a b : Nat) : Nat :=
  ((List.range r).filter (fun k => inCoordinateKernel r a b k)).foldl Nat.gcd r

def cstSmoothEnumerated (r a b : Nat) : Bool :=
  reflectionGeneratorGCD r a b == 1

def implementationsAgreeUpTo (bound : Nat) : Bool :=
  (List.range (bound + 1)).all fun r =>
    if r < 2 then true
    else
      (List.range r).all fun a =>
        (List.range r).all fun b =>
          cstSmoothPrimary r a b == cstSmoothEnumerated r a b

def representationCount (bound : Nat) : Nat :=
  ((List.range (bound + 1)).filter (fun r => 2 ≤ r)).foldl
    (fun acc r => acc + r * r) 0

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

/-- The larger independent comparison uses Lean's native evaluator. -/
theorem independent_agreement_through_48 : implementationsAgreeUpTo 48 = true := by
  native_decide

/-- Exact size of the independent comparison. -/
theorem independent_representation_count : representationCount 48 = 38023 := by
  native_decide

/-- Exact size of the larger closed-form sweep. -/
theorem primary_representation_count : representationCount 256 = 5625215 := by
  native_decide

/-- Exact smooth count in the larger sweep. -/
theorem primary_smooth_count : smoothCount 256 = 116075 := by
  native_decide

end TameDelPezzo.CyclicQuotient
