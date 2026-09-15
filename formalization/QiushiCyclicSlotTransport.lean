import QiushiConversion
import QiushiOccupation
import QiushiSplitRankBound
import QiushiTransposeTransport

/-!
# Cyclic slot transport

For the convention `tensorEntry` = `tr(A B Cᵀ)`, the correct cyclic action is
`(A,B,C) ↦ (B,Cᵀ,Aᵀ)`.  This file proves the transformation directly from
coordinates and does not use `QiushiOrbitInvariance`.
-/

open Matrix BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section

namespace QiushiMatmul

lemma tensorEntry_cycle (a b c : Coord9) :
    tensorEntry a b c = tensorEntry (c.2, c.1) a (b.2, b.1) := by
  simp only [tensorEntry]
  congr 1
  aesop

/-- Convention-preserving cyclic rotation `(A,B,C) ↦ (B,Cᵀ,Aᵀ)`. -/
def cycleEntryDecomp {r : Nat} (D : TensorEntryDecomp r) :
    TensorEntryDecomp r where
  A := D.B
  B := fun t => (D.C t).transpose
  C := fun t => (D.A t).transpose
  entry_identity := by
    intro a b c
    rw [tensorEntry_cycle, D.entry_identity]
    apply Finset.sum_congr rfl
    intro t _
    simp only [Matrix.transpose_apply]
    ring

@[simp] lemma cycleEntryDecomp_A {r : Nat} (D : TensorEntryDecomp r)
    (t : Fin r) : (cycleEntryDecomp D).A t = D.B t := rfl

@[simp] lemma cycleEntryDecomp_B {r : Nat} (D : TensorEntryDecomp r)
    (t : Fin r) : (cycleEntryDecomp D).B t = (D.C t).transpose := rfl

@[simp] lemma cycleEntryDecomp_C {r : Nat} (D : TensorEntryDecomp r)
    (t : Fin r) : (cycleEntryDecomp D).C t = (D.A t).transpose := rfl

theorem cycleEntryDecomp_thrice {r : Nat} (D : TensorEntryDecomp r) :
    cycleEntryDecomp (cycleEntryDecomp (cycleEntryDecomp D)) = D := by
  cases D
  rfl

/-- The A-split theorem transported once gives the B-slot rank bound. -/
theorem split_rank_bound_B {r : Nat} (D : TensorEntryDecomp r) :
    27 ≤ ∑ t : Fin r, (D.B t).rank := by
  simpa using split_rank_bound_from_entrywise (cycleEntryDecomp D)

/-- Two cyclic rotations put `Cᵀ` in the A slot; transpose preserves rank. -/
theorem split_rank_bound_C {r : Nat} (D : TensorEntryDecomp r) :
    27 ≤ ∑ t : Fin r, (D.C t).rank := by
  have h := split_rank_bound_from_entrywise
    (cycleEntryDecomp (cycleEntryDecomp D))
  simpa only [cycleEntryDecomp_A, cycleEntryDecomp_B,
    Matrix.rank_transpose] using h

/-- A full decomposition, cyclically rotated and then quotiented in its A
slot, is an A-quotient decomposition whose first factors are the original
B-factors. -/
def BSlotQuotientDecomp {r : Nat} (D : TensorEntryDecomp r)
    (W : Submodule F2 Mat3) : QuotientTensorDecomp W r :=
  entrywise_to_quotient (cycleEntryDecomp D) W

@[simp] lemma BSlotQuotientDecomp_A {r : Nat} (D : TensorEntryDecomp r)
    (W : Submodule F2 Mat3) (t : Fin r) :
    (BSlotQuotientDecomp D W).A t = D.B t := rfl

/-- Generic occupation transport to the B slot. -/
theorem B_slot_occupation_cap {r n : Nat} (D : TensorEntryDecomp r)
    (W : Submodule F2 Mat3) (hW : QuotientRankAtLeast W n) (hn : n ≤ r) :
    (Finset.univ.filter fun t : Fin r => D.B t ∈ W).card ≤ r - n := by
  let D0 : QuotientTensorDecomp (⊥ : Submodule F2 Mat3) r :=
    BSlotQuotientDecomp D ⊥
  have hocc := occupation_inequality
    (show (⊥ : Submodule F2 Mat3) ≤ W from bot_le) D0 hW hn
  simpa [killSet, D0, BSlotQuotientDecomp, entrywise_to_quotient,
    cycleEntryDecomp] using hocc

end QiushiMatmul
end
