import QiushiConversion
import QiushiCyclicSlotTransport
import QiushiMatmulFinitePremises
import QiushiOccupation

/-!
# Reusable length-21 occupation caps

These are direct instances of `occupation_inequality`; they add no finite
premises.  Indexed dispatchers package all three named lines, all eight named
all-high planes, and all fourteen named affine hyperplanes.
-/

open Matrix BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section

namespace QiushiMatmul

def tailLineSubspace (i : Fin 3) : Submodule F2 Mat3 :=
  match i.val with
  | 0 => lineRank1
  | 1 => lineRank2
  | _ => lineRank3

def tailPlaneSubspace (i : Fin 8) : Submodule F2 Mat3 :=
  match i.val with
  | 0 => plane484
  | 1 => plane485
  | 2 => plane486
  | 3 => plane487
  | 4 => plane488
  | 5 => plane489
  | 6 => plane490
  | _ => plane491

lemma tail_line_lb19 (P : FinitePremises) : ∀ i : Fin 3,
    QuotientRankAtLeast (tailLineSubspace i) 19 := by
  intro i
  fin_cases i
  · exact P.line_rank1_lb19
  · exact P.line_rank2_lb19
  · exact P.line_rank3_lb19

lemma tail_plane_lb19 (P : FinitePremises) : ∀ i : Fin 8,
    QuotientRankAtLeast (tailPlaneSubspace i) 19 := by
  intro i
  fin_cases i
  · exact P.plane484_lb19
  · exact P.plane485_lb19
  · exact P.plane486_lb19
  · exact P.plane487_lb19
  · exact P.plane488_lb19
  · exact P.plane489_lb19
  · exact P.plane490_lb19
  · exact P.plane491_lb19

theorem length21_quotient_occupation_cap
    {W U : Submodule F2 Mat3} (hWU : W ≤ U)
    (D : QuotientTensorDecomp W 21) {m : Nat}
    (hU : QuotientRankAtLeast U m) (hm : m ≤ 21) :
    (killSet D U).card ≤ 21 - m :=
  occupation_inequality hWU D hU hm

theorem length21_full_A_occupation_cap
    (D : TensorEntryDecomp 21) (U : Submodule F2 Mat3) {m : Nat}
    (hU : QuotientRankAtLeast U m) (hm : m ≤ 21) :
    (Finset.univ.filter fun t : Fin 21 => D.A t ∈ U).card ≤ 21 - m := by
  let D0 : QuotientTensorDecomp (⊥ : Submodule F2 Mat3) 21 :=
    entrywise_to_quotient D ⊥
  have h := occupation_inequality
    (show (⊥ : Submodule F2 Mat3) ≤ U from bot_le) D0 hU hm
  simpa [killSet, D0, entrywise_to_quotient] using h

theorem length21_named_line_cap (P : FinitePremises)
    (D : TensorEntryDecomp 21) (i : Fin 3) :
    (Finset.univ.filter fun t : Fin 21 => D.A t ∈ tailLineSubspace i).card ≤ 2 := by
  have h := length21_full_A_occupation_cap D (tailLineSubspace i)
    (tail_line_lb19 P i) (by omega)
  norm_num at h ⊢
  exact h

theorem length21_named_plane_cap (P : FinitePremises)
    (D : TensorEntryDecomp 21) (i : Fin 8) :
    (Finset.univ.filter fun t : Fin 21 => D.A t ∈ tailPlaneSubspace i).card ≤ 2 := by
  have h := length21_full_A_occupation_cap D (tailPlaneSubspace i)
    (tail_plane_lb19 P i) (by omega)
  norm_num at h ⊢
  exact h

theorem length21_affine_hyperplane_cap (P : FinitePremises)
    (D : TensorEntryDecomp 21) (i : Fin 14) :
    (Finset.univ.filter fun t : Fin 21 => D.A t ∈ affineHyperplane i).card ≤ 4 := by
  have h := length21_full_A_occupation_cap D (affineHyperplane i)
    (P.affine_hyperplane_lb17 i) (by omega)
  norm_num at h ⊢
  exact h

/-- The same generic cap transported to the B slot by the checked cyclic
decomposition symmetry. -/
theorem length21_full_B_occupation_cap
    (D : TensorEntryDecomp 21) (U : Submodule F2 Mat3) {m : Nat}
    (hU : QuotientRankAtLeast U m) (hm : m ≤ 21) :
    (Finset.univ.filter fun t : Fin 21 => D.B t ∈ U).card ≤ 21 - m :=
  B_slot_occupation_cap D U hU hm

end QiushiMatmul
end
