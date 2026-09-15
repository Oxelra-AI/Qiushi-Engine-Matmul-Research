import QiushiBranch262LabelProbe
import QiushiBranch262Dispatch
import QiushiExtractionBridge
import QiushiBranch262NoModel
import QiushiMonotonicity

set_option maxHeartbeats 80000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem contain262_of_sec
    (U : Submodule F2 Mat3) (hWU : o262W ≤ U)
    (M : Mat3) (j : Fin 31) (hlabel : label262 M = Fin.succ j)
    (hsec : codeMat (sectionCode262 (Fin.succ j)) ∈ U) : M ∈ U := by
  have hrec := reconstruction262_mem M
  rw [hlabel] at hrec; have hrecU := hWU hrec
  have : M + codeMat (sectionCode262 (Fin.succ j)) +
      codeMat (sectionCode262 (Fin.succ j)) = M := by
    rw [add_assoc, mat3_add_self_eq_zero, add_zero]
  rw [← this]; exact U.add_mem hrecU hsec

private theorem o262_zeroFiber (D : QuotientTensorDecomp o262W 16) :
    occFiberCard' (fun t : Fin 16 => label262 (D.A t)) ⟨0, by decide⟩ = 0 := by
  have hkill := zero_fiber_from_preceding_bound step113_262_base_lb16 D
  have hsub : (univ.filter (fun t : Fin 16 => label262 (D.A t) = ⟨0, by decide⟩))
      ⊆ killSet D o262W := by
    intro t ht
    simp only [mem_filter, mem_univ, true_and] at ht
    simp only [killSet, mem_filter, mem_univ, true_and]
    exact label262_eq_zero_mem (D.A t) ht
  exact Nat.eq_zero_of_le_zero (le_trans (card_le_card hsub) (Nat.le_of_eq hkill))

private theorem o262_total (D : QuotientTensorDecomp o262W 16) :
    (16 : Int) ≤ ∑ j : Fin 31, occVectorInt
      (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j := by
  have htot := occVectorInt_total_of_zero (fun t : Fin 16 => label262 (D.A t)) (o262_zeroFiber D)
  push_cast at htot; linarith

def activeSet262 : Fin 49 → Finset (Fin 31)
  | ⟨0, _⟩ => {⟨0, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩}
  | ⟨1, _⟩ => {⟨1, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩}
  | ⟨2, _⟩ => {⟨1, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩}
  | ⟨3, _⟩ => {⟨7, by decide⟩, ⟨15, by decide⟩, ⟨23, by decide⟩}
  | ⟨4, _⟩ => {⟨7, by decide⟩, ⟨16, by decide⟩, ⟨24, by decide⟩}
  | ⟨5, _⟩ => {⟨2, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩}
  | ⟨6, _⟩ => {⟨2, by decide⟩, ⟨11, by decide⟩, ⟨14, by decide⟩}
  | ⟨7, _⟩ => {⟨8, by decide⟩, ⟨18, by decide⟩, ⟨25, by decide⟩}
  | ⟨8, _⟩ => {⟨8, by decide⟩, ⟨17, by decide⟩, ⟨26, by decide⟩}
  | ⟨9, _⟩ => {⟨9, by decide⟩, ⟨21, by decide⟩, ⟨27, by decide⟩}
  | ⟨10, _⟩ => {⟨9, by decide⟩, ⟨19, by decide⟩, ⟨29, by decide⟩}
  | ⟨11, _⟩ => {⟨3, by decide⟩, ⟨17, by decide⟩, ⟨21, by decide⟩}
  | ⟨12, _⟩ => {⟨4, by decide⟩, ⟨18, by decide⟩, ⟨21, by decide⟩}
  | ⟨13, _⟩ => {⟨0, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩}
  | ⟨14, _⟩ => {⟨0, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩}
  | ⟨15, _⟩ => {⟨3, by decide⟩, ⟨10, by decide⟩, ⟨14, by decide⟩, ⟨18, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨27, by decide⟩}
  | ⟨16, _⟩ => {⟨4, by decide⟩, ⟨10, by decide⟩, ⟨13, by decide⟩, ⟨17, by decide⟩, ⟨22, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩}
  | ⟨17, _⟩ => {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩}
  | ⟨18, _⟩ => {⟨0, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩}
  | ⟨19, _⟩ => {⟨0, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩}
  | ⟨20, _⟩ => {⟨0, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩}
  | ⟨21, _⟩ => {⟨1, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩}
  | ⟨22, _⟩ => {⟨1, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩, ⟨17, by decide⟩, ⟨20, by decide⟩, ⟨22, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩}
  | ⟨23, _⟩ => {⟨1, by decide⟩}
  | ⟨24, _⟩ => {⟨2, by decide⟩, ⟨7, by decide⟩, ⟨10, by decide⟩}
  | ⟨25, _⟩ => {⟨1, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩}
  | ⟨26, _⟩ => {⟨9, by decide⟩, ⟨22, by decide⟩, ⟨28, by decide⟩}
  | ⟨27, _⟩ => {⟨0, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩}
  | ⟨28, _⟩ => {⟨0, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩}
  | ⟨29, _⟩ => {⟨3, by decide⟩, ⟨7, by decide⟩, ⟨11, by decide⟩, ⟨15, by decide⟩, ⟨19, by decide⟩, ⟨23, by decide⟩, ⟨27, by decide⟩}
  | ⟨30, _⟩ => {⟨4, by decide⟩, ⟨7, by decide⟩, ⟨12, by decide⟩, ⟨16, by decide⟩, ⟨19, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩}
  | ⟨31, _⟩ => {⟨0, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩}
  | ⟨32, _⟩ => {⟨0, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩}
  | ⟨33, _⟩ => {⟨2, by decide⟩, ⟨3, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩}
  | ⟨34, _⟩ => {⟨2, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨23, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩}
  | ⟨35, _⟩ => {⟨9, by decide⟩, ⟨20, by decide⟩, ⟨30, by decide⟩}
  | ⟨36, _⟩ => {⟨6, by decide⟩, ⟨25, by decide⟩, ⟨28, by decide⟩}
  | ⟨37, _⟩ => {⟨0, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩}
  | ⟨38, _⟩ => {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩}
  | ⟨39, _⟩ => {⟨2, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨19, by decide⟩, ⟨22, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩}
  | ⟨40, _⟩ => {⟨5, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩}
  | ⟨41, _⟩ => {⟨4, by decide⟩, ⟨26, by decide⟩, ⟨29, by decide⟩}
  | ⟨42, _⟩ => {⟨14, by decide⟩, ⟨15, by decide⟩, ⟨30, by decide⟩}
  | ⟨43, _⟩ => {⟨3, by decide⟩, ⟨26, by decide⟩, ⟨30, by decide⟩}
  | ⟨44, _⟩ => {⟨0, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩}
  | ⟨45, _⟩ => {⟨0, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩}
  | ⟨46, _⟩ => {⟨6, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨23, by decide⟩, ⟨30, by decide⟩}
  | ⟨47, _⟩ => {⟨3, by decide⟩, ⟨10, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨19, by decide⟩, ⟨26, by decide⟩, ⟨30, by decide⟩}
  | ⟨48, _⟩ => {⟨2, by decide⟩, ⟨3, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩}
  | _ => ∅

private theorem contain262_0 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨0, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource0 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource0
      step113_262_row0_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource0
      step113_262_row0_W_le_source (D.A t) ⟨9, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource0
      step113_262_row0_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_0 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨0, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨0, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row0_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨0, by decide⟩)
    (contain262_0 D)
    step113_262_row0_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_262.occRhs ⟨0, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_1 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨1, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource1 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource1
      step113_262_row1_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource1
      step113_262_row1_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource1
      step113_262_row1_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_1 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨1, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨1, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row1_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨1, by decide⟩)
    (contain262_1 D)
    step113_262_row1_qr
    (show (15 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(1 : ℕ) : Int) = S_262.occRhs ⟨1, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_2 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨2, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource2 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource2
      step113_262_row2_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource2
      step113_262_row2_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource2
      step113_262_row2_W_le_source (D.A t) ⟨6, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_2 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨2, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨2, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row2_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨2, by decide⟩)
    (contain262_2 D)
    step113_262_row2_qr
    (show (15 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(1 : ℕ) : Int) = S_262.occRhs ⟨2, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_3 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨3, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource3 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource3
      step113_262_row3_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource3
      step113_262_row3_W_le_source (D.A t) ⟨15, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource3
      step113_262_row3_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_3 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨3, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨3, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row3_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨3, by decide⟩)
    (contain262_3 D)
    step113_262_row3_qr
    (show (15 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(1 : ℕ) : Int) = S_262.occRhs ⟨3, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_4 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨4, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource4 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource4
      step113_262_row4_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource4
      step113_262_row4_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource4
      step113_262_row4_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_4 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨4, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨4, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row4_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨4, by decide⟩)
    (contain262_4 D)
    step113_262_row4_qr
    (show (15 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(1 : ℕ) : Int) = S_262.occRhs ⟨4, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_5 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨5, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource5 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource5
      step113_262_row5_W_le_source (D.A t) ⟨2, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource5
      step113_262_row5_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource5
      step113_262_row5_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_5 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨5, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨5, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row5_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨5, by decide⟩)
    (contain262_5 D)
    step113_262_row5_qr
    (show (15 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(1 : ℕ) : Int) = S_262.occRhs ⟨5, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_6 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨6, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource6 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource6
      step113_262_row6_W_le_source (D.A t) ⟨2, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource6
      step113_262_row6_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource6
      step113_262_row6_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_6 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨6, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨6, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row6_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨6, by decide⟩)
    (contain262_6 D)
    step113_262_row6_qr
    (show (15 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(1 : ℕ) : Int) = S_262.occRhs ⟨6, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_7 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨7, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource7 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource7
      step113_262_row7_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource7
      step113_262_row7_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource7
      step113_262_row7_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_7 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨7, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨7, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row7_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨7, by decide⟩)
    (contain262_7 D)
    step113_262_row7_qr
    (show (15 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(1 : ℕ) : Int) = S_262.occRhs ⟨7, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_8 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨8, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource8 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource8
      step113_262_row8_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource8
      step113_262_row8_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource8
      step113_262_row8_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_8 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨8, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨8, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row8_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨8, by decide⟩)
    (contain262_8 D)
    step113_262_row8_qr
    (show (15 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(1 : ℕ) : Int) = S_262.occRhs ⟨8, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_9 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨9, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource9 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource9
      step113_262_row9_W_le_source (D.A t) ⟨9, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource9
      step113_262_row9_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource9
      step113_262_row9_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_9 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨9, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨9, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row9_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨9, by decide⟩)
    (contain262_9 D)
    step113_262_row9_qr
    (show (15 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(1 : ℕ) : Int) = S_262.occRhs ⟨9, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_10 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨10, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource10 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource10
      step113_262_row10_W_le_source (D.A t) ⟨9, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource10
      step113_262_row10_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource10
      step113_262_row10_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_10 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨10, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨10, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row10_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨10, by decide⟩)
    (contain262_10 D)
    step113_262_row10_qr
    (show (15 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(1 : ℕ) : Int) = S_262.occRhs ⟨10, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_11 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨11, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource11 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource11
      step113_262_row11_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource11
      step113_262_row11_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource11
      step113_262_row11_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_11 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨11, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨11, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row11_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨11, by decide⟩)
    (contain262_11 D)
    step113_262_row11_qr
    (show (14 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(2 : ℕ) : Int) = S_262.occRhs ⟨11, by decide⟩ := by decide
  rw [show (16 : ℕ) - 14 = 2 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_12 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨12, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource12 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource12
      step113_262_row12_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource12
      step113_262_row12_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource12
      step113_262_row12_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_12 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨12, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨12, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row12_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨12, by decide⟩)
    (contain262_12 D)
    step113_262_row12_qr
    (show (14 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(2 : ℕ) : Int) = S_262.occRhs ⟨12, by decide⟩ := by decide
  rw [show (16 : ℕ) - 14 = 2 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_13 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨13, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource13 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource13
      step113_262_row13_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource13
      step113_262_row13_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource13
      step113_262_row13_W_le_source (D.A t) ⟨6, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource13
      step113_262_row13_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource13
      step113_262_row13_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource13
      step113_262_row13_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource13
      step113_262_row13_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_13 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨13, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨13, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row13_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨13, by decide⟩)
    (contain262_13 D)
    step113_262_row13_qr
    (show (9 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(7 : ℕ) : Int) = S_262.occRhs ⟨13, by decide⟩ := by decide
  rw [show (16 : ℕ) - 9 = 7 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_14 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨14, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource14 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource14
      step113_262_row14_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource14
      step113_262_row14_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource14
      step113_262_row14_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource14
      step113_262_row14_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource14
      step113_262_row14_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource14
      step113_262_row14_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource14
      step113_262_row14_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_14 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨14, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨14, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row14_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨14, by decide⟩)
    (contain262_14 D)
    step113_262_row14_qr
    (show (9 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(7 : ℕ) : Int) = S_262.occRhs ⟨14, by decide⟩ := by decide
  rw [show (16 : ℕ) - 9 = 7 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_15 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨15, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource15 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource15
      step113_262_row15_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource15
      step113_262_row15_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource15
      step113_262_row15_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource15
      step113_262_row15_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource15
      step113_262_row15_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource15
      step113_262_row15_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource15
      step113_262_row15_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_15 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨15, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨15, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row15_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨15, by decide⟩)
    (contain262_15 D)
    step113_262_row15_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_262.occRhs ⟨15, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_16 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨16, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource16 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource16
      step113_262_row16_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource16
      step113_262_row16_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource16
      step113_262_row16_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource16
      step113_262_row16_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource16
      step113_262_row16_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource16
      step113_262_row16_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource16
      step113_262_row16_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_16 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨16, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨16, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row16_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨16, by decide⟩)
    (contain262_16 D)
    step113_262_row16_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_262.occRhs ⟨16, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_17 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨17, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource17 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource17
      step113_262_row17_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource17
      step113_262_row17_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource17
      step113_262_row17_W_le_source (D.A t) ⟨2, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource17
      step113_262_row17_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource17
      step113_262_row17_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource17
      step113_262_row17_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource17
      step113_262_row17_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource17
      step113_262_row17_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource17
      step113_262_row17_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource17
      step113_262_row17_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource17
      step113_262_row17_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource17
      step113_262_row17_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource17
      step113_262_row17_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource17
      step113_262_row17_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource17
      step113_262_row17_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_17 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨17, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨17, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row17_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨17, by decide⟩)
    (contain262_17 D)
    step113_262_row17_qr
    (show (6 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(10 : ℕ) : Int) = S_262.occRhs ⟨17, by decide⟩ := by decide
  rw [show (16 : ℕ) - 6 = 10 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_18 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨18, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource18 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource18
      step113_262_row18_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource18
      step113_262_row18_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource18
      step113_262_row18_W_le_source (D.A t) ⟨6, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource18
      step113_262_row18_W_le_source (D.A t) ⟨9, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource18
      step113_262_row18_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource18
      step113_262_row18_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource18
      step113_262_row18_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource18
      step113_262_row18_W_le_source (D.A t) ⟨15, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource18
      step113_262_row18_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource18
      step113_262_row18_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource18
      step113_262_row18_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource18
      step113_262_row18_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource18
      step113_262_row18_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource18
      step113_262_row18_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource18
      step113_262_row18_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_18 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨18, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨18, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row18_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨18, by decide⟩)
    (contain262_18 D)
    step113_262_row18_qr
    (show (6 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(10 : ℕ) : Int) = S_262.occRhs ⟨18, by decide⟩ := by decide
  rw [show (16 : ℕ) - 6 = 10 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_19 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨19, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource19 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource19
      step113_262_row19_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource19
      step113_262_row19_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource19
      step113_262_row19_W_le_source (D.A t) ⟨6, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource19
      step113_262_row19_W_le_source (D.A t) ⟨9, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource19
      step113_262_row19_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource19
      step113_262_row19_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource19
      step113_262_row19_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource19
      step113_262_row19_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource19
      step113_262_row19_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource19
      step113_262_row19_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource19
      step113_262_row19_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource19
      step113_262_row19_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource19
      step113_262_row19_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource19
      step113_262_row19_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource19
      step113_262_row19_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_19 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨19, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨19, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row19_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨19, by decide⟩)
    (contain262_19 D)
    step113_262_row19_qr
    (show (6 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(10 : ℕ) : Int) = S_262.occRhs ⟨19, by decide⟩ := by decide
  rw [show (16 : ℕ) - 6 = 10 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_20 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨20, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource20 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource20
      step113_262_row20_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource20
      step113_262_row20_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource20
      step113_262_row20_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource20
      step113_262_row20_W_le_source (D.A t) ⟨9, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource20
      step113_262_row20_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource20
      step113_262_row20_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource20
      step113_262_row20_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource20
      step113_262_row20_W_le_source (D.A t) ⟨15, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource20
      step113_262_row20_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource20
      step113_262_row20_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource20
      step113_262_row20_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource20
      step113_262_row20_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource20
      step113_262_row20_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource20
      step113_262_row20_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource20
      step113_262_row20_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_20 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨20, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨20, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row20_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨20, by decide⟩)
    (contain262_20 D)
    step113_262_row20_qr
    (show (6 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(10 : ℕ) : Int) = S_262.occRhs ⟨20, by decide⟩ := by decide
  rw [show (16 : ℕ) - 6 = 10 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_21 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨21, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource21 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource21
      step113_262_row21_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource21
      step113_262_row21_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource21
      step113_262_row21_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource21
      step113_262_row21_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource21
      step113_262_row21_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource21
      step113_262_row21_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource21
      step113_262_row21_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource21
      step113_262_row21_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource21
      step113_262_row21_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource21
      step113_262_row21_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource21
      step113_262_row21_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource21
      step113_262_row21_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource21
      step113_262_row21_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource21
      step113_262_row21_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource21
      step113_262_row21_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_21 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨21, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨21, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row21_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨21, by decide⟩)
    (contain262_21 D)
    step113_262_row21_qr
    (show (9 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(7 : ℕ) : Int) = S_262.occRhs ⟨21, by decide⟩ := by decide
  rw [show (16 : ℕ) - 9 = 7 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_22 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨22, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource22 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource22
      step113_262_row22_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource22
      step113_262_row22_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource22
      step113_262_row22_W_le_source (D.A t) ⟨6, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource22
      step113_262_row22_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource22
      step113_262_row22_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource22
      step113_262_row22_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource22
      step113_262_row22_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource22
      step113_262_row22_W_le_source (D.A t) ⟨15, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource22
      step113_262_row22_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource22
      step113_262_row22_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource22
      step113_262_row22_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource22
      step113_262_row22_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource22
      step113_262_row22_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource22
      step113_262_row22_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource22
      step113_262_row22_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_22 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨22, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨22, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row22_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨22, by decide⟩)
    (contain262_22 D)
    step113_262_row22_qr
    (show (9 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(7 : ℕ) : Int) = S_262.occRhs ⟨22, by decide⟩ := by decide
  rw [show (16 : ℕ) - 9 = 7 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_23 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨23, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource23 := by
  simp only [mem_image, activeSet262, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  subst hj
  apply contain262_of_sec step113_262ActualSource23
    step113_262_row23_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
  exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_23 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨23, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨23, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row23_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨23, by decide⟩)
    (contain262_23 D)
    step113_262_row23_qr
    (show (16 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(0 : ℕ) : Int) = S_262.occRhs ⟨23, by decide⟩ := by decide
  rw [show (16 : ℕ) - 16 = 0 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_24 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨24, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource24 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource24
      step113_262_row24_W_le_source (D.A t) ⟨2, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource24
      step113_262_row24_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource24
      step113_262_row24_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_24 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨24, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨24, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row24_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨24, by decide⟩)
    (contain262_24 D)
    step113_262_row24_qr
    (show (15 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(1 : ℕ) : Int) = S_262.occRhs ⟨24, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_25 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨25, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource25 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource25
      step113_262_row25_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource25
      step113_262_row25_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource25
      step113_262_row25_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_25 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨25, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨25, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row25_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨25, by decide⟩)
    (contain262_25 D)
    step113_262_row25_qr
    (show (15 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(1 : ℕ) : Int) = S_262.occRhs ⟨25, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_26 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨26, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource26 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource26
      step113_262_row26_W_le_source (D.A t) ⟨9, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource26
      step113_262_row26_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource26
      step113_262_row26_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_26 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨26, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨26, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row26_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨26, by decide⟩)
    (contain262_26 D)
    step113_262_row26_qr
    (show (15 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(1 : ℕ) : Int) = S_262.occRhs ⟨26, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_27 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨27, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource27 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource27
      step113_262_row27_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource27
      step113_262_row27_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource27
      step113_262_row27_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource27
      step113_262_row27_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource27
      step113_262_row27_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource27
      step113_262_row27_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource27
      step113_262_row27_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_27 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨27, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨27, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row27_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨27, by decide⟩)
    (contain262_27 D)
    step113_262_row27_qr
    (show (9 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(7 : ℕ) : Int) = S_262.occRhs ⟨27, by decide⟩ := by decide
  rw [show (16 : ℕ) - 9 = 7 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_28 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨28, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource28 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource28
      step113_262_row28_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource28
      step113_262_row28_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource28
      step113_262_row28_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource28
      step113_262_row28_W_le_source (D.A t) ⟨15, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource28
      step113_262_row28_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource28
      step113_262_row28_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource28
      step113_262_row28_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_28 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨28, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨28, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row28_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨28, by decide⟩)
    (contain262_28 D)
    step113_262_row28_qr
    (show (9 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(7 : ℕ) : Int) = S_262.occRhs ⟨28, by decide⟩ := by decide
  rw [show (16 : ℕ) - 9 = 7 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_29 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨29, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource29 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource29
      step113_262_row29_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource29
      step113_262_row29_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource29
      step113_262_row29_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource29
      step113_262_row29_W_le_source (D.A t) ⟨15, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource29
      step113_262_row29_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource29
      step113_262_row29_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource29
      step113_262_row29_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_29 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨29, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨29, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row29_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨29, by decide⟩)
    (contain262_29 D)
    step113_262_row29_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_262.occRhs ⟨29, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_30 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨30, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource30 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource30
      step113_262_row30_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource30
      step113_262_row30_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource30
      step113_262_row30_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource30
      step113_262_row30_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource30
      step113_262_row30_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource30
      step113_262_row30_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource30
      step113_262_row30_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_30 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨30, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨30, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row30_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨30, by decide⟩)
    (contain262_30 D)
    step113_262_row30_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_262.occRhs ⟨30, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_31 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨31, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource31 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource31
      step113_262_row31_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource31
      step113_262_row31_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource31
      step113_262_row31_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource31
      step113_262_row31_W_le_source (D.A t) ⟨9, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource31
      step113_262_row31_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource31
      step113_262_row31_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource31
      step113_262_row31_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource31
      step113_262_row31_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource31
      step113_262_row31_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource31
      step113_262_row31_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource31
      step113_262_row31_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource31
      step113_262_row31_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource31
      step113_262_row31_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource31
      step113_262_row31_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource31
      step113_262_row31_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_31 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨31, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨31, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row31_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨31, by decide⟩)
    (contain262_31 D)
    step113_262_row31_qr
    (show (6 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(10 : ℕ) : Int) = S_262.occRhs ⟨31, by decide⟩ := by decide
  rw [show (16 : ℕ) - 6 = 10 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_32 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨32, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource32 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource32
      step113_262_row32_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource32
      step113_262_row32_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource32
      step113_262_row32_W_le_source (D.A t) ⟨6, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource32
      step113_262_row32_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource32
      step113_262_row32_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource32
      step113_262_row32_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource32
      step113_262_row32_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource32
      step113_262_row32_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource32
      step113_262_row32_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource32
      step113_262_row32_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource32
      step113_262_row32_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource32
      step113_262_row32_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource32
      step113_262_row32_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource32
      step113_262_row32_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource32
      step113_262_row32_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_32 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨32, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨32, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row32_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨32, by decide⟩)
    (contain262_32 D)
    step113_262_row32_qr
    (show (6 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(10 : ℕ) : Int) = S_262.occRhs ⟨32, by decide⟩ := by decide
  rw [show (16 : ℕ) - 6 = 10 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_33 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨33, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource33 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource33
      step113_262_row33_W_le_source (D.A t) ⟨2, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource33
      step113_262_row33_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource33
      step113_262_row33_W_le_source (D.A t) ⟨6, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource33
      step113_262_row33_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource33
      step113_262_row33_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource33
      step113_262_row33_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource33
      step113_262_row33_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource33
      step113_262_row33_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource33
      step113_262_row33_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource33
      step113_262_row33_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource33
      step113_262_row33_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource33
      step113_262_row33_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource33
      step113_262_row33_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource33
      step113_262_row33_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource33
      step113_262_row33_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_33 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨33, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨33, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row33_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨33, by decide⟩)
    (contain262_33 D)
    step113_262_row33_qr
    (show (9 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(7 : ℕ) : Int) = S_262.occRhs ⟨33, by decide⟩ := by decide
  rw [show (16 : ℕ) - 9 = 7 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_34 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨34, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource34 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource34
      step113_262_row34_W_le_source (D.A t) ⟨2, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource34
      step113_262_row34_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource34
      step113_262_row34_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource34
      step113_262_row34_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource34
      step113_262_row34_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource34
      step113_262_row34_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource34
      step113_262_row34_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource34
      step113_262_row34_W_le_source (D.A t) ⟨15, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource34
      step113_262_row34_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource34
      step113_262_row34_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource34
      step113_262_row34_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource34
      step113_262_row34_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource34
      step113_262_row34_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource34
      step113_262_row34_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource34
      step113_262_row34_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_34 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨34, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨34, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row34_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨34, by decide⟩)
    (contain262_34 D)
    step113_262_row34_qr
    (show (9 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(7 : ℕ) : Int) = S_262.occRhs ⟨34, by decide⟩ := by decide
  rw [show (16 : ℕ) - 9 = 7 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_35 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨35, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource35 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource35
      step113_262_row35_W_le_source (D.A t) ⟨9, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource35
      step113_262_row35_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource35
      step113_262_row35_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_35 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨35, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨35, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row35_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨35, by decide⟩)
    (contain262_35 D)
    step113_262_row35_qr
    (show (15 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(1 : ℕ) : Int) = S_262.occRhs ⟨35, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_36 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨36, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource36 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource36
      step113_262_row36_W_le_source (D.A t) ⟨6, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource36
      step113_262_row36_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource36
      step113_262_row36_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_36 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨36, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨36, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row36_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨36, by decide⟩)
    (contain262_36 D)
    step113_262_row36_qr
    (show (14 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(2 : ℕ) : Int) = S_262.occRhs ⟨36, by decide⟩ := by decide
  rw [show (16 : ℕ) - 14 = 2 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_37 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨37, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource37 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource37
      step113_262_row37_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource37
      step113_262_row37_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource37
      step113_262_row37_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource37
      step113_262_row37_W_le_source (D.A t) ⟨15, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource37
      step113_262_row37_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource37
      step113_262_row37_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource37
      step113_262_row37_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_37 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨37, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨37, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row37_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨37, by decide⟩)
    (contain262_37 D)
    step113_262_row37_qr
    (show (9 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(7 : ℕ) : Int) = S_262.occRhs ⟨37, by decide⟩ := by decide
  rw [show (16 : ℕ) - 9 = 7 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_38 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨38, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource38 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource38
      step113_262_row38_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource38
      step113_262_row38_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource38
      step113_262_row38_W_le_source (D.A t) ⟨2, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource38
      step113_262_row38_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource38
      step113_262_row38_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource38
      step113_262_row38_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource38
      step113_262_row38_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource38
      step113_262_row38_W_le_source (D.A t) ⟨15, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource38
      step113_262_row38_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource38
      step113_262_row38_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource38
      step113_262_row38_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource38
      step113_262_row38_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource38
      step113_262_row38_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource38
      step113_262_row38_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource38
      step113_262_row38_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_38 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨38, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨38, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row38_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨38, by decide⟩)
    (contain262_38 D)
    step113_262_row38_qr
    (show (6 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(10 : ℕ) : Int) = S_262.occRhs ⟨38, by decide⟩ := by decide
  rw [show (16 : ℕ) - 6 = 10 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_39 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨39, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource39 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource39
      step113_262_row39_W_le_source (D.A t) ⟨2, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource39
      step113_262_row39_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource39
      step113_262_row39_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource39
      step113_262_row39_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource39
      step113_262_row39_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource39
      step113_262_row39_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource39
      step113_262_row39_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource39
      step113_262_row39_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource39
      step113_262_row39_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource39
      step113_262_row39_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource39
      step113_262_row39_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource39
      step113_262_row39_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource39
      step113_262_row39_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource39
      step113_262_row39_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource39
      step113_262_row39_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_39 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨39, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨39, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row39_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨39, by decide⟩)
    (contain262_39 D)
    step113_262_row39_qr
    (show (9 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(7 : ℕ) : Int) = S_262.occRhs ⟨39, by decide⟩ := by decide
  rw [show (16 : ℕ) - 9 = 7 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_40 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨40, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource40 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource40
      step113_262_row40_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource40
      step113_262_row40_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource40
      step113_262_row40_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_40 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨40, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨40, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row40_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨40, by decide⟩)
    (contain262_40 D)
    step113_262_row40_qr
    (show (14 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(2 : ℕ) : Int) = S_262.occRhs ⟨40, by decide⟩ := by decide
  rw [show (16 : ℕ) - 14 = 2 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_41 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨41, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource41 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource41
      step113_262_row41_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource41
      step113_262_row41_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource41
      step113_262_row41_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_41 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨41, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨41, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row41_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨41, by decide⟩)
    (contain262_41 D)
    step113_262_row41_qr
    (show (14 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(2 : ℕ) : Int) = S_262.occRhs ⟨41, by decide⟩ := by decide
  rw [show (16 : ℕ) - 14 = 2 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_42 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨42, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource42 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource42
      step113_262_row42_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource42
      step113_262_row42_W_le_source (D.A t) ⟨15, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource42
      step113_262_row42_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_42 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨42, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨42, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row42_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨42, by decide⟩)
    (contain262_42 D)
    step113_262_row42_qr
    (show (14 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(2 : ℕ) : Int) = S_262.occRhs ⟨42, by decide⟩ := by decide
  rw [show (16 : ℕ) - 14 = 2 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_43 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨43, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource43 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource43
      step113_262_row43_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource43
      step113_262_row43_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource43
      step113_262_row43_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_43 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨43, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨43, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row43_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨43, by decide⟩)
    (contain262_43 D)
    step113_262_row43_qr
    (show (14 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(2 : ℕ) : Int) = S_262.occRhs ⟨43, by decide⟩ := by decide
  rw [show (16 : ℕ) - 14 = 2 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_44 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨44, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource44 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource44
      step113_262_row44_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource44
      step113_262_row44_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource44
      step113_262_row44_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource44
      step113_262_row44_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource44
      step113_262_row44_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource44
      step113_262_row44_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource44
      step113_262_row44_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_44 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨44, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨44, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row44_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨44, by decide⟩)
    (contain262_44 D)
    step113_262_row44_qr
    (show (9 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(7 : ℕ) : Int) = S_262.occRhs ⟨44, by decide⟩ := by decide
  rw [show (16 : ℕ) - 9 = 7 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_45 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨45, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource45 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource45
      step113_262_row45_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource45
      step113_262_row45_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource45
      step113_262_row45_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource45
      step113_262_row45_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource45
      step113_262_row45_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource45
      step113_262_row45_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource45
      step113_262_row45_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_45 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨45, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨45, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row45_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨45, by decide⟩)
    (contain262_45 D)
    step113_262_row45_qr
    (show (9 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(7 : ℕ) : Int) = S_262.occRhs ⟨45, by decide⟩ := by decide
  rw [show (16 : ℕ) - 9 = 7 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_46 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨46, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource46 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource46
      step113_262_row46_W_le_source (D.A t) ⟨6, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource46
      step113_262_row46_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource46
      step113_262_row46_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource46
      step113_262_row46_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource46
      step113_262_row46_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource46
      step113_262_row46_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource46
      step113_262_row46_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_46 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨46, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨46, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row46_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨46, by decide⟩)
    (contain262_46 D)
    step113_262_row46_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_262.occRhs ⟨46, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_47 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨47, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource47 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource47
      step113_262_row47_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource47
      step113_262_row47_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource47
      step113_262_row47_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource47
      step113_262_row47_W_le_source (D.A t) ⟨15, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource47
      step113_262_row47_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource47
      step113_262_row47_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource47
      step113_262_row47_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_47 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨47, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨47, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row47_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨47, by decide⟩)
    (contain262_47 D)
    step113_262_row47_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_262.occRhs ⟨47, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain262_48 (D : QuotientTensorDecomp o262W 16)
    (t : Fin 16)
    (ht : label262 (D.A t) ∈ (activeSet262 ⟨48, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_262ActualSource48 := by
  simp only [mem_image, activeSet262, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain262_of_sec step113_262ActualSource48
      step113_262_row48_W_le_source (D.A t) ⟨2, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource48
      step113_262_row48_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource48
      step113_262_row48_W_le_source (D.A t) ⟨6, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource48
      step113_262_row48_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource48
      step113_262_row48_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource48
      step113_262_row48_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource48
      step113_262_row48_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource48
      step113_262_row48_W_le_source (D.A t) ⟨15, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource48
      step113_262_row48_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource48
      step113_262_row48_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource48
      step113_262_row48_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource48
      step113_262_row48_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource48
      step113_262_row48_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource48
      step113_262_row48_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain262_of_sec step113_262ActualSource48
      step113_262_row48_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound262_48 (D : QuotientTensorDecomp o262W 16) :
    ∑ j ∈ activeSet262 ⟨48, by decide⟩,
      occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_262.occRhs ⟨48, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step113_262_row48_W_le_source D
    (fun t : Fin 16 => label262 (D.A t))
    (activeSet262 ⟨48, by decide⟩)
    (contain262_48 D)
    step113_262_row48_qr
    (show (9 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(7 : ℕ) : Int) = S_262.occRhs ⟨48, by decide⟩ := by decide
  rw [show (16 : ℕ) - 9 = 7 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem coeffMatch262 (i : Fin 49) (j : Fin 31) :
    S_262.occCoeff i j = if j ∈ activeSet262 i then 1 else 0 := by
  fin_cases i <;> (fin_cases j <;> decide)

private theorem o262_extractRootHolds (D : QuotientTensorDecomp o262W 16) :
    S_262.RootHolds (occVectorInt (fun t : Fin 16 => label262 (D.A t)) 31 (Nat.le_refl _)) :=
  rootHolds_from_label_bounds S_262 _
    (fun j => occVectorInt_nonneg _ (Nat.le_refl _) j)
    (o262_total D)
    activeSet262
    (fun i => by
      fin_cases i
      · exact rowBound262_0 D
      · exact rowBound262_1 D
      · exact rowBound262_2 D
      · exact rowBound262_3 D
      · exact rowBound262_4 D
      · exact rowBound262_5 D
      · exact rowBound262_6 D
      · exact rowBound262_7 D
      · exact rowBound262_8 D
      · exact rowBound262_9 D
      · exact rowBound262_10 D
      · exact rowBound262_11 D
      · exact rowBound262_12 D
      · exact rowBound262_13 D
      · exact rowBound262_14 D
      · exact rowBound262_15 D
      · exact rowBound262_16 D
      · exact rowBound262_17 D
      · exact rowBound262_18 D
      · exact rowBound262_19 D
      · exact rowBound262_20 D
      · exact rowBound262_21 D
      · exact rowBound262_22 D
      · exact rowBound262_23 D
      · exact rowBound262_24 D
      · exact rowBound262_25 D
      · exact rowBound262_26 D
      · exact rowBound262_27 D
      · exact rowBound262_28 D
      · exact rowBound262_29 D
      · exact rowBound262_30 D
      · exact rowBound262_31 D
      · exact rowBound262_32 D
      · exact rowBound262_33 D
      · exact rowBound262_34 D
      · exact rowBound262_35 D
      · exact rowBound262_36 D
      · exact rowBound262_37 D
      · exact rowBound262_38 D
      · exact rowBound262_39 D
      · exact rowBound262_40 D
      · exact rowBound262_41 D
      · exact rowBound262_42 D
      · exact rowBound262_43 D
      · exact rowBound262_44 D
      · exact rowBound262_45 D
      · exact rowBound262_46 D
      · exact rowBound262_47 D
      · exact rowBound262_48 D
    )
    (fun i j => coeffMatch262 i j)

/-- Unconditional orbit-262 quotient rank lower bound. -/
theorem step113_orbit262_lb17 : QuotientRankAtLeast o262W 17 := by
  apply branchBridge_quotientRankAtLeast o262W 16 S_262 orbit262_occupation_no_model
  intro r hr D
  by_cases hr16 : r < 16
  · exact False.elim ((step113_262_base_lb16 r hr16).false D)
  · have hrr : r = 16 := by omega
    subst hrr
    exact ⟨_, o262_extractRootHolds D⟩

end QiushiMatmul
