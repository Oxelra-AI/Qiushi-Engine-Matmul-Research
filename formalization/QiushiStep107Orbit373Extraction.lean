import QiushiStep107O373LabelProbe
import QiushiStep107Orbit373Dispatches
import QiushiExtractionBridge
import QiushiOrbit373BranchNoModel
import QiushiMonotonicity

set_option maxHeartbeats 80000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem contain373_of_sec
    (U : Submodule F2 Mat3) (hWU : o373W ≤ U)
    (M : Mat3) (j : Fin 31) (hlabel : label373 M = Fin.succ j)
    (hsec : codeMat (sectionCode373 (Fin.succ j)) ∈ U) : M ∈ U := by
  have hrec := reconstruction373_mem M
  rw [hlabel] at hrec
  have hrecU := hWU hrec
  have : M + codeMat (sectionCode373 (Fin.succ j)) +
      codeMat (sectionCode373 (Fin.succ j)) = M := by
    rw [add_assoc, mat3_add_self_eq_zero, add_zero]
  rw [← this]; exact U.add_mem hrecU hsec

private theorem o373_zeroFiber (D : QuotientTensorDecomp o373W 16) :
    occFiberCard' (fun t : Fin 16 => label373 (D.A t)) ⟨0, by decide⟩ = 0 := by
  have hkill := zero_fiber_from_preceding_bound step107_o373_base_lb16 D
  have hsub : (univ.filter (fun t : Fin 16 => label373 (D.A t) = ⟨0, by decide⟩))
      ⊆ killSet D o373W := by
    intro t ht
    simp only [mem_filter, mem_univ, true_and] at ht
    simp only [killSet, mem_filter, mem_univ, true_and]
    exact label373_eq_zero_mem (D.A t) ht
  exact Nat.eq_zero_of_le_zero (le_trans (card_le_card hsub) (Nat.le_of_eq hkill))

private theorem o373_total (D : QuotientTensorDecomp o373W 16) :
    (16 : Int) ≤ ∑ j : Fin 31, occVectorInt
      (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j := by
  have htot := occVectorInt_total_of_zero (fun t : Fin 16 => label373 (D.A t)) (o373_zeroFiber D)
  push_cast at htot; linarith

def activeSet373 : Fin 57 → Finset (Fin 31)
  | ⟨0, _⟩ => {⟨6, by decide⟩}
  | ⟨1, _⟩ => {⟨17, by decide⟩}
  | ⟨2, _⟩ => {⟨20, by decide⟩}
  | ⟨3, _⟩ => {⟨2, by decide⟩}
  | ⟨4, _⟩ => {⟨15, by decide⟩}
  | ⟨5, _⟩ => {⟨7, by decide⟩, ⟨16, by decide⟩, ⟨24, by decide⟩}
  | ⟨6, _⟩ => {⟨10, by decide⟩, ⟨22, by decide⟩, ⟨27, by decide⟩}
  | ⟨7, _⟩ => {⟨1, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩}
  | ⟨8, _⟩ => {⟨4, by decide⟩, ⟨9, by decide⟩, ⟨14, by decide⟩, ⟨17, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨28, by decide⟩}
  | ⟨9, _⟩ => {⟨3, by decide⟩, ⟨25, by decide⟩, ⟨29, by decide⟩}
  | ⟨10, _⟩ => {⟨1, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩}
  | ⟨11, _⟩ => {⟨2, by decide⟩, ⟨11, by decide⟩, ⟨14, by decide⟩, ⟨19, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨26, by decide⟩}
  | ⟨12, _⟩ => {⟨3, by decide⟩, ⟨8, by decide⟩, ⟨12, by decide⟩, ⟨16, by decide⟩, ⟨20, by decide⟩, ⟨23, by decide⟩, ⟨27, by decide⟩}
  | ⟨13, _⟩ => {⟨4, by decide⟩, ⟨7, by decide⟩, ⟨12, by decide⟩, ⟨16, by decide⟩, ⟨19, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩}
  | ⟨14, _⟩ => {⟨3, by decide⟩, ⟨9, by decide⟩, ⟨13, by decide⟩, ⟨18, by decide⟩, ⟨22, by decide⟩, ⟨24, by decide⟩, ⟨28, by decide⟩}
  | ⟨15, _⟩ => {⟨3, by decide⟩, ⟨7, by decide⟩, ⟨11, by decide⟩, ⟨17, by decide⟩, ⟨21, by decide⟩, ⟨25, by decide⟩, ⟨29, by decide⟩}
  | ⟨16, _⟩ => {⟨5, by decide⟩, ⟨7, by decide⟩, ⟨13, by decide⟩, ⟨16, by decide⟩, ⟨22, by decide⟩, ⟨24, by decide⟩, ⟨30, by decide⟩}
  | ⟨17, _⟩ => {⟨3, by decide⟩, ⟨8, by decide⟩, ⟨12, by decide⟩, ⟨17, by decide⟩, ⟨21, by decide⟩, ⟨26, by decide⟩, ⟨30, by decide⟩}
  | ⟨18, _⟩ => {⟨3, by decide⟩, ⟨7, by decide⟩, ⟨11, by decide⟩, ⟨18, by decide⟩, ⟨22, by decide⟩, ⟨26, by decide⟩, ⟨30, by decide⟩}
  | ⟨19, _⟩ => {⟨0, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩}
  | ⟨20, _⟩ => {⟨1, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩}
  | ⟨21, _⟩ => {⟨1, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨21, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩}
  | ⟨22, _⟩ => {⟨2, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨19, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩}
  | ⟨23, _⟩ => {⟨1, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨13, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨21, by decide⟩, ⟨23, by decide⟩, ⟨25, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩}
  | ⟨24, _⟩ => {⟨28, by decide⟩}
  | ⟨25, _⟩ => {⟨5, by decide⟩}
  | ⟨26, _⟩ => {⟨5, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩}
  | ⟨27, _⟩ => {⟨8, by decide⟩, ⟨16, by decide⟩, ⟨23, by decide⟩}
  | ⟨28, _⟩ => {⟨7, by decide⟩, ⟨22, by decide⟩, ⟨30, by decide⟩}
  | ⟨29, _⟩ => {⟨0, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩}
  | ⟨30, _⟩ => {⟨5, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩}
  | ⟨31, _⟩ => {⟨2, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨15, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩}
  | ⟨32, _⟩ => {⟨0, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩}
  | ⟨33, _⟩ => {⟨0, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩}
  | ⟨34, _⟩ => {⟨2, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨19, by decide⟩, ⟨22, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩}
  | ⟨35, _⟩ => {⟨1, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨19, by decide⟩, ⟨21, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩}
  | ⟨36, _⟩ => {⟨0, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩}
  | ⟨37, _⟩ => {⟨0, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩}
  | ⟨38, _⟩ => {⟨5, by decide⟩, ⟨16, by decide⟩, ⟨22, by decide⟩}
  | ⟨39, _⟩ => {⟨0, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩}
  | ⟨40, _⟩ => {⟨2, by decide⟩, ⟨11, by decide⟩, ⟨14, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩}
  | ⟨41, _⟩ => {⟨1, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩, ⟨19, by decide⟩, ⟨21, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩}
  | ⟨42, _⟩ => {⟨0, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩}
  | ⟨43, _⟩ => {⟨0, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩}
  | ⟨44, _⟩ => {⟨5, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨17, by decide⟩, ⟨19, by decide⟩, ⟨23, by decide⟩, ⟨29, by decide⟩}
  | ⟨45, _⟩ => {⟨1, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩}
  | ⟨46, _⟩ => {⟨5, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨24, by decide⟩, ⟨30, by decide⟩}
  | ⟨47, _⟩ => {⟨1, by decide⟩, ⟨11, by decide⟩, ⟨13, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩}
  | ⟨48, _⟩ => {⟨0, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩}
  | ⟨49, _⟩ => {⟨5, by decide⟩, ⟨7, by decide⟩, ⟨13, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩}
  | ⟨50, _⟩ => {⟨2, by decide⟩, ⟨7, by decide⟩, ⟨10, by decide⟩, ⟨19, by decide⟩, ⟨22, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩}
  | ⟨51, _⟩ => {⟨0, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩}
  | ⟨52, _⟩ => {⟨1, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩}
  | ⟨53, _⟩ => {⟨1, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨22, by decide⟩}
  | ⟨54, _⟩ => {⟨1, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩}
  | ⟨55, _⟩ => {⟨0, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩}
  | ⟨56, _⟩ => {⟨1, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨20, by decide⟩, ⟨22, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩}
  | _ => ∅

private theorem contain373_0 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨0, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource0 := by
  simp only [mem_image, activeSet373, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  subst hj
  apply contain373_of_sec step107o373ActualSource0
    step107_o373_row0_W_le_source (D.A t) ⟨6, by decide⟩ hjl.symm
  exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_0 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨0, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨0, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row0_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨0, by decide⟩)
    (contain373_0 D)
    step107_o373_row0_qr
    (show (16 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(0 : ℕ) : Int) = S_373.occRhs ⟨0, by decide⟩ := by decide
  rw [show (16 : ℕ) - 16 = 0 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_1 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨1, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource1 := by
  simp only [mem_image, activeSet373, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  subst hj
  apply contain373_of_sec step107o373ActualSource1
    step107_o373_row1_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
  exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_1 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨1, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨1, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row1_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨1, by decide⟩)
    (contain373_1 D)
    step107_o373_row1_qr
    (show (16 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(0 : ℕ) : Int) = S_373.occRhs ⟨1, by decide⟩ := by decide
  rw [show (16 : ℕ) - 16 = 0 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_2 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨2, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource2 := by
  simp only [mem_image, activeSet373, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  subst hj
  apply contain373_of_sec step107o373ActualSource2
    step107_o373_row2_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
  exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_2 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨2, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨2, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row2_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨2, by decide⟩)
    (contain373_2 D)
    step107_o373_row2_qr
    (show (16 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(0 : ℕ) : Int) = S_373.occRhs ⟨2, by decide⟩ := by decide
  rw [show (16 : ℕ) - 16 = 0 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_3 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨3, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource3 := by
  simp only [mem_image, activeSet373, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  subst hj
  apply contain373_of_sec step107o373ActualSource3
    step107_o373_row3_W_le_source (D.A t) ⟨2, by decide⟩ hjl.symm
  exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_3 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨3, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨3, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row3_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨3, by decide⟩)
    (contain373_3 D)
    step107_o373_row3_qr
    (show (15 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(1 : ℕ) : Int) = S_373.occRhs ⟨3, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_4 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨4, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource4 := by
  simp only [mem_image, activeSet373, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  subst hj
  apply contain373_of_sec step107o373ActualSource4
    step107_o373_row4_W_le_source (D.A t) ⟨15, by decide⟩ hjl.symm
  exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_4 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨4, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨4, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row4_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨4, by decide⟩)
    (contain373_4 D)
    step107_o373_row4_qr
    (show (15 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(1 : ℕ) : Int) = S_373.occRhs ⟨4, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_5 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨5, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource5 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource5
      step107_o373_row5_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource5
      step107_o373_row5_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource5
      step107_o373_row5_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_5 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨5, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨5, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row5_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨5, by decide⟩)
    (contain373_5 D)
    step107_o373_row5_qr
    (show (15 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(1 : ℕ) : Int) = S_373.occRhs ⟨5, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_6 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨6, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource6 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource6
      step107_o373_row6_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource6
      step107_o373_row6_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource6
      step107_o373_row6_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_6 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨6, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨6, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row6_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨6, by decide⟩)
    (contain373_6 D)
    step107_o373_row6_qr
    (show (15 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(1 : ℕ) : Int) = S_373.occRhs ⟨6, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_7 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨7, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource7 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource7
      step107_o373_row7_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource7
      step107_o373_row7_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource7
      step107_o373_row7_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_7 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨7, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨7, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row7_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨7, by decide⟩)
    (contain373_7 D)
    step107_o373_row7_qr
    (show (14 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(2 : ℕ) : Int) = S_373.occRhs ⟨7, by decide⟩ := by decide
  rw [show (16 : ℕ) - 14 = 2 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_8 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨8, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource8 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource8
      step107_o373_row8_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource8
      step107_o373_row8_W_le_source (D.A t) ⟨9, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource8
      step107_o373_row8_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource8
      step107_o373_row8_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource8
      step107_o373_row8_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource8
      step107_o373_row8_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource8
      step107_o373_row8_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_8 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨8, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨8, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row8_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨8, by decide⟩)
    (contain373_8 D)
    step107_o373_row8_qr
    (show (14 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(2 : ℕ) : Int) = S_373.occRhs ⟨8, by decide⟩ := by decide
  rw [show (16 : ℕ) - 14 = 2 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_9 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨9, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource9 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource9
      step107_o373_row9_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource9
      step107_o373_row9_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource9
      step107_o373_row9_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_9 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨9, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨9, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row9_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨9, by decide⟩)
    (contain373_9 D)
    step107_o373_row9_qr
    (show (14 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(2 : ℕ) : Int) = S_373.occRhs ⟨9, by decide⟩ := by decide
  rw [show (16 : ℕ) - 14 = 2 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_10 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨10, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource10 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource10
      step107_o373_row10_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource10
      step107_o373_row10_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource10
      step107_o373_row10_W_le_source (D.A t) ⟨6, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource10
      step107_o373_row10_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource10
      step107_o373_row10_W_le_source (D.A t) ⟨9, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource10
      step107_o373_row10_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource10
      step107_o373_row10_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_10 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨10, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨10, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row10_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨10, by decide⟩)
    (contain373_10 D)
    step107_o373_row10_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_373.occRhs ⟨10, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_11 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨11, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource11 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource11
      step107_o373_row11_W_le_source (D.A t) ⟨2, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource11
      step107_o373_row11_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource11
      step107_o373_row11_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource11
      step107_o373_row11_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource11
      step107_o373_row11_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource11
      step107_o373_row11_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource11
      step107_o373_row11_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_11 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨11, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨11, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row11_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨11, by decide⟩)
    (contain373_11 D)
    step107_o373_row11_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_373.occRhs ⟨11, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_12 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨12, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource12 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource12
      step107_o373_row12_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource12
      step107_o373_row12_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource12
      step107_o373_row12_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource12
      step107_o373_row12_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource12
      step107_o373_row12_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource12
      step107_o373_row12_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource12
      step107_o373_row12_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_12 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨12, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨12, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row12_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨12, by decide⟩)
    (contain373_12 D)
    step107_o373_row12_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_373.occRhs ⟨12, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_13 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨13, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource13 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource13
      step107_o373_row13_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource13
      step107_o373_row13_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource13
      step107_o373_row13_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource13
      step107_o373_row13_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource13
      step107_o373_row13_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource13
      step107_o373_row13_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource13
      step107_o373_row13_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_13 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨13, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨13, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row13_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨13, by decide⟩)
    (contain373_13 D)
    step107_o373_row13_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_373.occRhs ⟨13, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_14 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨14, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource14 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource14
      step107_o373_row14_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource14
      step107_o373_row14_W_le_source (D.A t) ⟨9, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource14
      step107_o373_row14_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource14
      step107_o373_row14_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource14
      step107_o373_row14_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource14
      step107_o373_row14_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource14
      step107_o373_row14_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_14 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨14, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨14, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row14_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨14, by decide⟩)
    (contain373_14 D)
    step107_o373_row14_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_373.occRhs ⟨14, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_15 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨15, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource15 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource15
      step107_o373_row15_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource15
      step107_o373_row15_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource15
      step107_o373_row15_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource15
      step107_o373_row15_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource15
      step107_o373_row15_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource15
      step107_o373_row15_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource15
      step107_o373_row15_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_15 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨15, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨15, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row15_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨15, by decide⟩)
    (contain373_15 D)
    step107_o373_row15_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_373.occRhs ⟨15, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_16 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨16, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource16 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource16
      step107_o373_row16_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource16
      step107_o373_row16_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource16
      step107_o373_row16_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource16
      step107_o373_row16_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource16
      step107_o373_row16_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource16
      step107_o373_row16_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource16
      step107_o373_row16_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_16 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨16, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨16, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row16_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨16, by decide⟩)
    (contain373_16 D)
    step107_o373_row16_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_373.occRhs ⟨16, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_17 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨17, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource17 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource17
      step107_o373_row17_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource17
      step107_o373_row17_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource17
      step107_o373_row17_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource17
      step107_o373_row17_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource17
      step107_o373_row17_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource17
      step107_o373_row17_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource17
      step107_o373_row17_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_17 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨17, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨17, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row17_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨17, by decide⟩)
    (contain373_17 D)
    step107_o373_row17_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_373.occRhs ⟨17, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_18 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨18, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource18 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource18
      step107_o373_row18_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource18
      step107_o373_row18_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource18
      step107_o373_row18_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource18
      step107_o373_row18_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource18
      step107_o373_row18_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource18
      step107_o373_row18_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource18
      step107_o373_row18_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_18 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨18, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨18, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row18_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨18, by decide⟩)
    (contain373_18 D)
    step107_o373_row18_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_373.occRhs ⟨18, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_19 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨19, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource19 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource19
      step107_o373_row19_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource19
      step107_o373_row19_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource19
      step107_o373_row19_W_le_source (D.A t) ⟨6, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource19
      step107_o373_row19_W_le_source (D.A t) ⟨9, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource19
      step107_o373_row19_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource19
      step107_o373_row19_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource19
      step107_o373_row19_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource19
      step107_o373_row19_W_le_source (D.A t) ⟨15, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource19
      step107_o373_row19_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource19
      step107_o373_row19_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource19
      step107_o373_row19_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource19
      step107_o373_row19_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource19
      step107_o373_row19_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource19
      step107_o373_row19_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource19
      step107_o373_row19_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_19 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨19, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨19, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row19_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨19, by decide⟩)
    (contain373_19 D)
    step107_o373_row19_qr
    (show (9 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(7 : ℕ) : Int) = S_373.occRhs ⟨19, by decide⟩ := by decide
  rw [show (16 : ℕ) - 9 = 7 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_20 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨20, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource20 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource20
      step107_o373_row20_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource20
      step107_o373_row20_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource20
      step107_o373_row20_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource20
      step107_o373_row20_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource20
      step107_o373_row20_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource20
      step107_o373_row20_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource20
      step107_o373_row20_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource20
      step107_o373_row20_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource20
      step107_o373_row20_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource20
      step107_o373_row20_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource20
      step107_o373_row20_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource20
      step107_o373_row20_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource20
      step107_o373_row20_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource20
      step107_o373_row20_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource20
      step107_o373_row20_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_20 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨20, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨20, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row20_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨20, by decide⟩)
    (contain373_20 D)
    step107_o373_row20_qr
    (show (9 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(7 : ℕ) : Int) = S_373.occRhs ⟨20, by decide⟩ := by decide
  rw [show (16 : ℕ) - 9 = 7 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_21 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨21, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource21 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource21
      step107_o373_row21_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource21
      step107_o373_row21_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource21
      step107_o373_row21_W_le_source (D.A t) ⟨6, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource21
      step107_o373_row21_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource21
      step107_o373_row21_W_le_source (D.A t) ⟨9, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource21
      step107_o373_row21_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource21
      step107_o373_row21_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource21
      step107_o373_row21_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource21
      step107_o373_row21_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource21
      step107_o373_row21_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource21
      step107_o373_row21_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource21
      step107_o373_row21_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource21
      step107_o373_row21_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource21
      step107_o373_row21_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource21
      step107_o373_row21_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_21 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨21, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨21, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row21_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨21, by decide⟩)
    (contain373_21 D)
    step107_o373_row21_qr
    (show (9 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(7 : ℕ) : Int) = S_373.occRhs ⟨21, by decide⟩ := by decide
  rw [show (16 : ℕ) - 9 = 7 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_22 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨22, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource22 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource22
      step107_o373_row22_W_le_source (D.A t) ⟨2, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource22
      step107_o373_row22_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource22
      step107_o373_row22_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource22
      step107_o373_row22_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource22
      step107_o373_row22_W_le_source (D.A t) ⟨9, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource22
      step107_o373_row22_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource22
      step107_o373_row22_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource22
      step107_o373_row22_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource22
      step107_o373_row22_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource22
      step107_o373_row22_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource22
      step107_o373_row22_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource22
      step107_o373_row22_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource22
      step107_o373_row22_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource22
      step107_o373_row22_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource22
      step107_o373_row22_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_22 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨22, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨22, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row22_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨22, by decide⟩)
    (contain373_22 D)
    step107_o373_row22_qr
    (show (9 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(7 : ℕ) : Int) = S_373.occRhs ⟨22, by decide⟩ := by decide
  rw [show (16 : ℕ) - 9 = 7 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_23 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨23, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource23 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource23
      step107_o373_row23_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource23
      step107_o373_row23_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource23
      step107_o373_row23_W_le_source (D.A t) ⟨6, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource23
      step107_o373_row23_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource23
      step107_o373_row23_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource23
      step107_o373_row23_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource23
      step107_o373_row23_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource23
      step107_o373_row23_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource23
      step107_o373_row23_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource23
      step107_o373_row23_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource23
      step107_o373_row23_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource23
      step107_o373_row23_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource23
      step107_o373_row23_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource23
      step107_o373_row23_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource23
      step107_o373_row23_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_23 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨23, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨23, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row23_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨23, by decide⟩)
    (contain373_23 D)
    step107_o373_row23_qr
    (show (9 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(7 : ℕ) : Int) = S_373.occRhs ⟨23, by decide⟩ := by decide
  rw [show (16 : ℕ) - 9 = 7 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_24 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨24, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource24 := by
  simp only [mem_image, activeSet373, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  subst hj
  apply contain373_of_sec step107o373ActualSource24
    step107_o373_row24_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
  exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_24 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨24, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨24, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row24_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨24, by decide⟩)
    (contain373_24 D)
    step107_o373_row24_qr
    (show (16 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(0 : ℕ) : Int) = S_373.occRhs ⟨24, by decide⟩ := by decide
  rw [show (16 : ℕ) - 16 = 0 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_25 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨25, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource25 := by
  simp only [mem_image, activeSet373, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  subst hj
  apply contain373_of_sec step107o373ActualSource25
    step107_o373_row25_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
  exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_25 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨25, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨25, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row25_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨25, by decide⟩)
    (contain373_25 D)
    step107_o373_row25_qr
    (show (15 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(1 : ℕ) : Int) = S_373.occRhs ⟨25, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_26 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨26, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource26 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource26
      step107_o373_row26_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource26
      step107_o373_row26_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource26
      step107_o373_row26_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_26 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨26, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨26, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row26_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨26, by decide⟩)
    (contain373_26 D)
    step107_o373_row26_qr
    (show (15 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(1 : ℕ) : Int) = S_373.occRhs ⟨26, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_27 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨27, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource27 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource27
      step107_o373_row27_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource27
      step107_o373_row27_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource27
      step107_o373_row27_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_27 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨27, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨27, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row27_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨27, by decide⟩)
    (contain373_27 D)
    step107_o373_row27_qr
    (show (15 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(1 : ℕ) : Int) = S_373.occRhs ⟨27, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_28 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨28, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource28 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource28
      step107_o373_row28_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource28
      step107_o373_row28_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource28
      step107_o373_row28_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_28 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨28, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨28, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row28_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨28, by decide⟩)
    (contain373_28 D)
    step107_o373_row28_qr
    (show (15 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(1 : ℕ) : Int) = S_373.occRhs ⟨28, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_29 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨29, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource29 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource29
      step107_o373_row29_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource29
      step107_o373_row29_W_le_source (D.A t) ⟨9, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource29
      step107_o373_row29_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_29 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨29, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨29, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row29_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨29, by decide⟩)
    (contain373_29 D)
    step107_o373_row29_qr
    (show (14 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(2 : ℕ) : Int) = S_373.occRhs ⟨29, by decide⟩ := by decide
  rw [show (16 : ℕ) - 14 = 2 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_30 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨30, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource30 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource30
      step107_o373_row30_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource30
      step107_o373_row30_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource30
      step107_o373_row30_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_30 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨30, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨30, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row30_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨30, by decide⟩)
    (contain373_30 D)
    step107_o373_row30_qr
    (show (14 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(2 : ℕ) : Int) = S_373.occRhs ⟨30, by decide⟩ := by decide
  rw [show (16 : ℕ) - 14 = 2 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_31 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨31, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource31 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource31
      step107_o373_row31_W_le_source (D.A t) ⟨2, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource31
      step107_o373_row31_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource31
      step107_o373_row31_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource31
      step107_o373_row31_W_le_source (D.A t) ⟨15, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource31
      step107_o373_row31_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource31
      step107_o373_row31_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource31
      step107_o373_row31_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_31 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨31, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨31, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row31_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨31, by decide⟩)
    (contain373_31 D)
    step107_o373_row31_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_373.occRhs ⟨31, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_32 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨32, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource32 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource32
      step107_o373_row32_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource32
      step107_o373_row32_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource32
      step107_o373_row32_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource32
      step107_o373_row32_W_le_source (D.A t) ⟨15, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource32
      step107_o373_row32_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource32
      step107_o373_row32_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource32
      step107_o373_row32_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_32 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨32, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨32, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row32_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨32, by decide⟩)
    (contain373_32 D)
    step107_o373_row32_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_373.occRhs ⟨32, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_33 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨33, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource33 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource33
      step107_o373_row33_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource33
      step107_o373_row33_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource33
      step107_o373_row33_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource33
      step107_o373_row33_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource33
      step107_o373_row33_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource33
      step107_o373_row33_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource33
      step107_o373_row33_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_33 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨33, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨33, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row33_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨33, by decide⟩)
    (contain373_33 D)
    step107_o373_row33_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_373.occRhs ⟨33, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_34 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨34, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource34 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource34
      step107_o373_row34_W_le_source (D.A t) ⟨2, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource34
      step107_o373_row34_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource34
      step107_o373_row34_W_le_source (D.A t) ⟨9, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource34
      step107_o373_row34_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource34
      step107_o373_row34_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource34
      step107_o373_row34_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource34
      step107_o373_row34_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_34 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨34, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨34, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row34_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨34, by decide⟩)
    (contain373_34 D)
    step107_o373_row34_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_373.occRhs ⟨34, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_35 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨35, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource35 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource35
      step107_o373_row35_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource35
      step107_o373_row35_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource35
      step107_o373_row35_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource35
      step107_o373_row35_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource35
      step107_o373_row35_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource35
      step107_o373_row35_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource35
      step107_o373_row35_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_35 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨35, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨35, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row35_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨35, by decide⟩)
    (contain373_35 D)
    step107_o373_row35_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_373.occRhs ⟨35, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_36 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨36, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource36 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource36
      step107_o373_row36_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource36
      step107_o373_row36_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource36
      step107_o373_row36_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource36
      step107_o373_row36_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource36
      step107_o373_row36_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource36
      step107_o373_row36_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource36
      step107_o373_row36_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_36 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨36, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨36, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row36_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨36, by decide⟩)
    (contain373_36 D)
    step107_o373_row36_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_373.occRhs ⟨36, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_37 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨37, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource37 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource37
      step107_o373_row37_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource37
      step107_o373_row37_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource37
      step107_o373_row37_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource37
      step107_o373_row37_W_le_source (D.A t) ⟨9, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource37
      step107_o373_row37_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource37
      step107_o373_row37_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource37
      step107_o373_row37_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource37
      step107_o373_row37_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource37
      step107_o373_row37_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource37
      step107_o373_row37_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource37
      step107_o373_row37_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource37
      step107_o373_row37_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource37
      step107_o373_row37_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource37
      step107_o373_row37_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource37
      step107_o373_row37_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_37 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨37, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨37, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row37_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨37, by decide⟩)
    (contain373_37 D)
    step107_o373_row37_qr
    (show (9 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(7 : ℕ) : Int) = S_373.occRhs ⟨37, by decide⟩ := by decide
  rw [show (16 : ℕ) - 9 = 7 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_38 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨38, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource38 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource38
      step107_o373_row38_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource38
      step107_o373_row38_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource38
      step107_o373_row38_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_38 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨38, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨38, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row38_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨38, by decide⟩)
    (contain373_38 D)
    step107_o373_row38_qr
    (show (15 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(1 : ℕ) : Int) = S_373.occRhs ⟨38, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_39 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨39, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource39 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource39
      step107_o373_row39_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource39
      step107_o373_row39_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource39
      step107_o373_row39_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_39 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨39, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨39, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row39_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨39, by decide⟩)
    (contain373_39 D)
    step107_o373_row39_qr
    (show (14 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(2 : ℕ) : Int) = S_373.occRhs ⟨39, by decide⟩ := by decide
  rw [show (16 : ℕ) - 14 = 2 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_40 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨40, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource40 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource40
      step107_o373_row40_W_le_source (D.A t) ⟨2, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource40
      step107_o373_row40_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource40
      step107_o373_row40_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource40
      step107_o373_row40_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource40
      step107_o373_row40_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource40
      step107_o373_row40_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource40
      step107_o373_row40_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_40 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨40, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨40, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row40_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨40, by decide⟩)
    (contain373_40 D)
    step107_o373_row40_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_373.occRhs ⟨40, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_41 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨41, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource41 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource41
      step107_o373_row41_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource41
      step107_o373_row41_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource41
      step107_o373_row41_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource41
      step107_o373_row41_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource41
      step107_o373_row41_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource41
      step107_o373_row41_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource41
      step107_o373_row41_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_41 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨41, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨41, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row41_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨41, by decide⟩)
    (contain373_41 D)
    step107_o373_row41_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_373.occRhs ⟨41, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_42 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨42, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource42 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource42
      step107_o373_row42_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource42
      step107_o373_row42_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource42
      step107_o373_row42_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource42
      step107_o373_row42_W_le_source (D.A t) ⟨15, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource42
      step107_o373_row42_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource42
      step107_o373_row42_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource42
      step107_o373_row42_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_42 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨42, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨42, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row42_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨42, by decide⟩)
    (contain373_42 D)
    step107_o373_row42_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_373.occRhs ⟨42, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_43 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨43, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource43 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource43
      step107_o373_row43_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource43
      step107_o373_row43_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource43
      step107_o373_row43_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource43
      step107_o373_row43_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource43
      step107_o373_row43_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource43
      step107_o373_row43_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource43
      step107_o373_row43_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_43 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨43, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨43, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row43_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨43, by decide⟩)
    (contain373_43 D)
    step107_o373_row43_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_373.occRhs ⟨43, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_44 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨44, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource44 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource44
      step107_o373_row44_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource44
      step107_o373_row44_W_le_source (D.A t) ⟨9, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource44
      step107_o373_row44_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource44
      step107_o373_row44_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource44
      step107_o373_row44_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource44
      step107_o373_row44_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource44
      step107_o373_row44_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_44 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨44, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨44, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row44_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨44, by decide⟩)
    (contain373_44 D)
    step107_o373_row44_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_373.occRhs ⟨44, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_45 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨45, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource45 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource45
      step107_o373_row45_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource45
      step107_o373_row45_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource45
      step107_o373_row45_W_le_source (D.A t) ⟨6, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource45
      step107_o373_row45_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource45
      step107_o373_row45_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource45
      step107_o373_row45_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource45
      step107_o373_row45_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_45 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨45, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨45, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row45_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨45, by decide⟩)
    (contain373_45 D)
    step107_o373_row45_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_373.occRhs ⟨45, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_46 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨46, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource46 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource46
      step107_o373_row46_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource46
      step107_o373_row46_W_le_source (D.A t) ⟨9, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource46
      step107_o373_row46_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource46
      step107_o373_row46_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource46
      step107_o373_row46_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource46
      step107_o373_row46_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource46
      step107_o373_row46_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_46 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨46, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨46, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row46_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨46, by decide⟩)
    (contain373_46 D)
    step107_o373_row46_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_373.occRhs ⟨46, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_47 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨47, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource47 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource47
      step107_o373_row47_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource47
      step107_o373_row47_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource47
      step107_o373_row47_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource47
      step107_o373_row47_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource47
      step107_o373_row47_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource47
      step107_o373_row47_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource47
      step107_o373_row47_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_47 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨47, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨47, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row47_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨47, by decide⟩)
    (contain373_47 D)
    step107_o373_row47_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_373.occRhs ⟨47, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_48 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨48, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource48 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource48
      step107_o373_row48_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource48
      step107_o373_row48_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource48
      step107_o373_row48_W_le_source (D.A t) ⟨6, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource48
      step107_o373_row48_W_le_source (D.A t) ⟨9, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource48
      step107_o373_row48_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource48
      step107_o373_row48_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource48
      step107_o373_row48_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_48 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨48, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨48, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row48_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨48, by decide⟩)
    (contain373_48 D)
    step107_o373_row48_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_373.occRhs ⟨48, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_49 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨49, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource49 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource49
      step107_o373_row49_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource49
      step107_o373_row49_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource49
      step107_o373_row49_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource49
      step107_o373_row49_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource49
      step107_o373_row49_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource49
      step107_o373_row49_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource49
      step107_o373_row49_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_49 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨49, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨49, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row49_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨49, by decide⟩)
    (contain373_49 D)
    step107_o373_row49_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_373.occRhs ⟨49, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_50 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨50, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource50 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource50
      step107_o373_row50_W_le_source (D.A t) ⟨2, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource50
      step107_o373_row50_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource50
      step107_o373_row50_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource50
      step107_o373_row50_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource50
      step107_o373_row50_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource50
      step107_o373_row50_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource50
      step107_o373_row50_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_50 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨50, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨50, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row50_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨50, by decide⟩)
    (contain373_50 D)
    step107_o373_row50_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_373.occRhs ⟨50, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_51 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨51, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource51 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource51
      step107_o373_row51_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource51
      step107_o373_row51_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource51
      step107_o373_row51_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource51
      step107_o373_row51_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource51
      step107_o373_row51_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource51
      step107_o373_row51_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource51
      step107_o373_row51_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource51
      step107_o373_row51_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource51
      step107_o373_row51_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource51
      step107_o373_row51_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource51
      step107_o373_row51_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource51
      step107_o373_row51_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource51
      step107_o373_row51_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource51
      step107_o373_row51_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource51
      step107_o373_row51_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_51 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨51, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨51, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row51_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨51, by decide⟩)
    (contain373_51 D)
    step107_o373_row51_qr
    (show (9 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(7 : ℕ) : Int) = S_373.occRhs ⟨51, by decide⟩ := by decide
  rw [show (16 : ℕ) - 9 = 7 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_52 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨52, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource52 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource52
      step107_o373_row52_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource52
      step107_o373_row52_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource52
      step107_o373_row52_W_le_source (D.A t) ⟨6, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_52 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨52, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨52, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row52_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨52, by decide⟩)
    (contain373_52 D)
    step107_o373_row52_qr
    (show (14 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(2 : ℕ) : Int) = S_373.occRhs ⟨52, by decide⟩ := by decide
  rw [show (16 : ℕ) - 14 = 2 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_53 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨53, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource53 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource53
      step107_o373_row53_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource53
      step107_o373_row53_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource53
      step107_o373_row53_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource53
      step107_o373_row53_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource53
      step107_o373_row53_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource53
      step107_o373_row53_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource53
      step107_o373_row53_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_53 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨53, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨53, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row53_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨53, by decide⟩)
    (contain373_53 D)
    step107_o373_row53_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_373.occRhs ⟨53, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_54 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨54, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource54 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource54
      step107_o373_row54_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource54
      step107_o373_row54_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource54
      step107_o373_row54_W_le_source (D.A t) ⟨9, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource54
      step107_o373_row54_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource54
      step107_o373_row54_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource54
      step107_o373_row54_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource54
      step107_o373_row54_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_54 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨54, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨54, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row54_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨54, by decide⟩)
    (contain373_54 D)
    step107_o373_row54_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_373.occRhs ⟨54, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_55 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨55, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource55 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource55
      step107_o373_row55_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource55
      step107_o373_row55_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource55
      step107_o373_row55_W_le_source (D.A t) ⟨6, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource55
      step107_o373_row55_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource55
      step107_o373_row55_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource55
      step107_o373_row55_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource55
      step107_o373_row55_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_55 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨55, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨55, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row55_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨55, by decide⟩)
    (contain373_55 D)
    step107_o373_row55_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_373.occRhs ⟨55, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain373_56 (D : QuotientTensorDecomp o373W 16)
    (t : Fin 16)
    (ht : label373 (D.A t) ∈ (activeSet373 ⟨56, by decide⟩).image Fin.succ) :
    D.A t ∈ step107o373ActualSource56 := by
  simp only [mem_image, activeSet373, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain373_of_sec step107o373ActualSource56
      step107_o373_row56_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource56
      step107_o373_row56_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource56
      step107_o373_row56_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource56
      step107_o373_row56_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource56
      step107_o373_row56_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource56
      step107_o373_row56_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain373_of_sec step107o373ActualSource56
      step107_o373_row56_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound373_56 (D : QuotientTensorDecomp o373W 16) :
    ∑ j ∈ activeSet373 ⟨56, by decide⟩,
      occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_373.occRhs ⟨56, by decide⟩ := by
  have h := live_labeled_fiber_occ_row_int
    step107_o373_row56_W_le_source D
    (fun t : Fin 16 => label373 (D.A t))
    (activeSet373 ⟨56, by decide⟩)
    (contain373_56 D)
    step107_o373_row56_qr
    (show (12 : ℕ) ≤ 16 by omega)
    (show (16 : ℕ) ≤ 16 by omega)
  have hcap : (↑(4 : ℕ) : Int) = S_373.occRhs ⟨56, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem coeffMatch373 (i : Fin 57) (j : Fin 31) :
    S_373.occCoeff i j = if j ∈ activeSet373 i then 1 else 0 := by
  fin_cases i <;> (fin_cases j <;> decide)

private theorem o373_extractRootHolds (D : QuotientTensorDecomp o373W 16) :
    S_373.RootHolds (occVectorInt (fun t : Fin 16 => label373 (D.A t)) 31 (Nat.le_refl _)) :=
  rootHolds_from_label_bounds S_373 _
    (fun j => occVectorInt_nonneg _ _ j)
    (o373_total D)
    activeSet373
    (fun i => by
      fin_cases i
      · exact rowBound373_0 D
      · exact rowBound373_1 D
      · exact rowBound373_2 D
      · exact rowBound373_3 D
      · exact rowBound373_4 D
      · exact rowBound373_5 D
      · exact rowBound373_6 D
      · exact rowBound373_7 D
      · exact rowBound373_8 D
      · exact rowBound373_9 D
      · exact rowBound373_10 D
      · exact rowBound373_11 D
      · exact rowBound373_12 D
      · exact rowBound373_13 D
      · exact rowBound373_14 D
      · exact rowBound373_15 D
      · exact rowBound373_16 D
      · exact rowBound373_17 D
      · exact rowBound373_18 D
      · exact rowBound373_19 D
      · exact rowBound373_20 D
      · exact rowBound373_21 D
      · exact rowBound373_22 D
      · exact rowBound373_23 D
      · exact rowBound373_24 D
      · exact rowBound373_25 D
      · exact rowBound373_26 D
      · exact rowBound373_27 D
      · exact rowBound373_28 D
      · exact rowBound373_29 D
      · exact rowBound373_30 D
      · exact rowBound373_31 D
      · exact rowBound373_32 D
      · exact rowBound373_33 D
      · exact rowBound373_34 D
      · exact rowBound373_35 D
      · exact rowBound373_36 D
      · exact rowBound373_37 D
      · exact rowBound373_38 D
      · exact rowBound373_39 D
      · exact rowBound373_40 D
      · exact rowBound373_41 D
      · exact rowBound373_42 D
      · exact rowBound373_43 D
      · exact rowBound373_44 D
      · exact rowBound373_45 D
      · exact rowBound373_46 D
      · exact rowBound373_47 D
      · exact rowBound373_48 D
      · exact rowBound373_49 D
      · exact rowBound373_50 D
      · exact rowBound373_51 D
      · exact rowBound373_52 D
      · exact rowBound373_53 D
      · exact rowBound373_54 D
      · exact rowBound373_55 D
      · exact rowBound373_56 D
    )
    (fun i j => coeffMatch373 i j)

/-- Unconditional orbit-373 quotient rank lower bound. -/
theorem step107_orbit373_lb17 : QuotientRankAtLeast o373W 17 := by
  apply branchBridge_quotientRankAtLeast o373W 16 S_373 orbit373_occupation_no_model
  intro r hr D
  by_cases hr16 : r < 16
  · exact False.elim ((step107_o373_base_lb16 r hr16).false D)
  · have hrr : r = 16 := by omega
    subst hrr
    exact ⟨_, o373_extractRootHolds D⟩

end QiushiMatmul
