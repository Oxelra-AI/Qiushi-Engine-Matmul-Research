import QiushiStep103O279LabelProbe
import QiushiStep103Orbit279Dispatches
import QiushiExtractionBridge
import QiushiOrbit279BranchNoModel
import QiushiMonotonicity

set_option maxHeartbeats 80000000
set_option synthInstance.maxHeartbeats 80000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

theorem contain279_of_sec
    (U : Submodule F2 Mat3) (hWU : o279W ≤ U)
    (M : Mat3) (j : Fin 31) (hlabel : label279 M = Fin.succ j)
    (hsec : codeMat (sectionCode279 (Fin.succ j)) ∈ U) : M ∈ U := by
  have hrec := reconstruction279_mem M
  rw [hlabel] at hrec
  have hrecU : M + codeMat (sectionCode279 (Fin.succ j)) ∈ U := hWU hrec
  have : M + codeMat (sectionCode279 (Fin.succ j)) +
      codeMat (sectionCode279 (Fin.succ j)) = M := by
    rw [add_assoc, mat3_add_self_eq_zero, add_zero]
  rw [← this]; exact U.add_mem hrecU hsec

theorem o279_zeroFiber (D : QuotientTensorDecomp o279W 16) :
    occFiberCard' (fun t : Fin 16 => label279 (D.A t)) ⟨0, by decide⟩ = 0 := by
  have hkill := zero_fiber_from_preceding_bound step103_o279_base_lb16 D
  have hsub : (univ.filter (fun t : Fin 16 => label279 (D.A t) = ⟨0, by decide⟩))
      ⊆ killSet D o279W := by
    intro t ht
    simp only [mem_filter, mem_univ, true_and] at ht
    simp only [killSet, mem_filter, mem_univ, true_and]
    exact label279_eq_zero_mem (D.A t) ht
  exact Nat.eq_zero_of_le_zero (le_trans (card_le_card hsub) (Nat.le_of_eq hkill))

theorem o279_total (D : QuotientTensorDecomp o279W 16) :
    (16 : Int) ≤ ∑ j : Fin 31, occVectorInt
      (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _) j := by
  have := occVectorInt_total_of_zero
    (fun t : Fin 16 => label279 (D.A t)) (o279_zeroFiber D)
  exact le_of_eq this.symm

def activeSet279 : Fin 64 → Finset (Fin 31)
  | ⟨0, _⟩ => {⟨29, by decide⟩}
  | ⟨1, _⟩ => {⟨5, by decide⟩}
  | ⟨2, _⟩ => {⟨6, by decide⟩}
  | ⟨3, _⟩ => {⟨7, by decide⟩}
  | ⟨4, _⟩ => {⟨0, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩}
  | ⟨5, _⟩ => {⟨0, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩}
  | ⟨6, _⟩ => {⟨12, by decide⟩, ⟨20, by decide⟩, ⟨23, by decide⟩}
  | ⟨7, _⟩ => {⟨12, by decide⟩, ⟨19, by decide⟩, ⟨24, by decide⟩}
  | ⟨8, _⟩ => {⟨11, by decide⟩, ⟨20, by decide⟩, ⟨24, by decide⟩}
  | ⟨9, _⟩ => {⟨12, by decide⟩, ⟨21, by decide⟩, ⟨26, by decide⟩}
  | ⟨10, _⟩ => {⟨1, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨23, by decide⟩, ⟨25, by decide⟩}
  | ⟨11, _⟩ => {⟨1, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩}
  | ⟨12, _⟩ => {⟨5, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨15, by decide⟩, ⟨21, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩}
  | ⟨13, _⟩ => {⟨6, by decide⟩, ⟨7, by decide⟩, ⟨14, by decide⟩, ⟨17, by decide⟩, ⟨20, by decide⟩, ⟨25, by decide⟩, ⟨28, by decide⟩}
  | ⟨14, _⟩ => {⟨5, by decide⟩, ⟨8, by decide⟩, ⟨14, by decide⟩, ⟨17, by decide⟩, ⟨19, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩}
  | ⟨15, _⟩ => {⟨2, by decide⟩, ⟨7, by decide⟩, ⟨10, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩}
  | ⟨16, _⟩ => {⟨6, by decide⟩, ⟨9, by decide⟩, ⟨12, by decide⟩, ⟨17, by decide⟩, ⟨20, by decide⟩, ⟨23, by decide⟩, ⟨30, by decide⟩}
  | ⟨17, _⟩ => {⟨5, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨17, by decide⟩, ⟨19, by decide⟩, ⟨24, by decide⟩, ⟨30, by decide⟩}
  | ⟨18, _⟩ => {⟨2, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩}
  | ⟨19, _⟩ => {⟨2, by decide⟩, ⟨11, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨18, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩}
  | ⟨20, _⟩ => {⟨1, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨17, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩}
  | ⟨21, _⟩ => {⟨16, by decide⟩}
  | ⟨22, _⟩ => {⟨28, by decide⟩}
  | ⟨23, _⟩ => {⟨11, by decide⟩, ⟨19, by decide⟩, ⟨23, by decide⟩}
  | ⟨24, _⟩ => {⟨1, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨22, by decide⟩}
  | ⟨25, _⟩ => {⟨6, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨15, by decide⟩, ⟨22, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩}
  | ⟨26, _⟩ => {⟨1, by decide⟩, ⟨11, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩, ⟨17, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩}
  | ⟨27, _⟩ => {⟨2, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨19, by decide⟩, ⟨22, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩}
  | ⟨28, _⟩ => {⟨2, by decide⟩, ⟨3, by decide⟩, ⟨6, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩}
  | ⟨29, _⟩ => {⟨1, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩}
  | ⟨30, _⟩ => {⟨2, by decide⟩, ⟨3, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨22, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩}
  | ⟨31, _⟩ => {⟨3, by decide⟩, ⟨7, by decide⟩, ⟨11, by decide⟩, ⟨15, by decide⟩, ⟨19, by decide⟩, ⟨23, by decide⟩, ⟨27, by decide⟩}
  | ⟨32, _⟩ => {⟨3, by decide⟩, ⟨8, by decide⟩, ⟨12, by decide⟩, ⟨17, by decide⟩, ⟨21, by decide⟩, ⟨26, by decide⟩, ⟨30, by decide⟩}
  | ⟨33, _⟩ => {⟨2, by decide⟩, ⟨3, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩}
  | ⟨34, _⟩ => {⟨1, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨13, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨22, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩}
  | ⟨35, _⟩ => {⟨18, by decide⟩}
  | ⟨36, _⟩ => {⟨3, by decide⟩}
  | ⟨37, _⟩ => {⟨11, by decide⟩, ⟨21, by decide⟩, ⟨25, by decide⟩}
  | ⟨38, _⟩ => {⟨1, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨21, by decide⟩}
  | ⟨39, _⟩ => {⟨4, by decide⟩, ⟨10, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩, ⟨20, by decide⟩, ⟨26, by decide⟩, ⟨29, by decide⟩}
  | ⟨40, _⟩ => {⟨2, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨23, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩}
  | ⟨41, _⟩ => {⟨4, by decide⟩, ⟨7, by decide⟩, ⟨12, by decide⟩, ⟨17, by decide⟩, ⟨22, by decide⟩, ⟨25, by decide⟩, ⟨30, by decide⟩}
  | ⟨42, _⟩ => {⟨1, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨21, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩}
  | ⟨43, _⟩ => {⟨1, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨13, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨21, by decide⟩, ⟨23, by decide⟩, ⟨25, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩}
  | ⟨44, _⟩ => {⟨3, by decide⟩, ⟨9, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩, ⟨19, by decide⟩, ⟨25, by decide⟩, ⟨29, by decide⟩}
  | ⟨45, _⟩ => {⟨9, by decide⟩}
  | ⟨46, _⟩ => {⟨10, by decide⟩}
  | ⟨47, _⟩ => {⟨4, by decide⟩, ⟨8, by decide⟩, ⟨11, by decide⟩, ⟨15, by decide⟩, ⟨20, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩}
  | ⟨48, _⟩ => {⟨5, by decide⟩, ⟨8, by decide⟩, ⟨14, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩}
  | ⟨49, _⟩ => {⟨3, by decide⟩, ⟨9, by decide⟩, ⟨13, by decide⟩, ⟨16, by decide⟩, ⟨20, by decide⟩, ⟨26, by decide⟩, ⟨30, by decide⟩}
  | ⟨50, _⟩ => {⟨2, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨19, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩}
  | ⟨51, _⟩ => {⟨13, by decide⟩, ⟨16, by decide⟩, ⟨30, by decide⟩}
  | ⟨52, _⟩ => {⟨2, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨23, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩}
  | ⟨53, _⟩ => {⟨5, by decide⟩, ⟨7, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩, ⟨21, by decide⟩, ⟨23, by decide⟩, ⟨29, by decide⟩}
  | ⟨54, _⟩ => {⟨12, by decide⟩, ⟨22, by decide⟩, ⟨25, by decide⟩}
  | ⟨55, _⟩ => {⟨11, by decide⟩, ⟨22, by decide⟩, ⟨26, by decide⟩}
  | ⟨56, _⟩ => {⟨6, by decide⟩, ⟨8, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩, ⟨22, by decide⟩, ⟨24, by decide⟩, ⟨29, by decide⟩}
  | ⟨57, _⟩ => {⟨5, by decide⟩, ⟨7, by decide⟩, ⟨13, by decide⟩, ⟨16, by decide⟩, ⟨22, by decide⟩, ⟨24, by decide⟩, ⟨30, by decide⟩}
  | ⟨58, _⟩ => {⟨0, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩}
  | ⟨59, _⟩ => {⟨2, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨19, by decide⟩, ⟨22, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩}
  | ⟨60, _⟩ => {⟨4, by decide⟩, ⟨9, by decide⟩, ⟨14, by decide⟩, ⟨18, by decide⟩, ⟨21, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩}
  | ⟨61, _⟩ => {⟨3, by decide⟩, ⟨10, by decide⟩, ⟨14, by decide⟩, ⟨18, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨27, by decide⟩}
  | ⟨62, _⟩ => {⟨4, by decide⟩, ⟨9, by decide⟩, ⟨14, by decide⟩, ⟨17, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨28, by decide⟩}
  | ⟨63, _⟩ => {⟨6, by decide⟩, ⟨8, by decide⟩, ⟨13, by decide⟩, ⟨16, by decide⟩, ⟨21, by decide⟩, ⟨23, by decide⟩, ⟨30, by decide⟩}
  | _ => ∅

end QiushiMatmul
