import QiushiBranch415LabelProbe
import QiushiBranch415Dispatch
import QiushiExtractionBridgePadded
import QiushiBranch415NoModel
import QiushiMonotonicity

set_option maxHeartbeats 80000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem contain415_of_sec
    (U : Submodule F2 Mat3) (hWU : o415W ≤ U)
    (M : Mat3) (j : Fin 63) (hlabel : label415 M = Fin.succ j)
    (hsec : codeMat (sectionCode415 (Fin.succ j)) ∈ U) : M ∈ U := by
  have hrec := reconstruction415_mem M
  rw [hlabel] at hrec; have hrecU := hWU hrec
  have : M + codeMat (sectionCode415 (Fin.succ j)) +
      codeMat (sectionCode415 (Fin.succ j)) = M := by
    rw [add_assoc, mat3_add_self_eq_zero, add_zero]
  rw [← this]; exact U.add_mem hrecU hsec

private theorem o415_total {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    (16 : Int) ≤ ∑ j : Fin 63, occVectorIntPadded
      (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j := by
  have htot := occVectorIntPadded_total (fun t : Fin r => label415 (D.A t)) ⟨0, by decide⟩ hr
  rw [htot]
  norm_num

def activeSet415 : Fin 101 → Finset (Fin 63)
  | ⟨0, _⟩ => {⟨2, by decide⟩, ⟨7, by decide⟩, ⟨10, by decide⟩}
  | ⟨1, _⟩ => {⟨5, by decide⟩, ⟨7, by decide⟩, ⟨13, by decide⟩}
  | ⟨2, _⟩ => {⟨6, by decide⟩, ⟨7, by decide⟩, ⟨14, by decide⟩}
  | ⟨3, _⟩ => {⟨16, by decide⟩, ⟨31, by decide⟩, ⟨48, by decide⟩}
  | ⟨4, _⟩ => {⟨18, by decide⟩, ⟨40, by decide⟩, ⟨57, by decide⟩}
  | ⟨5, _⟩ => {⟨19, by decide⟩, ⟨42, by decide⟩, ⟨62, by decide⟩}
  | ⟨6, _⟩ => {⟨27, by decide⟩, ⟨42, by decide⟩, ⟨54, by decide⟩}
  | ⟨7, _⟩ => {⟨22, by decide⟩, ⟨41, by decide⟩, ⟨60, by decide⟩}
  | ⟨8, _⟩ => {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩}
  | ⟨9, _⟩ => {⟨0, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩}
  | ⟨10, _⟩ => {⟨0, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩}
  | ⟨11, _⟩ => {⟨0, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩}
  | ⟨12, _⟩ => {⟨0, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩}
  | ⟨13, _⟩ => {⟨0, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩}
  | ⟨14, _⟩ => {⟨0, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩}
  | ⟨15, _⟩ => {⟨3, by decide⟩, ⟨7, by decide⟩, ⟨11, by decide⟩, ⟨34, by decide⟩, ⟨38, by decide⟩, ⟨42, by decide⟩, ⟨46, by decide⟩}
  | ⟨16, _⟩ => {⟨4, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩, ⟨31, by decide⟩, ⟨36, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩}
  | ⟨17, _⟩ => {⟨12, by decide⟩, ⟨21, by decide⟩, ⟨26, by decide⟩, ⟨35, by decide⟩, ⟨40, by decide⟩, ⟨49, by decide⟩, ⟨62, by decide⟩}
  | ⟨18, _⟩ => {⟨3, by decide⟩, ⟨9, by decide⟩, ⟨13, by decide⟩, ⟨33, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨43, by decide⟩}
  | ⟨19, _⟩ => {⟨3, by decide⟩, ⟨10, by decide⟩, ⟨14, by decide⟩, ⟨34, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨43, by decide⟩}
  | ⟨20, _⟩ => {⟨6, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨32, by decide⟩, ⟨37, by decide⟩, ⟨41, by decide⟩, ⟨44, by decide⟩}
  | ⟨21, _⟩ => {⟨5, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨32, by decide⟩, ⟨38, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩}
  | ⟨22, _⟩ => {⟨1, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩}
  | ⟨23, _⟩ => {⟨2, by decide⟩, ⟨11, by decide⟩, ⟨14, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩}
  | ⟨24, _⟩ => {⟨2, by decide⟩, ⟨3, by decide⟩, ⟨6, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩}
  | ⟨25, _⟩ => {⟨1, by decide⟩, ⟨11, by decide⟩, ⟨13, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩}
  | ⟨26, _⟩ => {⟨4, by decide⟩, ⟨23, by decide⟩, ⟨28, by decide⟩, ⟨39, by decide⟩, ⟨44, by decide⟩, ⟨47, by decide⟩, ⟨52, by decide⟩}
  | ⟨27, _⟩ => {⟨8, by decide⟩, ⟨19, by decide⟩, ⟨28, by decide⟩, ⟨36, by decide⟩, ⟨43, by decide⟩, ⟨48, by decide⟩, ⟨55, by decide⟩}
  | ⟨28, _⟩ => {⟨8, by decide⟩, ⟨20, by decide⟩, ⟨27, by decide⟩, ⟨36, by decide⟩, ⟨43, by decide⟩, ⟨47, by decide⟩, ⟨56, by decide⟩}
  | ⟨29, _⟩ => {⟨12, by decide⟩, ⟨21, by decide⟩, ⟨26, by decide⟩, ⟨32, by decide⟩, ⟨43, by decide⟩, ⟨54, by decide⟩, ⟨57, by decide⟩}
  | ⟨30, _⟩ => {⟨8, by decide⟩, ⟨21, by decide⟩, ⟨30, by decide⟩, ⟨35, by decide⟩, ⟨44, by decide⟩, ⟨49, by decide⟩, ⟨58, by decide⟩}
  | ⟨31, _⟩ => {⟨12, by decide⟩, ⟨22, by decide⟩, ⟨25, by decide⟩, ⟨32, by decide⟩, ⟨43, by decide⟩, ⟨53, by decide⟩, ⟨58, by decide⟩}
  | ⟨32, _⟩ => {⟨8, by decide⟩, ⟨15, by decide⟩, ⟨24, by decide⟩, ⟨36, by decide⟩, ⟨43, by decide⟩, ⟨52, by decide⟩, ⟨59, by decide⟩}
  | ⟨33, _⟩ => {⟨4, by decide⟩, ⟨16, by decide⟩, ⟨19, by decide⟩, ⟨39, by decide⟩, ⟨44, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩}
  | ⟨34, _⟩ => {⟨4, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨55, by decide⟩, ⟨60, by decide⟩}
  | ⟨35, _⟩ => {⟨4, by decide⟩, ⟨15, by decide⟩, ⟨20, by decide⟩, ⟨39, by decide⟩, ⟨44, by decide⟩, ⟨55, by decide⟩, ⟨60, by decide⟩}
  | ⟨36, _⟩ => {⟨3, by decide⟩, ⟨23, by decide⟩, ⟨27, by decide⟩, ⟨32, by decide⟩, ⟨36, by decide⟩, ⟨56, by decide⟩, ⟨60, by decide⟩}
  | ⟨37, _⟩ => {⟨12, by decide⟩, ⟨17, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨43, by decide⟩, ⟨50, by decide⟩, ⟨61, by decide⟩}
  | ⟨38, _⟩ => {⟨8, by decide⟩, ⟨18, by decide⟩, ⟨25, by decide⟩, ⟨35, by decide⟩, ⟨44, by decide⟩, ⟨54, by decide⟩, ⟨61, by decide⟩}
  | ⟨39, _⟩ => {⟨12, by decide⟩, ⟨22, by decide⟩, ⟨25, by decide⟩, ⟨36, by decide⟩, ⟨39, by decide⟩, ⟨49, by decide⟩, ⟨62, by decide⟩}
  | ⟨40, _⟩ => {⟨11, by decide⟩, ⟨22, by decide⟩, ⟨26, by decide⟩, ⟨35, by decide⟩, ⟨39, by decide⟩, ⟨50, by decide⟩, ⟨62, by decide⟩}
  | ⟨41, _⟩ => {⟨8, by decide⟩, ⟨17, by decide⟩, ⟨26, by decide⟩, ⟨35, by decide⟩, ⟨44, by decide⟩, ⟨53, by decide⟩, ⟨62, by decide⟩}
  | ⟨42, _⟩ => {⟨3, by decide⟩, ⟨7, by decide⟩, ⟨11, by decide⟩, ⟨15, by decide⟩, ⟨19, by decide⟩, ⟨23, by decide⟩, ⟨27, by decide⟩, ⟨34, by decide⟩, ⟨38, by decide⟩, ⟨42, by decide⟩, ⟨46, by decide⟩, ⟨50, by decide⟩, ⟨54, by decide⟩, ⟨58, by decide⟩, ⟨62, by decide⟩}
  | ⟨43, _⟩ => {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩}
  | ⟨44, _⟩ => {⟨0, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩}
  | ⟨45, _⟩ => {⟨0, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩}
  | ⟨46, _⟩ => {⟨20, by decide⟩, ⟨31, by decide⟩, ⟨52, by decide⟩}
  | ⟨47, _⟩ => {⟨29, by decide⟩, ⟨40, by decide⟩, ⟨54, by decide⟩}
  | ⟨48, _⟩ => {⟨17, by decide⟩, ⟨40, by decide⟩, ⟨58, by decide⟩}
  | ⟨49, _⟩ => {⟨3, by decide⟩, ⟨10, by decide⟩, ⟨14, by decide⟩}
  | ⟨50, _⟩ => {⟨4, by decide⟩, ⟨16, by decide⟩, ⟨19, by decide⟩}
  | ⟨51, _⟩ => {⟨29, by decide⟩, ⟨35, by decide⟩, ⟨57, by decide⟩}
  | ⟨52, _⟩ => {⟨29, by decide⟩, ⟨43, by decide⟩, ⟨49, by decide⟩}
  | ⟨53, _⟩ => {⟨9, by decide⟩, ⟨21, by decide⟩, ⟨27, by decide⟩}
  | ⟨54, _⟩ => {⟨25, by decide⟩, ⟨46, by decide⟩, ⟨52, by decide⟩}
  | ⟨55, _⟩ => {⟨29, by decide⟩, ⟨33, by decide⟩, ⟨59, by decide⟩}
  | ⟨56, _⟩ => {⟨29, by decide⟩, ⟨34, by decide⟩, ⟨60, by decide⟩}
  | ⟨57, _⟩ => {⟨19, by decide⟩, ⟨41, by decide⟩, ⟨61, by decide⟩}
  | ⟨58, _⟩ => {⟨20, by decide⟩, ⟨42, by decide⟩, ⟨61, by decide⟩}
  | ⟨59, _⟩ => {⟨13, by decide⟩, ⟨21, by decide⟩, ⟨23, by decide⟩}
  | ⟨60, _⟩ => {⟨14, by decide⟩, ⟨21, by decide⟩, ⟨24, by decide⟩}
  | ⟨61, _⟩ => {⟨25, by decide⟩, ⟨42, by decide⟩, ⟨48, by decide⟩}
  | ⟨62, _⟩ => {⟨29, by decide⟩, ⟨37, by decide⟩, ⟨55, by decide⟩}
  | ⟨63, _⟩ => {⟨29, by decide⟩, ⟨38, by decide⟩, ⟨56, by decide⟩}
  | ⟨64, _⟩ => {⟨15, by decide⟩, ⟨45, by decide⟩, ⟨61, by decide⟩}
  | ⟨65, _⟩ => {⟨3, by decide⟩, ⟨7, by decide⟩, ⟨11, by decide⟩, ⟨33, by decide⟩, ⟨37, by decide⟩, ⟨41, by decide⟩, ⟨45, by decide⟩}
  | ⟨66, _⟩ => {⟨8, by decide⟩, ⟨22, by decide⟩, ⟨29, by decide⟩, ⟨35, by decide⟩, ⟨44, by decide⟩, ⟨50, by decide⟩, ⟨57, by decide⟩}
  | ⟨67, _⟩ => {⟨12, by decide⟩, ⟨18, by decide⟩, ⟨29, by decide⟩, ⟨32, by decide⟩, ⟨43, by decide⟩, ⟨49, by decide⟩, ⟨62, by decide⟩}
  | ⟨68, _⟩ => {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩}
  | ⟨69, _⟩ => {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩}
  | ⟨70, _⟩ => {⟨0, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩}
  | ⟨71, _⟩ => {⟨0, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩}
  | ⟨72, _⟩ => {⟨0, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩}
  | ⟨73, _⟩ => {⟨3, by decide⟩, ⟨7, by decide⟩, ⟨11, by decide⟩, ⟨17, by decide⟩, ⟨21, by decide⟩, ⟨25, by decide⟩, ⟨29, by decide⟩, ⟨34, by decide⟩, ⟨38, by decide⟩, ⟨42, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨52, by decide⟩, ⟨56, by decide⟩, ⟨60, by decide⟩}
  | ⟨74, _⟩ => {⟨1, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩}
  | ⟨75, _⟩ => {⟨1, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩}
  | ⟨76, _⟩ => {⟨2, by decide⟩, ⟨3, by decide⟩, ⟨6, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩}
  | ⟨77, _⟩ => {⟨1, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩}
  | ⟨78, _⟩ => {⟨15, by decide⟩, ⟨31, by decide⟩, ⟨47, by decide⟩}
  | ⟨79, _⟩ => {⟨19, by decide⟩, ⟨31, by decide⟩, ⟨51, by decide⟩}
  | ⟨80, _⟩ => {⟨16, by decide⟩, ⟨36, by decide⟩, ⟨51, by decide⟩}
  | ⟨81, _⟩ => {⟨4, by decide⟩, ⟨48, by decide⟩, ⟨51, by decide⟩}
  | ⟨82, _⟩ => {⟨25, by decide⟩, ⟨45, by decide⟩, ⟨51, by decide⟩}
  | ⟨83, _⟩ => {⟨26, by decide⟩, ⟨46, by decide⟩, ⟨51, by decide⟩}
  | ⟨84, _⟩ => {⟨21, by decide⟩, ⟨33, by decide⟩, ⟨51, by decide⟩}
  | ⟨85, _⟩ => {⟨22, by decide⟩, ⟨34, by decide⟩, ⟨51, by decide⟩}
  | ⟨86, _⟩ => {⟨28, by decide⟩, ⟨42, by decide⟩, ⟨53, by decide⟩}
  | ⟨87, _⟩ => {⟨28, by decide⟩, ⟨41, by decide⟩, ⟨54, by decide⟩}
  | ⟨88, _⟩ => {⟨1, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩}
  | ⟨89, _⟩ => {⟨2, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩}
  | ⟨90, _⟩ => {⟨12, by decide⟩, ⟨22, by decide⟩, ⟨25, by decide⟩, ⟨35, by decide⟩, ⟨40, by decide⟩, ⟨50, by decide⟩, ⟨61, by decide⟩}
  | ⟨91, _⟩ => {⟨4, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩, ⟨39, by decide⟩, ⟨44, by decide⟩, ⟨48, by decide⟩, ⟨51, by decide⟩}
  | ⟨92, _⟩ => {⟨3, by decide⟩, ⟨24, by decide⟩, ⟨28, by decide⟩, ⟨32, by decide⟩, ⟨36, by decide⟩, ⟨55, by decide⟩, ⟨59, by decide⟩}
  | ⟨93, _⟩ => {⟨4, by decide⟩, ⟨23, by decide⟩, ⟨28, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩}
  | ⟨94, _⟩ => {⟨8, by decide⟩, ⟨16, by decide⟩, ⟨23, by decide⟩, ⟨36, by decide⟩, ⟨43, by decide⟩, ⟨51, by decide⟩, ⟨60, by decide⟩}
  | ⟨95, _⟩ => {⟨0, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩}
  | ⟨96, _⟩ => {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩}
  | ⟨97, _⟩ => {⟨0, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩}
  | ⟨98, _⟩ => {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩}
  | ⟨99, _⟩ => {⟨0, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩}
  | ⟨100, _⟩ => {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩}
  | _ => ∅

private theorem contain415_0 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨0, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource0 := by
  rw [show activeSet415 ⟨0, by decide⟩ = {⟨2, by decide⟩, ⟨7, by decide⟩, ⟨10, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource0
      step113_415_row0_W_le_source (D.A t) ⟨2, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource0
      step113_415_row0_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource0
      step113_415_row0_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_0 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨0, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨0, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource0 := by
    intro t h0
    exact step113_415_row0_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource0
    step113_415_row0_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨0, by decide⟩)
    hzero
    (contain415_0 D)
    15 step113_415_row0_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨0, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_1 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨1, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource1 := by
  rw [show activeSet415 ⟨1, by decide⟩ = {⟨5, by decide⟩, ⟨7, by decide⟩, ⟨13, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource1
      step113_415_row1_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource1
      step113_415_row1_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource1
      step113_415_row1_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_1 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨1, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨1, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource1 := by
    intro t h0
    exact step113_415_row1_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource1
    step113_415_row1_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨1, by decide⟩)
    hzero
    (contain415_1 D)
    15 step113_415_row1_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨1, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_2 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨2, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource2 := by
  rw [show activeSet415 ⟨2, by decide⟩ = {⟨6, by decide⟩, ⟨7, by decide⟩, ⟨14, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource2
      step113_415_row2_W_le_source (D.A t) ⟨6, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource2
      step113_415_row2_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource2
      step113_415_row2_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_2 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨2, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨2, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource2 := by
    intro t h0
    exact step113_415_row2_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource2
    step113_415_row2_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨2, by decide⟩)
    hzero
    (contain415_2 D)
    15 step113_415_row2_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨2, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_3 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨3, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource3 := by
  rw [show activeSet415 ⟨3, by decide⟩ = {⟨16, by decide⟩, ⟨31, by decide⟩, ⟨48, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource3
      step113_415_row3_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource3
      step113_415_row3_W_le_source (D.A t) ⟨31, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource3
      step113_415_row3_W_le_source (D.A t) ⟨48, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_3 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨3, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨3, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource3 := by
    intro t h0
    exact step113_415_row3_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource3
    step113_415_row3_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨3, by decide⟩)
    hzero
    (contain415_3 D)
    15 step113_415_row3_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨3, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_4 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨4, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource4 := by
  rw [show activeSet415 ⟨4, by decide⟩ = {⟨18, by decide⟩, ⟨40, by decide⟩, ⟨57, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource4
      step113_415_row4_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource4
      step113_415_row4_W_le_source (D.A t) ⟨40, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource4
      step113_415_row4_W_le_source (D.A t) ⟨57, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_4 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨4, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨4, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource4 := by
    intro t h0
    exact step113_415_row4_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource4
    step113_415_row4_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨4, by decide⟩)
    hzero
    (contain415_4 D)
    15 step113_415_row4_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨4, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_5 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨5, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource5 := by
  rw [show activeSet415 ⟨5, by decide⟩ = {⟨19, by decide⟩, ⟨42, by decide⟩, ⟨62, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource5
      step113_415_row5_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource5
      step113_415_row5_W_le_source (D.A t) ⟨42, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource5
      step113_415_row5_W_le_source (D.A t) ⟨62, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_5 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨5, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨5, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource5 := by
    intro t h0
    exact step113_415_row5_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource5
    step113_415_row5_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨5, by decide⟩)
    hzero
    (contain415_5 D)
    15 step113_415_row5_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨5, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_6 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨6, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource6 := by
  rw [show activeSet415 ⟨6, by decide⟩ = {⟨27, by decide⟩, ⟨42, by decide⟩, ⟨54, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource6
      step113_415_row6_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource6
      step113_415_row6_W_le_source (D.A t) ⟨42, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource6
      step113_415_row6_W_le_source (D.A t) ⟨54, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_6 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨6, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨6, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource6 := by
    intro t h0
    exact step113_415_row6_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource6
    step113_415_row6_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨6, by decide⟩)
    hzero
    (contain415_6 D)
    15 step113_415_row6_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨6, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_7 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨7, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource7 := by
  rw [show activeSet415 ⟨7, by decide⟩ = {⟨22, by decide⟩, ⟨41, by decide⟩, ⟨60, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource7
      step113_415_row7_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource7
      step113_415_row7_W_le_source (D.A t) ⟨41, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource7
      step113_415_row7_W_le_source (D.A t) ⟨60, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_7 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨7, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨7, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource7 := by
    intro t h0
    exact step113_415_row7_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource7
    step113_415_row7_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨7, by decide⟩)
    hzero
    (contain415_7 D)
    15 step113_415_row7_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨7, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_8 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨8, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource8 := by
  rw [show activeSet415 ⟨8, by decide⟩ = {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource8
      step113_415_row8_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource8
      step113_415_row8_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource8
      step113_415_row8_W_le_source (D.A t) ⟨2, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource8
      step113_415_row8_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource8
      step113_415_row8_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource8
      step113_415_row8_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource8
      step113_415_row8_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_8 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨8, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨8, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource8 := by
    intro t h0
    exact step113_415_row8_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource8
    step113_415_row8_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨8, by decide⟩)
    hzero
    (contain415_8 D)
    11 step113_415_row8_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(5 : ℕ) : Int) = S_415.occRhs ⟨8, by decide⟩ := by decide
  rw [show (16 : ℕ) - 11 = 5 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_9 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨9, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource9 := by
  rw [show activeSet415 ⟨9, by decide⟩ = {⟨0, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource9
      step113_415_row9_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource9
      step113_415_row9_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource9
      step113_415_row9_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource9
      step113_415_row9_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource9
      step113_415_row9_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource9
      step113_415_row9_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource9
      step113_415_row9_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_9 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨9, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨9, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource9 := by
    intro t h0
    exact step113_415_row9_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource9
    step113_415_row9_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨9, by decide⟩)
    hzero
    (contain415_9 D)
    11 step113_415_row9_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(5 : ℕ) : Int) = S_415.occRhs ⟨9, by decide⟩ := by decide
  rw [show (16 : ℕ) - 11 = 5 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_10 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨10, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource10 := by
  rw [show activeSet415 ⟨10, by decide⟩ = {⟨0, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource10
      step113_415_row10_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource10
      step113_415_row10_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource10
      step113_415_row10_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource10
      step113_415_row10_W_le_source (D.A t) ⟨33, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource10
      step113_415_row10_W_le_source (D.A t) ⟨34, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource10
      step113_415_row10_W_le_source (D.A t) ⟨53, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource10
      step113_415_row10_W_le_source (D.A t) ⟨54, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_10 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨10, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨10, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource10 := by
    intro t h0
    exact step113_415_row10_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource10
    step113_415_row10_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨10, by decide⟩)
    hzero
    (contain415_10 D)
    11 step113_415_row10_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(5 : ℕ) : Int) = S_415.occRhs ⟨10, by decide⟩ := by decide
  rw [show (16 : ℕ) - 11 = 5 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_11 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨11, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource11 := by
  rw [show activeSet415 ⟨11, by decide⟩ = {⟨0, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource11
      step113_415_row11_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource11
      step113_415_row11_W_le_source (D.A t) ⟨15, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource11
      step113_415_row11_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource11
      step113_415_row11_W_le_source (D.A t) ⟨37, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource11
      step113_415_row11_W_le_source (D.A t) ⟨38, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource11
      step113_415_row11_W_le_source (D.A t) ⟨53, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource11
      step113_415_row11_W_le_source (D.A t) ⟨54, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_11 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨11, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨11, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource11 := by
    intro t h0
    exact step113_415_row11_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource11
    step113_415_row11_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨11, by decide⟩)
    hzero
    (contain415_11 D)
    11 step113_415_row11_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(5 : ℕ) : Int) = S_415.occRhs ⟨11, by decide⟩ := by decide
  rw [show (16 : ℕ) - 11 = 5 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_12 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨12, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource12 := by
  rw [show activeSet415 ⟨12, by decide⟩ = {⟨0, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource12
      step113_415_row12_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource12
      step113_415_row12_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource12
      step113_415_row12_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource12
      step113_415_row12_W_le_source (D.A t) ⟨45, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource12
      step113_415_row12_W_le_source (D.A t) ⟨46, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource12
      step113_415_row12_W_le_source (D.A t) ⟨57, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource12
      step113_415_row12_W_le_source (D.A t) ⟨58, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_12 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨12, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨12, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource12 := by
    intro t h0
    exact step113_415_row12_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource12
    step113_415_row12_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨12, by decide⟩)
    hzero
    (contain415_12 D)
    11 step113_415_row12_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(5 : ℕ) : Int) = S_415.occRhs ⟨12, by decide⟩ := by decide
  rw [show (16 : ℕ) - 11 = 5 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_13 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨13, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource13 := by
  rw [show activeSet415 ⟨13, by decide⟩ = {⟨0, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource13
      step113_415_row13_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource13
      step113_415_row13_W_le_source (D.A t) ⟨9, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource13
      step113_415_row13_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource13
      step113_415_row13_W_le_source (D.A t) ⟨53, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource13
      step113_415_row13_W_le_source (D.A t) ⟨54, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource13
      step113_415_row13_W_le_source (D.A t) ⟨59, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource13
      step113_415_row13_W_le_source (D.A t) ⟨60, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_13 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨13, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨13, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource13 := by
    intro t h0
    exact step113_415_row13_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource13
    step113_415_row13_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨13, by decide⟩)
    hzero
    (contain415_13 D)
    11 step113_415_row13_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(5 : ℕ) : Int) = S_415.occRhs ⟨13, by decide⟩ := by decide
  rw [show (16 : ℕ) - 11 = 5 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_14 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨14, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource14 := by
  rw [show activeSet415 ⟨14, by decide⟩ = {⟨0, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource14
      step113_415_row14_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource14
      step113_415_row14_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource14
      step113_415_row14_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource14
      step113_415_row14_W_le_source (D.A t) ⟨47, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource14
      step113_415_row14_W_le_source (D.A t) ⟨48, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource14
      step113_415_row14_W_le_source (D.A t) ⟨61, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource14
      step113_415_row14_W_le_source (D.A t) ⟨62, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_14 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨14, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨14, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource14 := by
    intro t h0
    exact step113_415_row14_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource14
    step113_415_row14_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨14, by decide⟩)
    hzero
    (contain415_14 D)
    11 step113_415_row14_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(5 : ℕ) : Int) = S_415.occRhs ⟨14, by decide⟩ := by decide
  rw [show (16 : ℕ) - 11 = 5 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_15 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨15, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource15 := by
  rw [show activeSet415 ⟨15, by decide⟩ = {⟨3, by decide⟩, ⟨7, by decide⟩, ⟨11, by decide⟩, ⟨34, by decide⟩, ⟨38, by decide⟩, ⟨42, by decide⟩, ⟨46, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource15
      step113_415_row15_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource15
      step113_415_row15_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource15
      step113_415_row15_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource15
      step113_415_row15_W_le_source (D.A t) ⟨34, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource15
      step113_415_row15_W_le_source (D.A t) ⟨38, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource15
      step113_415_row15_W_le_source (D.A t) ⟨42, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource15
      step113_415_row15_W_le_source (D.A t) ⟨46, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_15 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨15, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨15, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource15 := by
    intro t h0
    exact step113_415_row15_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource15
    step113_415_row15_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨15, by decide⟩)
    hzero
    (contain415_15 D)
    15 step113_415_row15_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨15, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_16 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨16, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource16 := by
  rw [show activeSet415 ⟨16, by decide⟩ = {⟨4, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩, ⟨31, by decide⟩, ⟨36, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource16
      step113_415_row16_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource16
      step113_415_row16_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource16
      step113_415_row16_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource16
      step113_415_row16_W_le_source (D.A t) ⟨31, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource16
      step113_415_row16_W_le_source (D.A t) ⟨36, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource16
      step113_415_row16_W_le_source (D.A t) ⟨56, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource16
      step113_415_row16_W_le_source (D.A t) ⟨59, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_16 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨16, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨16, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource16 := by
    intro t h0
    exact step113_415_row16_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource16
    step113_415_row16_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨16, by decide⟩)
    hzero
    (contain415_16 D)
    15 step113_415_row16_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨16, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_17 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨17, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource17 := by
  rw [show activeSet415 ⟨17, by decide⟩ = {⟨12, by decide⟩, ⟨21, by decide⟩, ⟨26, by decide⟩, ⟨35, by decide⟩, ⟨40, by decide⟩, ⟨49, by decide⟩, ⟨62, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource17
      step113_415_row17_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource17
      step113_415_row17_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource17
      step113_415_row17_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource17
      step113_415_row17_W_le_source (D.A t) ⟨35, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource17
      step113_415_row17_W_le_source (D.A t) ⟨40, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource17
      step113_415_row17_W_le_source (D.A t) ⟨49, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource17
      step113_415_row17_W_le_source (D.A t) ⟨62, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_17 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨17, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨17, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource17 := by
    intro t h0
    exact step113_415_row17_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource17
    step113_415_row17_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨17, by decide⟩)
    hzero
    (contain415_17 D)
    15 step113_415_row17_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨17, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_18 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨18, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource18 := by
  rw [show activeSet415 ⟨18, by decide⟩ = {⟨3, by decide⟩, ⟨9, by decide⟩, ⟨13, by decide⟩, ⟨33, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨43, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource18
      step113_415_row18_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource18
      step113_415_row18_W_le_source (D.A t) ⟨9, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource18
      step113_415_row18_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource18
      step113_415_row18_W_le_source (D.A t) ⟨33, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource18
      step113_415_row18_W_le_source (D.A t) ⟨37, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource18
      step113_415_row18_W_le_source (D.A t) ⟨39, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource18
      step113_415_row18_W_le_source (D.A t) ⟨43, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_18 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨18, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨18, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource18 := by
    intro t h0
    exact step113_415_row18_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource18
    step113_415_row18_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨18, by decide⟩)
    hzero
    (contain415_18 D)
    15 step113_415_row18_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨18, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_19 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨19, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource19 := by
  rw [show activeSet415 ⟨19, by decide⟩ = {⟨3, by decide⟩, ⟨10, by decide⟩, ⟨14, by decide⟩, ⟨34, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨43, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource19
      step113_415_row19_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource19
      step113_415_row19_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource19
      step113_415_row19_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource19
      step113_415_row19_W_le_source (D.A t) ⟨34, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource19
      step113_415_row19_W_le_source (D.A t) ⟨38, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource19
      step113_415_row19_W_le_source (D.A t) ⟨39, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource19
      step113_415_row19_W_le_source (D.A t) ⟨43, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_19 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨19, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨19, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource19 := by
    intro t h0
    exact step113_415_row19_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource19
    step113_415_row19_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨19, by decide⟩)
    hzero
    (contain415_19 D)
    15 step113_415_row19_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨19, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_20 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨20, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource20 := by
  rw [show activeSet415 ⟨20, by decide⟩ = {⟨6, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨32, by decide⟩, ⟨37, by decide⟩, ⟨41, by decide⟩, ⟨44, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource20
      step113_415_row20_W_le_source (D.A t) ⟨6, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource20
      step113_415_row20_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource20
      step113_415_row20_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource20
      step113_415_row20_W_le_source (D.A t) ⟨32, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource20
      step113_415_row20_W_le_source (D.A t) ⟨37, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource20
      step113_415_row20_W_le_source (D.A t) ⟨41, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource20
      step113_415_row20_W_le_source (D.A t) ⟨44, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_20 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨20, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨20, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource20 := by
    intro t h0
    exact step113_415_row20_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource20
    step113_415_row20_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨20, by decide⟩)
    hzero
    (contain415_20 D)
    15 step113_415_row20_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨20, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_21 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨21, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource21 := by
  rw [show activeSet415 ⟨21, by decide⟩ = {⟨5, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨32, by decide⟩, ⟨38, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource21
      step113_415_row21_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource21
      step113_415_row21_W_le_source (D.A t) ⟨9, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource21
      step113_415_row21_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource21
      step113_415_row21_W_le_source (D.A t) ⟨32, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource21
      step113_415_row21_W_le_source (D.A t) ⟨38, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource21
      step113_415_row21_W_le_source (D.A t) ⟨42, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource21
      step113_415_row21_W_le_source (D.A t) ⟨44, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_21 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨21, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨21, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource21 := by
    intro t h0
    exact step113_415_row21_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource21
    step113_415_row21_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨21, by decide⟩)
    hzero
    (contain415_21 D)
    15 step113_415_row21_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨21, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_22 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨22, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource22 := by
  rw [show activeSet415 ⟨22, by decide⟩ = {⟨1, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource22
      step113_415_row22_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource22
      step113_415_row22_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource22
      step113_415_row22_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource22
      step113_415_row22_W_le_source (D.A t) ⟨39, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource22
      step113_415_row22_W_le_source (D.A t) ⟨41, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource22
      step113_415_row22_W_le_source (D.A t) ⟨43, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource22
      step113_415_row22_W_le_source (D.A t) ⟨45, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_22 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨22, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨22, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource22 := by
    intro t h0
    exact step113_415_row22_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource22
    step113_415_row22_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨22, by decide⟩)
    hzero
    (contain415_22 D)
    15 step113_415_row22_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨22, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_23 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨23, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource23 := by
  rw [show activeSet415 ⟨23, by decide⟩ = {⟨2, by decide⟩, ⟨11, by decide⟩, ⟨14, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource23
      step113_415_row23_W_le_source (D.A t) ⟨2, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource23
      step113_415_row23_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource23
      step113_415_row23_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource23
      step113_415_row23_W_le_source (D.A t) ⟨32, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource23
      step113_415_row23_W_le_source (D.A t) ⟨33, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource23
      step113_415_row23_W_le_source (D.A t) ⟨44, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource23
      step113_415_row23_W_le_source (D.A t) ⟨45, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_23 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨23, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨23, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource23 := by
    intro t h0
    exact step113_415_row23_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource23
    step113_415_row23_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨23, by decide⟩)
    hzero
    (contain415_23 D)
    15 step113_415_row23_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨23, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_24 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨24, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource24 := by
  rw [show activeSet415 ⟨24, by decide⟩ = {⟨2, by decide⟩, ⟨3, by decide⟩, ⟨6, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource24
      step113_415_row24_W_le_source (D.A t) ⟨2, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource24
      step113_415_row24_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource24
      step113_415_row24_W_le_source (D.A t) ⟨6, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource24
      step113_415_row24_W_le_source (D.A t) ⟨39, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource24
      step113_415_row24_W_le_source (D.A t) ⟨42, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource24
      step113_415_row24_W_le_source (D.A t) ⟨43, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource24
      step113_415_row24_W_le_source (D.A t) ⟨46, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_24 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨24, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨24, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource24 := by
    intro t h0
    exact step113_415_row24_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource24
    step113_415_row24_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨24, by decide⟩)
    hzero
    (contain415_24 D)
    15 step113_415_row24_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨24, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_25 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨25, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource25 := by
  rw [show activeSet415 ⟨25, by decide⟩ = {⟨1, by decide⟩, ⟨11, by decide⟩, ⟨13, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource25
      step113_415_row25_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource25
      step113_415_row25_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource25
      step113_415_row25_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource25
      step113_415_row25_W_le_source (D.A t) ⟨32, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource25
      step113_415_row25_W_le_source (D.A t) ⟨34, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource25
      step113_415_row25_W_le_source (D.A t) ⟨44, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource25
      step113_415_row25_W_le_source (D.A t) ⟨46, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_25 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨25, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨25, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource25 := by
    intro t h0
    exact step113_415_row25_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource25
    step113_415_row25_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨25, by decide⟩)
    hzero
    (contain415_25 D)
    15 step113_415_row25_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨25, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_26 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨26, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource26 := by
  rw [show activeSet415 ⟨26, by decide⟩ = {⟨4, by decide⟩, ⟨23, by decide⟩, ⟨28, by decide⟩, ⟨39, by decide⟩, ⟨44, by decide⟩, ⟨47, by decide⟩, ⟨52, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource26
      step113_415_row26_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource26
      step113_415_row26_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource26
      step113_415_row26_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource26
      step113_415_row26_W_le_source (D.A t) ⟨39, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource26
      step113_415_row26_W_le_source (D.A t) ⟨44, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource26
      step113_415_row26_W_le_source (D.A t) ⟨47, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource26
      step113_415_row26_W_le_source (D.A t) ⟨52, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_26 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨26, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨26, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource26 := by
    intro t h0
    exact step113_415_row26_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource26
    step113_415_row26_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨26, by decide⟩)
    hzero
    (contain415_26 D)
    15 step113_415_row26_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨26, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_27 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨27, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource27 := by
  rw [show activeSet415 ⟨27, by decide⟩ = {⟨8, by decide⟩, ⟨19, by decide⟩, ⟨28, by decide⟩, ⟨36, by decide⟩, ⟨43, by decide⟩, ⟨48, by decide⟩, ⟨55, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource27
      step113_415_row27_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource27
      step113_415_row27_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource27
      step113_415_row27_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource27
      step113_415_row27_W_le_source (D.A t) ⟨36, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource27
      step113_415_row27_W_le_source (D.A t) ⟨43, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource27
      step113_415_row27_W_le_source (D.A t) ⟨48, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource27
      step113_415_row27_W_le_source (D.A t) ⟨55, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_27 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨27, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨27, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource27 := by
    intro t h0
    exact step113_415_row27_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource27
    step113_415_row27_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨27, by decide⟩)
    hzero
    (contain415_27 D)
    15 step113_415_row27_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨27, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_28 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨28, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource28 := by
  rw [show activeSet415 ⟨28, by decide⟩ = {⟨8, by decide⟩, ⟨20, by decide⟩, ⟨27, by decide⟩, ⟨36, by decide⟩, ⟨43, by decide⟩, ⟨47, by decide⟩, ⟨56, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource28
      step113_415_row28_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource28
      step113_415_row28_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource28
      step113_415_row28_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource28
      step113_415_row28_W_le_source (D.A t) ⟨36, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource28
      step113_415_row28_W_le_source (D.A t) ⟨43, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource28
      step113_415_row28_W_le_source (D.A t) ⟨47, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource28
      step113_415_row28_W_le_source (D.A t) ⟨56, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_28 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨28, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨28, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource28 := by
    intro t h0
    exact step113_415_row28_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource28
    step113_415_row28_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨28, by decide⟩)
    hzero
    (contain415_28 D)
    15 step113_415_row28_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨28, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_29 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨29, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource29 := by
  rw [show activeSet415 ⟨29, by decide⟩ = {⟨12, by decide⟩, ⟨21, by decide⟩, ⟨26, by decide⟩, ⟨32, by decide⟩, ⟨43, by decide⟩, ⟨54, by decide⟩, ⟨57, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource29
      step113_415_row29_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource29
      step113_415_row29_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource29
      step113_415_row29_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource29
      step113_415_row29_W_le_source (D.A t) ⟨32, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource29
      step113_415_row29_W_le_source (D.A t) ⟨43, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource29
      step113_415_row29_W_le_source (D.A t) ⟨54, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource29
      step113_415_row29_W_le_source (D.A t) ⟨57, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_29 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨29, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨29, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource29 := by
    intro t h0
    exact step113_415_row29_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource29
    step113_415_row29_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨29, by decide⟩)
    hzero
    (contain415_29 D)
    15 step113_415_row29_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨29, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_30 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨30, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource30 := by
  rw [show activeSet415 ⟨30, by decide⟩ = {⟨8, by decide⟩, ⟨21, by decide⟩, ⟨30, by decide⟩, ⟨35, by decide⟩, ⟨44, by decide⟩, ⟨49, by decide⟩, ⟨58, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource30
      step113_415_row30_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource30
      step113_415_row30_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource30
      step113_415_row30_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource30
      step113_415_row30_W_le_source (D.A t) ⟨35, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource30
      step113_415_row30_W_le_source (D.A t) ⟨44, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource30
      step113_415_row30_W_le_source (D.A t) ⟨49, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource30
      step113_415_row30_W_le_source (D.A t) ⟨58, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_30 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨30, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨30, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource30 := by
    intro t h0
    exact step113_415_row30_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource30
    step113_415_row30_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨30, by decide⟩)
    hzero
    (contain415_30 D)
    15 step113_415_row30_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨30, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_31 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨31, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource31 := by
  rw [show activeSet415 ⟨31, by decide⟩ = {⟨12, by decide⟩, ⟨22, by decide⟩, ⟨25, by decide⟩, ⟨32, by decide⟩, ⟨43, by decide⟩, ⟨53, by decide⟩, ⟨58, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource31
      step113_415_row31_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource31
      step113_415_row31_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource31
      step113_415_row31_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource31
      step113_415_row31_W_le_source (D.A t) ⟨32, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource31
      step113_415_row31_W_le_source (D.A t) ⟨43, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource31
      step113_415_row31_W_le_source (D.A t) ⟨53, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource31
      step113_415_row31_W_le_source (D.A t) ⟨58, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_31 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨31, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨31, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource31 := by
    intro t h0
    exact step113_415_row31_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource31
    step113_415_row31_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨31, by decide⟩)
    hzero
    (contain415_31 D)
    15 step113_415_row31_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨31, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_32 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨32, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource32 := by
  rw [show activeSet415 ⟨32, by decide⟩ = {⟨8, by decide⟩, ⟨15, by decide⟩, ⟨24, by decide⟩, ⟨36, by decide⟩, ⟨43, by decide⟩, ⟨52, by decide⟩, ⟨59, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource32
      step113_415_row32_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource32
      step113_415_row32_W_le_source (D.A t) ⟨15, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource32
      step113_415_row32_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource32
      step113_415_row32_W_le_source (D.A t) ⟨36, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource32
      step113_415_row32_W_le_source (D.A t) ⟨43, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource32
      step113_415_row32_W_le_source (D.A t) ⟨52, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource32
      step113_415_row32_W_le_source (D.A t) ⟨59, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_32 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨32, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨32, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource32 := by
    intro t h0
    exact step113_415_row32_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource32
    step113_415_row32_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨32, by decide⟩)
    hzero
    (contain415_32 D)
    15 step113_415_row32_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨32, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_33 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨33, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource33 := by
  rw [show activeSet415 ⟨33, by decide⟩ = {⟨4, by decide⟩, ⟨16, by decide⟩, ⟨19, by decide⟩, ⟨39, by decide⟩, ⟨44, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource33
      step113_415_row33_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource33
      step113_415_row33_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource33
      step113_415_row33_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource33
      step113_415_row33_W_le_source (D.A t) ⟨39, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource33
      step113_415_row33_W_le_source (D.A t) ⟨44, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource33
      step113_415_row33_W_le_source (D.A t) ⟨56, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource33
      step113_415_row33_W_le_source (D.A t) ⟨59, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_33 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨33, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨33, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource33 := by
    intro t h0
    exact step113_415_row33_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource33
    step113_415_row33_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨33, by decide⟩)
    hzero
    (contain415_33 D)
    15 step113_415_row33_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨33, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_34 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨34, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource34 := by
  rw [show activeSet415 ⟨34, by decide⟩ = {⟨4, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨55, by decide⟩, ⟨60, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource34
      step113_415_row34_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource34
      step113_415_row34_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource34
      step113_415_row34_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource34
      step113_415_row34_W_le_source (D.A t) ⟨32, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource34
      step113_415_row34_W_le_source (D.A t) ⟨35, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource34
      step113_415_row34_W_le_source (D.A t) ⟨55, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource34
      step113_415_row34_W_le_source (D.A t) ⟨60, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_34 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨34, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨34, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource34 := by
    intro t h0
    exact step113_415_row34_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource34
    step113_415_row34_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨34, by decide⟩)
    hzero
    (contain415_34 D)
    15 step113_415_row34_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨34, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_35 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨35, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource35 := by
  rw [show activeSet415 ⟨35, by decide⟩ = {⟨4, by decide⟩, ⟨15, by decide⟩, ⟨20, by decide⟩, ⟨39, by decide⟩, ⟨44, by decide⟩, ⟨55, by decide⟩, ⟨60, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource35
      step113_415_row35_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource35
      step113_415_row35_W_le_source (D.A t) ⟨15, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource35
      step113_415_row35_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource35
      step113_415_row35_W_le_source (D.A t) ⟨39, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource35
      step113_415_row35_W_le_source (D.A t) ⟨44, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource35
      step113_415_row35_W_le_source (D.A t) ⟨55, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource35
      step113_415_row35_W_le_source (D.A t) ⟨60, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_35 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨35, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨35, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource35 := by
    intro t h0
    exact step113_415_row35_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource35
    step113_415_row35_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨35, by decide⟩)
    hzero
    (contain415_35 D)
    15 step113_415_row35_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨35, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_36 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨36, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource36 := by
  rw [show activeSet415 ⟨36, by decide⟩ = {⟨3, by decide⟩, ⟨23, by decide⟩, ⟨27, by decide⟩, ⟨32, by decide⟩, ⟨36, by decide⟩, ⟨56, by decide⟩, ⟨60, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource36
      step113_415_row36_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource36
      step113_415_row36_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource36
      step113_415_row36_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource36
      step113_415_row36_W_le_source (D.A t) ⟨32, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource36
      step113_415_row36_W_le_source (D.A t) ⟨36, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource36
      step113_415_row36_W_le_source (D.A t) ⟨56, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource36
      step113_415_row36_W_le_source (D.A t) ⟨60, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_36 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨36, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨36, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource36 := by
    intro t h0
    exact step113_415_row36_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource36
    step113_415_row36_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨36, by decide⟩)
    hzero
    (contain415_36 D)
    15 step113_415_row36_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨36, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_37 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨37, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource37 := by
  rw [show activeSet415 ⟨37, by decide⟩ = {⟨12, by decide⟩, ⟨17, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨43, by decide⟩, ⟨50, by decide⟩, ⟨61, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource37
      step113_415_row37_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource37
      step113_415_row37_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource37
      step113_415_row37_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource37
      step113_415_row37_W_le_source (D.A t) ⟨32, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource37
      step113_415_row37_W_le_source (D.A t) ⟨43, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource37
      step113_415_row37_W_le_source (D.A t) ⟨50, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource37
      step113_415_row37_W_le_source (D.A t) ⟨61, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_37 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨37, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨37, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource37 := by
    intro t h0
    exact step113_415_row37_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource37
    step113_415_row37_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨37, by decide⟩)
    hzero
    (contain415_37 D)
    15 step113_415_row37_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨37, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_38 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨38, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource38 := by
  rw [show activeSet415 ⟨38, by decide⟩ = {⟨8, by decide⟩, ⟨18, by decide⟩, ⟨25, by decide⟩, ⟨35, by decide⟩, ⟨44, by decide⟩, ⟨54, by decide⟩, ⟨61, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource38
      step113_415_row38_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource38
      step113_415_row38_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource38
      step113_415_row38_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource38
      step113_415_row38_W_le_source (D.A t) ⟨35, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource38
      step113_415_row38_W_le_source (D.A t) ⟨44, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource38
      step113_415_row38_W_le_source (D.A t) ⟨54, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource38
      step113_415_row38_W_le_source (D.A t) ⟨61, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_38 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨38, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨38, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource38 := by
    intro t h0
    exact step113_415_row38_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource38
    step113_415_row38_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨38, by decide⟩)
    hzero
    (contain415_38 D)
    15 step113_415_row38_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨38, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_39 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨39, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource39 := by
  rw [show activeSet415 ⟨39, by decide⟩ = {⟨12, by decide⟩, ⟨22, by decide⟩, ⟨25, by decide⟩, ⟨36, by decide⟩, ⟨39, by decide⟩, ⟨49, by decide⟩, ⟨62, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource39
      step113_415_row39_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource39
      step113_415_row39_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource39
      step113_415_row39_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource39
      step113_415_row39_W_le_source (D.A t) ⟨36, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource39
      step113_415_row39_W_le_source (D.A t) ⟨39, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource39
      step113_415_row39_W_le_source (D.A t) ⟨49, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource39
      step113_415_row39_W_le_source (D.A t) ⟨62, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_39 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨39, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨39, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource39 := by
    intro t h0
    exact step113_415_row39_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource39
    step113_415_row39_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨39, by decide⟩)
    hzero
    (contain415_39 D)
    15 step113_415_row39_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨39, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_40 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨40, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource40 := by
  rw [show activeSet415 ⟨40, by decide⟩ = {⟨11, by decide⟩, ⟨22, by decide⟩, ⟨26, by decide⟩, ⟨35, by decide⟩, ⟨39, by decide⟩, ⟨50, by decide⟩, ⟨62, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource40
      step113_415_row40_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource40
      step113_415_row40_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource40
      step113_415_row40_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource40
      step113_415_row40_W_le_source (D.A t) ⟨35, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource40
      step113_415_row40_W_le_source (D.A t) ⟨39, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource40
      step113_415_row40_W_le_source (D.A t) ⟨50, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource40
      step113_415_row40_W_le_source (D.A t) ⟨62, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_40 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨40, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨40, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource40 := by
    intro t h0
    exact step113_415_row40_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource40
    step113_415_row40_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨40, by decide⟩)
    hzero
    (contain415_40 D)
    15 step113_415_row40_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨40, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_41 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨41, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource41 := by
  rw [show activeSet415 ⟨41, by decide⟩ = {⟨8, by decide⟩, ⟨17, by decide⟩, ⟨26, by decide⟩, ⟨35, by decide⟩, ⟨44, by decide⟩, ⟨53, by decide⟩, ⟨62, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource41
      step113_415_row41_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource41
      step113_415_row41_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource41
      step113_415_row41_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource41
      step113_415_row41_W_le_source (D.A t) ⟨35, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource41
      step113_415_row41_W_le_source (D.A t) ⟨44, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource41
      step113_415_row41_W_le_source (D.A t) ⟨53, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource41
      step113_415_row41_W_le_source (D.A t) ⟨62, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_41 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨41, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨41, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource41 := by
    intro t h0
    exact step113_415_row41_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource41
    step113_415_row41_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨41, by decide⟩)
    hzero
    (contain415_41 D)
    15 step113_415_row41_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨41, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_42 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨42, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource42 := by
  rw [show activeSet415 ⟨42, by decide⟩ = {⟨3, by decide⟩, ⟨7, by decide⟩, ⟨11, by decide⟩, ⟨15, by decide⟩, ⟨19, by decide⟩, ⟨23, by decide⟩, ⟨27, by decide⟩, ⟨34, by decide⟩, ⟨38, by decide⟩, ⟨42, by decide⟩, ⟨46, by decide⟩, ⟨50, by decide⟩, ⟨54, by decide⟩, ⟨58, by decide⟩, ⟨62, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource42
      step113_415_row42_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource42
      step113_415_row42_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource42
      step113_415_row42_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource42
      step113_415_row42_W_le_source (D.A t) ⟨15, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource42
      step113_415_row42_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource42
      step113_415_row42_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource42
      step113_415_row42_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource42
      step113_415_row42_W_le_source (D.A t) ⟨34, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource42
      step113_415_row42_W_le_source (D.A t) ⟨38, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource42
      step113_415_row42_W_le_source (D.A t) ⟨42, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource42
      step113_415_row42_W_le_source (D.A t) ⟨46, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource42
      step113_415_row42_W_le_source (D.A t) ⟨50, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource42
      step113_415_row42_W_le_source (D.A t) ⟨54, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource42
      step113_415_row42_W_le_source (D.A t) ⟨58, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource42
      step113_415_row42_W_le_source (D.A t) ⟨62, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_42 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨42, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨42, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource42 := by
    intro t h0
    exact step113_415_row42_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource42
    step113_415_row42_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨42, by decide⟩)
    hzero
    (contain415_42 D)
    12 step113_415_row42_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(4 : ℕ) : Int) = S_415.occRhs ⟨42, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_43 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨43, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource43 := by
  rw [show activeSet415 ⟨43, by decide⟩ = {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource43
      step113_415_row43_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource43
      step113_415_row43_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource43
      step113_415_row43_W_le_source (D.A t) ⟨2, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource43
      step113_415_row43_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource43
      step113_415_row43_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource43
      step113_415_row43_W_le_source (D.A t) ⟨9, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource43
      step113_415_row43_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource43
      step113_415_row43_W_le_source (D.A t) ⟨15, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource43
      step113_415_row43_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource43
      step113_415_row43_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource43
      step113_415_row43_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource43
      step113_415_row43_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource43
      step113_415_row43_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource43
      step113_415_row43_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource43
      step113_415_row43_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource43
      step113_415_row43_W_le_source (D.A t) ⟨31, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource43
      step113_415_row43_W_le_source (D.A t) ⟨32, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource43
      step113_415_row43_W_le_source (D.A t) ⟨33, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource43
      step113_415_row43_W_le_source (D.A t) ⟨34, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource43
      step113_415_row43_W_le_source (D.A t) ⟨39, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource43
      step113_415_row43_W_le_source (D.A t) ⟨40, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource43
      step113_415_row43_W_le_source (D.A t) ⟨41, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource43
      step113_415_row43_W_le_source (D.A t) ⟨42, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource43
      step113_415_row43_W_le_source (D.A t) ⟨47, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource43
      step113_415_row43_W_le_source (D.A t) ⟨48, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource43
      step113_415_row43_W_le_source (D.A t) ⟨49, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource43
      step113_415_row43_W_le_source (D.A t) ⟨50, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource43
      step113_415_row43_W_le_source (D.A t) ⟨55, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource43
      step113_415_row43_W_le_source (D.A t) ⟨56, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource43
      step113_415_row43_W_le_source (D.A t) ⟨57, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource43
      step113_415_row43_W_le_source (D.A t) ⟨58, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_43 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨43, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨43, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource43 := by
    intro t h0
    exact step113_415_row43_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource43
    step113_415_row43_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨43, by decide⟩)
    hzero
    (contain415_43 D)
    6 step113_415_row43_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(10 : ℕ) : Int) = S_415.occRhs ⟨43, by decide⟩ := by decide
  rw [show (16 : ℕ) - 6 = 10 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_44 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨44, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource44 := by
  rw [show activeSet415 ⟨44, by decide⟩ = {⟨0, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource44
      step113_415_row44_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource44
      step113_415_row44_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource44
      step113_415_row44_W_le_source (D.A t) ⟨6, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource44
      step113_415_row44_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource44
      step113_415_row44_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource44
      step113_415_row44_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource44
      step113_415_row44_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource44
      step113_415_row44_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource44
      step113_415_row44_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource44
      step113_415_row44_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource44
      step113_415_row44_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource44
      step113_415_row44_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource44
      step113_415_row44_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource44
      step113_415_row44_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource44
      step113_415_row44_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource44
      step113_415_row44_W_le_source (D.A t) ⟨31, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource44
      step113_415_row44_W_le_source (D.A t) ⟨32, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource44
      step113_415_row44_W_le_source (D.A t) ⟨37, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource44
      step113_415_row44_W_le_source (D.A t) ⟨38, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource44
      step113_415_row44_W_le_source (D.A t) ⟨39, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource44
      step113_415_row44_W_le_source (D.A t) ⟨40, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource44
      step113_415_row44_W_le_source (D.A t) ⟨45, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource44
      step113_415_row44_W_le_source (D.A t) ⟨46, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource44
      step113_415_row44_W_le_source (D.A t) ⟨49, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource44
      step113_415_row44_W_le_source (D.A t) ⟨50, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource44
      step113_415_row44_W_le_source (D.A t) ⟨51, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource44
      step113_415_row44_W_le_source (D.A t) ⟨52, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource44
      step113_415_row44_W_le_source (D.A t) ⟨57, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource44
      step113_415_row44_W_le_source (D.A t) ⟨58, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource44
      step113_415_row44_W_le_source (D.A t) ⟨59, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource44
      step113_415_row44_W_le_source (D.A t) ⟨60, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_44 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨44, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨44, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource44 := by
    intro t h0
    exact step113_415_row44_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource44
    step113_415_row44_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨44, by decide⟩)
    hzero
    (contain415_44 D)
    6 step113_415_row44_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(10 : ℕ) : Int) = S_415.occRhs ⟨44, by decide⟩ := by decide
  rw [show (16 : ℕ) - 6 = 10 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_45 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨45, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource45 := by
  rw [show activeSet415 ⟨45, by decide⟩ = {⟨0, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource45
      step113_415_row45_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource45
      step113_415_row45_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource45
      step113_415_row45_W_le_source (D.A t) ⟨6, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource45
      step113_415_row45_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource45
      step113_415_row45_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource45
      step113_415_row45_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource45
      step113_415_row45_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource45
      step113_415_row45_W_le_source (D.A t) ⟨15, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource45
      step113_415_row45_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource45
      step113_415_row45_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource45
      step113_415_row45_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource45
      step113_415_row45_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource45
      step113_415_row45_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource45
      step113_415_row45_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource45
      step113_415_row45_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource45
      step113_415_row45_W_le_source (D.A t) ⟨31, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource45
      step113_415_row45_W_le_source (D.A t) ⟨32, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource45
      step113_415_row45_W_le_source (D.A t) ⟨37, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource45
      step113_415_row45_W_le_source (D.A t) ⟨38, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource45
      step113_415_row45_W_le_source (D.A t) ⟨39, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource45
      step113_415_row45_W_le_source (D.A t) ⟨40, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource45
      step113_415_row45_W_le_source (D.A t) ⟨45, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource45
      step113_415_row45_W_le_source (D.A t) ⟨46, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource45
      step113_415_row45_W_le_source (D.A t) ⟨47, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource45
      step113_415_row45_W_le_source (D.A t) ⟨48, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource45
      step113_415_row45_W_le_source (D.A t) ⟨53, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource45
      step113_415_row45_W_le_source (D.A t) ⟨54, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource45
      step113_415_row45_W_le_source (D.A t) ⟨55, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource45
      step113_415_row45_W_le_source (D.A t) ⟨56, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource45
      step113_415_row45_W_le_source (D.A t) ⟨61, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource45
      step113_415_row45_W_le_source (D.A t) ⟨62, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_45 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨45, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨45, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource45 := by
    intro t h0
    exact step113_415_row45_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource45
    step113_415_row45_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨45, by decide⟩)
    hzero
    (contain415_45 D)
    6 step113_415_row45_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(10 : ℕ) : Int) = S_415.occRhs ⟨45, by decide⟩ := by decide
  rw [show (16 : ℕ) - 6 = 10 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_46 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨46, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource46 := by
  rw [show activeSet415 ⟨46, by decide⟩ = {⟨20, by decide⟩, ⟨31, by decide⟩, ⟨52, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource46
      step113_415_row46_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource46
      step113_415_row46_W_le_source (D.A t) ⟨31, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource46
      step113_415_row46_W_le_source (D.A t) ⟨52, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_46 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨46, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨46, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource46 := by
    intro t h0
    exact step113_415_row46_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource46
    step113_415_row46_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨46, by decide⟩)
    hzero
    (contain415_46 D)
    15 step113_415_row46_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨46, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_47 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨47, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource47 := by
  rw [show activeSet415 ⟨47, by decide⟩ = {⟨29, by decide⟩, ⟨40, by decide⟩, ⟨54, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource47
      step113_415_row47_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource47
      step113_415_row47_W_le_source (D.A t) ⟨40, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource47
      step113_415_row47_W_le_source (D.A t) ⟨54, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_47 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨47, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨47, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource47 := by
    intro t h0
    exact step113_415_row47_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource47
    step113_415_row47_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨47, by decide⟩)
    hzero
    (contain415_47 D)
    15 step113_415_row47_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨47, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_48 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨48, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource48 := by
  rw [show activeSet415 ⟨48, by decide⟩ = {⟨17, by decide⟩, ⟨40, by decide⟩, ⟨58, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource48
      step113_415_row48_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource48
      step113_415_row48_W_le_source (D.A t) ⟨40, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource48
      step113_415_row48_W_le_source (D.A t) ⟨58, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_48 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨48, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨48, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource48 := by
    intro t h0
    exact step113_415_row48_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource48
    step113_415_row48_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨48, by decide⟩)
    hzero
    (contain415_48 D)
    15 step113_415_row48_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨48, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_49 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨49, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource49 := by
  rw [show activeSet415 ⟨49, by decide⟩ = {⟨3, by decide⟩, ⟨10, by decide⟩, ⟨14, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource49
      step113_415_row49_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource49
      step113_415_row49_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource49
      step113_415_row49_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_49 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨49, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨49, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource49 := by
    intro t h0
    exact step113_415_row49_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource49
    step113_415_row49_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨49, by decide⟩)
    hzero
    (contain415_49 D)
    15 step113_415_row49_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨49, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_50 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨50, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource50 := by
  rw [show activeSet415 ⟨50, by decide⟩ = {⟨4, by decide⟩, ⟨16, by decide⟩, ⟨19, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource50
      step113_415_row50_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource50
      step113_415_row50_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource50
      step113_415_row50_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_50 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨50, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨50, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource50 := by
    intro t h0
    exact step113_415_row50_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource50
    step113_415_row50_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨50, by decide⟩)
    hzero
    (contain415_50 D)
    15 step113_415_row50_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨50, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_51 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨51, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource51 := by
  rw [show activeSet415 ⟨51, by decide⟩ = {⟨29, by decide⟩, ⟨35, by decide⟩, ⟨57, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource51
      step113_415_row51_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource51
      step113_415_row51_W_le_source (D.A t) ⟨35, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource51
      step113_415_row51_W_le_source (D.A t) ⟨57, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_51 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨51, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨51, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource51 := by
    intro t h0
    exact step113_415_row51_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource51
    step113_415_row51_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨51, by decide⟩)
    hzero
    (contain415_51 D)
    15 step113_415_row51_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨51, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_52 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨52, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource52 := by
  rw [show activeSet415 ⟨52, by decide⟩ = {⟨29, by decide⟩, ⟨43, by decide⟩, ⟨49, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource52
      step113_415_row52_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource52
      step113_415_row52_W_le_source (D.A t) ⟨43, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource52
      step113_415_row52_W_le_source (D.A t) ⟨49, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_52 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨52, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨52, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource52 := by
    intro t h0
    exact step113_415_row52_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource52
    step113_415_row52_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨52, by decide⟩)
    hzero
    (contain415_52 D)
    15 step113_415_row52_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨52, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_53 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨53, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource53 := by
  rw [show activeSet415 ⟨53, by decide⟩ = {⟨9, by decide⟩, ⟨21, by decide⟩, ⟨27, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource53
      step113_415_row53_W_le_source (D.A t) ⟨9, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource53
      step113_415_row53_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource53
      step113_415_row53_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_53 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨53, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨53, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource53 := by
    intro t h0
    exact step113_415_row53_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource53
    step113_415_row53_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨53, by decide⟩)
    hzero
    (contain415_53 D)
    15 step113_415_row53_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨53, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_54 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨54, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource54 := by
  rw [show activeSet415 ⟨54, by decide⟩ = {⟨25, by decide⟩, ⟨46, by decide⟩, ⟨52, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource54
      step113_415_row54_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource54
      step113_415_row54_W_le_source (D.A t) ⟨46, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource54
      step113_415_row54_W_le_source (D.A t) ⟨52, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_54 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨54, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨54, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource54 := by
    intro t h0
    exact step113_415_row54_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource54
    step113_415_row54_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨54, by decide⟩)
    hzero
    (contain415_54 D)
    15 step113_415_row54_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨54, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_55 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨55, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource55 := by
  rw [show activeSet415 ⟨55, by decide⟩ = {⟨29, by decide⟩, ⟨33, by decide⟩, ⟨59, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource55
      step113_415_row55_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource55
      step113_415_row55_W_le_source (D.A t) ⟨33, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource55
      step113_415_row55_W_le_source (D.A t) ⟨59, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_55 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨55, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨55, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource55 := by
    intro t h0
    exact step113_415_row55_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource55
    step113_415_row55_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨55, by decide⟩)
    hzero
    (contain415_55 D)
    15 step113_415_row55_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨55, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_56 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨56, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource56 := by
  rw [show activeSet415 ⟨56, by decide⟩ = {⟨29, by decide⟩, ⟨34, by decide⟩, ⟨60, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource56
      step113_415_row56_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource56
      step113_415_row56_W_le_source (D.A t) ⟨34, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource56
      step113_415_row56_W_le_source (D.A t) ⟨60, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_56 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨56, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨56, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource56 := by
    intro t h0
    exact step113_415_row56_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource56
    step113_415_row56_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨56, by decide⟩)
    hzero
    (contain415_56 D)
    15 step113_415_row56_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨56, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_57 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨57, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource57 := by
  rw [show activeSet415 ⟨57, by decide⟩ = {⟨19, by decide⟩, ⟨41, by decide⟩, ⟨61, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource57
      step113_415_row57_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource57
      step113_415_row57_W_le_source (D.A t) ⟨41, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource57
      step113_415_row57_W_le_source (D.A t) ⟨61, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_57 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨57, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨57, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource57 := by
    intro t h0
    exact step113_415_row57_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource57
    step113_415_row57_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨57, by decide⟩)
    hzero
    (contain415_57 D)
    15 step113_415_row57_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨57, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_58 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨58, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource58 := by
  rw [show activeSet415 ⟨58, by decide⟩ = {⟨20, by decide⟩, ⟨42, by decide⟩, ⟨61, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource58
      step113_415_row58_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource58
      step113_415_row58_W_le_source (D.A t) ⟨42, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource58
      step113_415_row58_W_le_source (D.A t) ⟨61, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_58 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨58, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨58, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource58 := by
    intro t h0
    exact step113_415_row58_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource58
    step113_415_row58_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨58, by decide⟩)
    hzero
    (contain415_58 D)
    15 step113_415_row58_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨58, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_59 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨59, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource59 := by
  rw [show activeSet415 ⟨59, by decide⟩ = {⟨13, by decide⟩, ⟨21, by decide⟩, ⟨23, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource59
      step113_415_row59_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource59
      step113_415_row59_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource59
      step113_415_row59_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_59 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨59, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨59, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource59 := by
    intro t h0
    exact step113_415_row59_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource59
    step113_415_row59_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨59, by decide⟩)
    hzero
    (contain415_59 D)
    15 step113_415_row59_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨59, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_60 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨60, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource60 := by
  rw [show activeSet415 ⟨60, by decide⟩ = {⟨14, by decide⟩, ⟨21, by decide⟩, ⟨24, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource60
      step113_415_row60_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource60
      step113_415_row60_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource60
      step113_415_row60_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_60 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨60, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨60, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource60 := by
    intro t h0
    exact step113_415_row60_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource60
    step113_415_row60_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨60, by decide⟩)
    hzero
    (contain415_60 D)
    15 step113_415_row60_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨60, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_61 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨61, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource61 := by
  rw [show activeSet415 ⟨61, by decide⟩ = {⟨25, by decide⟩, ⟨42, by decide⟩, ⟨48, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource61
      step113_415_row61_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource61
      step113_415_row61_W_le_source (D.A t) ⟨42, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource61
      step113_415_row61_W_le_source (D.A t) ⟨48, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_61 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨61, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨61, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource61 := by
    intro t h0
    exact step113_415_row61_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource61
    step113_415_row61_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨61, by decide⟩)
    hzero
    (contain415_61 D)
    15 step113_415_row61_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨61, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_62 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨62, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource62 := by
  rw [show activeSet415 ⟨62, by decide⟩ = {⟨29, by decide⟩, ⟨37, by decide⟩, ⟨55, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource62
      step113_415_row62_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource62
      step113_415_row62_W_le_source (D.A t) ⟨37, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource62
      step113_415_row62_W_le_source (D.A t) ⟨55, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_62 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨62, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨62, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource62 := by
    intro t h0
    exact step113_415_row62_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource62
    step113_415_row62_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨62, by decide⟩)
    hzero
    (contain415_62 D)
    15 step113_415_row62_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨62, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_63 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨63, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource63 := by
  rw [show activeSet415 ⟨63, by decide⟩ = {⟨29, by decide⟩, ⟨38, by decide⟩, ⟨56, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource63
      step113_415_row63_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource63
      step113_415_row63_W_le_source (D.A t) ⟨38, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource63
      step113_415_row63_W_le_source (D.A t) ⟨56, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_63 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨63, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨63, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource63 := by
    intro t h0
    exact step113_415_row63_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource63
    step113_415_row63_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨63, by decide⟩)
    hzero
    (contain415_63 D)
    15 step113_415_row63_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨63, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_64 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨64, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource64 := by
  rw [show activeSet415 ⟨64, by decide⟩ = {⟨15, by decide⟩, ⟨45, by decide⟩, ⟨61, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource64
      step113_415_row64_W_le_source (D.A t) ⟨15, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource64
      step113_415_row64_W_le_source (D.A t) ⟨45, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource64
      step113_415_row64_W_le_source (D.A t) ⟨61, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_64 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨64, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨64, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource64 := by
    intro t h0
    exact step113_415_row64_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource64
    step113_415_row64_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨64, by decide⟩)
    hzero
    (contain415_64 D)
    15 step113_415_row64_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨64, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_65 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨65, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource65 := by
  rw [show activeSet415 ⟨65, by decide⟩ = {⟨3, by decide⟩, ⟨7, by decide⟩, ⟨11, by decide⟩, ⟨33, by decide⟩, ⟨37, by decide⟩, ⟨41, by decide⟩, ⟨45, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource65
      step113_415_row65_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource65
      step113_415_row65_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource65
      step113_415_row65_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource65
      step113_415_row65_W_le_source (D.A t) ⟨33, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource65
      step113_415_row65_W_le_source (D.A t) ⟨37, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource65
      step113_415_row65_W_le_source (D.A t) ⟨41, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource65
      step113_415_row65_W_le_source (D.A t) ⟨45, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_65 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨65, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨65, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource65 := by
    intro t h0
    exact step113_415_row65_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource65
    step113_415_row65_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨65, by decide⟩)
    hzero
    (contain415_65 D)
    15 step113_415_row65_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨65, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_66 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨66, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource66 := by
  rw [show activeSet415 ⟨66, by decide⟩ = {⟨8, by decide⟩, ⟨22, by decide⟩, ⟨29, by decide⟩, ⟨35, by decide⟩, ⟨44, by decide⟩, ⟨50, by decide⟩, ⟨57, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource66
      step113_415_row66_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource66
      step113_415_row66_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource66
      step113_415_row66_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource66
      step113_415_row66_W_le_source (D.A t) ⟨35, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource66
      step113_415_row66_W_le_source (D.A t) ⟨44, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource66
      step113_415_row66_W_le_source (D.A t) ⟨50, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource66
      step113_415_row66_W_le_source (D.A t) ⟨57, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_66 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨66, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨66, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource66 := by
    intro t h0
    exact step113_415_row66_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource66
    step113_415_row66_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨66, by decide⟩)
    hzero
    (contain415_66 D)
    15 step113_415_row66_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨66, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_67 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨67, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource67 := by
  rw [show activeSet415 ⟨67, by decide⟩ = {⟨12, by decide⟩, ⟨18, by decide⟩, ⟨29, by decide⟩, ⟨32, by decide⟩, ⟨43, by decide⟩, ⟨49, by decide⟩, ⟨62, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource67
      step113_415_row67_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource67
      step113_415_row67_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource67
      step113_415_row67_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource67
      step113_415_row67_W_le_source (D.A t) ⟨32, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource67
      step113_415_row67_W_le_source (D.A t) ⟨43, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource67
      step113_415_row67_W_le_source (D.A t) ⟨49, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource67
      step113_415_row67_W_le_source (D.A t) ⟨62, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_67 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨67, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨67, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource67 := by
    intro t h0
    exact step113_415_row67_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource67
    step113_415_row67_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨67, by decide⟩)
    hzero
    (contain415_67 D)
    15 step113_415_row67_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨67, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_68 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨68, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource68 := by
  rw [show activeSet415 ⟨68, by decide⟩ = {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource68
      step113_415_row68_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource68
      step113_415_row68_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource68
      step113_415_row68_W_le_source (D.A t) ⟨2, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource68
      step113_415_row68_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource68
      step113_415_row68_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource68
      step113_415_row68_W_le_source (D.A t) ⟨9, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource68
      step113_415_row68_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource68
      step113_415_row68_W_le_source (D.A t) ⟨15, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource68
      step113_415_row68_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource68
      step113_415_row68_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource68
      step113_415_row68_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource68
      step113_415_row68_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource68
      step113_415_row68_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource68
      step113_415_row68_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource68
      step113_415_row68_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_68 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨68, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨68, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource68 := by
    intro t h0
    exact step113_415_row68_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource68
    step113_415_row68_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨68, by decide⟩)
    hzero
    (contain415_68 D)
    9 step113_415_row68_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(7 : ℕ) : Int) = S_415.occRhs ⟨68, by decide⟩ := by decide
  rw [show (16 : ℕ) - 9 = 7 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_69 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨69, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource69 := by
  rw [show activeSet415 ⟨69, by decide⟩ = {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource69
      step113_415_row69_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource69
      step113_415_row69_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource69
      step113_415_row69_W_le_source (D.A t) ⟨2, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource69
      step113_415_row69_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource69
      step113_415_row69_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource69
      step113_415_row69_W_le_source (D.A t) ⟨9, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource69
      step113_415_row69_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource69
      step113_415_row69_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource69
      step113_415_row69_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource69
      step113_415_row69_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource69
      step113_415_row69_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource69
      step113_415_row69_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource69
      step113_415_row69_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource69
      step113_415_row69_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource69
      step113_415_row69_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_69 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨69, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨69, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource69 := by
    intro t h0
    exact step113_415_row69_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource69
    step113_415_row69_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨69, by decide⟩)
    hzero
    (contain415_69 D)
    9 step113_415_row69_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(7 : ℕ) : Int) = S_415.occRhs ⟨69, by decide⟩ := by decide
  rw [show (16 : ℕ) - 9 = 7 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_70 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨70, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource70 := by
  rw [show activeSet415 ⟨70, by decide⟩ = {⟨0, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource70
      step113_415_row70_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource70
      step113_415_row70_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource70
      step113_415_row70_W_le_source (D.A t) ⟨6, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource70
      step113_415_row70_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource70
      step113_415_row70_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource70
      step113_415_row70_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource70
      step113_415_row70_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource70
      step113_415_row70_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource70
      step113_415_row70_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource70
      step113_415_row70_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource70
      step113_415_row70_W_le_source (D.A t) ⟨20, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource70
      step113_415_row70_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource70
      step113_415_row70_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource70
      step113_415_row70_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource70
      step113_415_row70_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_70 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨70, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨70, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource70 := by
    intro t h0
    exact step113_415_row70_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource70
    step113_415_row70_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨70, by decide⟩)
    hzero
    (contain415_70 D)
    9 step113_415_row70_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(7 : ℕ) : Int) = S_415.occRhs ⟨70, by decide⟩ := by decide
  rw [show (16 : ℕ) - 9 = 7 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_71 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨71, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource71 := by
  rw [show activeSet415 ⟨71, by decide⟩ = {⟨0, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource71
      step113_415_row71_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource71
      step113_415_row71_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource71
      step113_415_row71_W_le_source (D.A t) ⟨6, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource71
      step113_415_row71_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource71
      step113_415_row71_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource71
      step113_415_row71_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource71
      step113_415_row71_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource71
      step113_415_row71_W_le_source (D.A t) ⟨15, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource71
      step113_415_row71_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource71
      step113_415_row71_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource71
      step113_415_row71_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource71
      step113_415_row71_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource71
      step113_415_row71_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource71
      step113_415_row71_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource71
      step113_415_row71_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_71 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨71, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨71, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource71 := by
    intro t h0
    exact step113_415_row71_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource71
    step113_415_row71_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨71, by decide⟩)
    hzero
    (contain415_71 D)
    9 step113_415_row71_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(7 : ℕ) : Int) = S_415.occRhs ⟨71, by decide⟩ := by decide
  rw [show (16 : ℕ) - 9 = 7 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_72 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨72, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource72 := by
  rw [show activeSet415 ⟨72, by decide⟩ = {⟨0, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource72
      step113_415_row72_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource72
      step113_415_row72_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource72
      step113_415_row72_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource72
      step113_415_row72_W_le_source (D.A t) ⟨15, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource72
      step113_415_row72_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource72
      step113_415_row72_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource72
      step113_415_row72_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource72
      step113_415_row72_W_le_source (D.A t) ⟨31, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource72
      step113_415_row72_W_le_source (D.A t) ⟨32, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource72
      step113_415_row72_W_le_source (D.A t) ⟨45, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource72
      step113_415_row72_W_le_source (D.A t) ⟨46, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource72
      step113_415_row72_W_le_source (D.A t) ⟨47, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource72
      step113_415_row72_W_le_source (D.A t) ⟨48, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource72
      step113_415_row72_W_le_source (D.A t) ⟨61, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource72
      step113_415_row72_W_le_source (D.A t) ⟨62, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_72 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨72, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨72, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource72 := by
    intro t h0
    exact step113_415_row72_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource72
    step113_415_row72_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨72, by decide⟩)
    hzero
    (contain415_72 D)
    9 step113_415_row72_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(7 : ℕ) : Int) = S_415.occRhs ⟨72, by decide⟩ := by decide
  rw [show (16 : ℕ) - 9 = 7 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_73 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨73, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource73 := by
  rw [show activeSet415 ⟨73, by decide⟩ = {⟨3, by decide⟩, ⟨7, by decide⟩, ⟨11, by decide⟩, ⟨17, by decide⟩, ⟨21, by decide⟩, ⟨25, by decide⟩, ⟨29, by decide⟩, ⟨34, by decide⟩, ⟨38, by decide⟩, ⟨42, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨52, by decide⟩, ⟨56, by decide⟩, ⟨60, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource73
      step113_415_row73_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource73
      step113_415_row73_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource73
      step113_415_row73_W_le_source (D.A t) ⟨11, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource73
      step113_415_row73_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource73
      step113_415_row73_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource73
      step113_415_row73_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource73
      step113_415_row73_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource73
      step113_415_row73_W_le_source (D.A t) ⟨34, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource73
      step113_415_row73_W_le_source (D.A t) ⟨38, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource73
      step113_415_row73_W_le_source (D.A t) ⟨42, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource73
      step113_415_row73_W_le_source (D.A t) ⟨46, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource73
      step113_415_row73_W_le_source (D.A t) ⟨48, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource73
      step113_415_row73_W_le_source (D.A t) ⟨52, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource73
      step113_415_row73_W_le_source (D.A t) ⟨56, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource73
      step113_415_row73_W_le_source (D.A t) ⟨60, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_73 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨73, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨73, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource73 := by
    intro t h0
    exact step113_415_row73_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource73
    step113_415_row73_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨73, by decide⟩)
    hzero
    (contain415_73 D)
    12 step113_415_row73_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(4 : ℕ) : Int) = S_415.occRhs ⟨73, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_74 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨74, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource74 := by
  rw [show activeSet415 ⟨74, by decide⟩ = {⟨1, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource74
      step113_415_row74_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource74
      step113_415_row74_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource74
      step113_415_row74_W_le_source (D.A t) ⟨6, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource74
      step113_415_row74_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource74
      step113_415_row74_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource74
      step113_415_row74_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource74
      step113_415_row74_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource74
      step113_415_row74_W_le_source (D.A t) ⟨31, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource74
      step113_415_row74_W_le_source (D.A t) ⟨33, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource74
      step113_415_row74_W_le_source (D.A t) ⟨36, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource74
      step113_415_row74_W_le_source (D.A t) ⟨38, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource74
      step113_415_row74_W_le_source (D.A t) ⟨56, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource74
      step113_415_row74_W_le_source (D.A t) ⟨58, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource74
      step113_415_row74_W_le_source (D.A t) ⟨59, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource74
      step113_415_row74_W_le_source (D.A t) ⟨61, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_74 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨74, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨74, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource74 := by
    intro t h0
    exact step113_415_row74_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource74
    step113_415_row74_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨74, by decide⟩)
    hzero
    (contain415_74 D)
    12 step113_415_row74_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(4 : ℕ) : Int) = S_415.occRhs ⟨74, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_75 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨75, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource75 := by
  rw [show activeSet415 ⟨75, by decide⟩ = {⟨1, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource75
      step113_415_row75_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource75
      step113_415_row75_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource75
      step113_415_row75_W_le_source (D.A t) ⟨6, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource75
      step113_415_row75_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource75
      step113_415_row75_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource75
      step113_415_row75_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource75
      step113_415_row75_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource75
      step113_415_row75_W_le_source (D.A t) ⟨39, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource75
      step113_415_row75_W_le_source (D.A t) ⟨41, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource75
      step113_415_row75_W_le_source (D.A t) ⟨44, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource75
      step113_415_row75_W_le_source (D.A t) ⟨46, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource75
      step113_415_row75_W_le_source (D.A t) ⟨48, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource75
      step113_415_row75_W_le_source (D.A t) ⟨50, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource75
      step113_415_row75_W_le_source (D.A t) ⟨51, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource75
      step113_415_row75_W_le_source (D.A t) ⟨53, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_75 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨75, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨75, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource75 := by
    intro t h0
    exact step113_415_row75_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource75
    step113_415_row75_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨75, by decide⟩)
    hzero
    (contain415_75 D)
    12 step113_415_row75_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(4 : ℕ) : Int) = S_415.occRhs ⟨75, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_76 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨76, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource76 := by
  rw [show activeSet415 ⟨76, by decide⟩ = {⟨2, by decide⟩, ⟨3, by decide⟩, ⟨6, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource76
      step113_415_row76_W_le_source (D.A t) ⟨2, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource76
      step113_415_row76_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource76
      step113_415_row76_W_le_source (D.A t) ⟨6, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource76
      step113_415_row76_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource76
      step113_415_row76_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource76
      step113_415_row76_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource76
      step113_415_row76_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource76
      step113_415_row76_W_le_source (D.A t) ⟨39, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource76
      step113_415_row76_W_le_source (D.A t) ⟨42, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource76
      step113_415_row76_W_le_source (D.A t) ⟨43, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource76
      step113_415_row76_W_le_source (D.A t) ⟨46, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource76
      step113_415_row76_W_le_source (D.A t) ⟨48, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource76
      step113_415_row76_W_le_source (D.A t) ⟨49, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource76
      step113_415_row76_W_le_source (D.A t) ⟨52, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource76
      step113_415_row76_W_le_source (D.A t) ⟨53, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_76 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨76, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨76, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource76 := by
    intro t h0
    exact step113_415_row76_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource76
    step113_415_row76_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨76, by decide⟩)
    hzero
    (contain415_76 D)
    12 step113_415_row76_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(4 : ℕ) : Int) = S_415.occRhs ⟨76, by decide⟩ := by decide
  rw [show (16 : ℕ) - 12 = 4 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_77 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨77, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource77 := by
  rw [show activeSet415 ⟨77, by decide⟩ = {⟨1, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource77
      step113_415_row77_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource77
      step113_415_row77_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource77
      step113_415_row77_W_le_source (D.A t) ⟨9, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_77 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨77, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨77, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource77 := by
    intro t h0
    exact step113_415_row77_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource77
    step113_415_row77_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨77, by decide⟩)
    hzero
    (contain415_77 D)
    15 step113_415_row77_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨77, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_78 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨78, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource78 := by
  rw [show activeSet415 ⟨78, by decide⟩ = {⟨15, by decide⟩, ⟨31, by decide⟩, ⟨47, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource78
      step113_415_row78_W_le_source (D.A t) ⟨15, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource78
      step113_415_row78_W_le_source (D.A t) ⟨31, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource78
      step113_415_row78_W_le_source (D.A t) ⟨47, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_78 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨78, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨78, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource78 := by
    intro t h0
    exact step113_415_row78_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource78
    step113_415_row78_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨78, by decide⟩)
    hzero
    (contain415_78 D)
    15 step113_415_row78_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨78, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_79 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨79, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource79 := by
  rw [show activeSet415 ⟨79, by decide⟩ = {⟨19, by decide⟩, ⟨31, by decide⟩, ⟨51, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource79
      step113_415_row79_W_le_source (D.A t) ⟨19, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource79
      step113_415_row79_W_le_source (D.A t) ⟨31, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource79
      step113_415_row79_W_le_source (D.A t) ⟨51, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_79 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨79, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨79, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource79 := by
    intro t h0
    exact step113_415_row79_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource79
    step113_415_row79_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨79, by decide⟩)
    hzero
    (contain415_79 D)
    15 step113_415_row79_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨79, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_80 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨80, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource80 := by
  rw [show activeSet415 ⟨80, by decide⟩ = {⟨16, by decide⟩, ⟨36, by decide⟩, ⟨51, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource80
      step113_415_row80_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource80
      step113_415_row80_W_le_source (D.A t) ⟨36, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource80
      step113_415_row80_W_le_source (D.A t) ⟨51, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_80 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨80, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨80, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource80 := by
    intro t h0
    exact step113_415_row80_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource80
    step113_415_row80_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨80, by decide⟩)
    hzero
    (contain415_80 D)
    15 step113_415_row80_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨80, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_81 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨81, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource81 := by
  rw [show activeSet415 ⟨81, by decide⟩ = {⟨4, by decide⟩, ⟨48, by decide⟩, ⟨51, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource81
      step113_415_row81_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource81
      step113_415_row81_W_le_source (D.A t) ⟨48, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource81
      step113_415_row81_W_le_source (D.A t) ⟨51, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_81 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨81, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨81, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource81 := by
    intro t h0
    exact step113_415_row81_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource81
    step113_415_row81_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨81, by decide⟩)
    hzero
    (contain415_81 D)
    15 step113_415_row81_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨81, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_82 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨82, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource82 := by
  rw [show activeSet415 ⟨82, by decide⟩ = {⟨25, by decide⟩, ⟨45, by decide⟩, ⟨51, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource82
      step113_415_row82_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource82
      step113_415_row82_W_le_source (D.A t) ⟨45, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource82
      step113_415_row82_W_le_source (D.A t) ⟨51, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_82 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨82, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨82, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource82 := by
    intro t h0
    exact step113_415_row82_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource82
    step113_415_row82_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨82, by decide⟩)
    hzero
    (contain415_82 D)
    15 step113_415_row82_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨82, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_83 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨83, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource83 := by
  rw [show activeSet415 ⟨83, by decide⟩ = {⟨26, by decide⟩, ⟨46, by decide⟩, ⟨51, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource83
      step113_415_row83_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource83
      step113_415_row83_W_le_source (D.A t) ⟨46, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource83
      step113_415_row83_W_le_source (D.A t) ⟨51, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_83 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨83, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨83, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource83 := by
    intro t h0
    exact step113_415_row83_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource83
    step113_415_row83_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨83, by decide⟩)
    hzero
    (contain415_83 D)
    15 step113_415_row83_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨83, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_84 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨84, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource84 := by
  rw [show activeSet415 ⟨84, by decide⟩ = {⟨21, by decide⟩, ⟨33, by decide⟩, ⟨51, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource84
      step113_415_row84_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource84
      step113_415_row84_W_le_source (D.A t) ⟨33, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource84
      step113_415_row84_W_le_source (D.A t) ⟨51, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_84 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨84, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨84, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource84 := by
    intro t h0
    exact step113_415_row84_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource84
    step113_415_row84_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨84, by decide⟩)
    hzero
    (contain415_84 D)
    15 step113_415_row84_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨84, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_85 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨85, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource85 := by
  rw [show activeSet415 ⟨85, by decide⟩ = {⟨22, by decide⟩, ⟨34, by decide⟩, ⟨51, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource85
      step113_415_row85_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource85
      step113_415_row85_W_le_source (D.A t) ⟨34, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource85
      step113_415_row85_W_le_source (D.A t) ⟨51, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_85 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨85, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨85, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource85 := by
    intro t h0
    exact step113_415_row85_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource85
    step113_415_row85_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨85, by decide⟩)
    hzero
    (contain415_85 D)
    15 step113_415_row85_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨85, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_86 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨86, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource86 := by
  rw [show activeSet415 ⟨86, by decide⟩ = {⟨28, by decide⟩, ⟨42, by decide⟩, ⟨53, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource86
      step113_415_row86_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource86
      step113_415_row86_W_le_source (D.A t) ⟨42, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource86
      step113_415_row86_W_le_source (D.A t) ⟨53, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_86 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨86, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨86, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource86 := by
    intro t h0
    exact step113_415_row86_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource86
    step113_415_row86_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨86, by decide⟩)
    hzero
    (contain415_86 D)
    15 step113_415_row86_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨86, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_87 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨87, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource87 := by
  rw [show activeSet415 ⟨87, by decide⟩ = {⟨28, by decide⟩, ⟨41, by decide⟩, ⟨54, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource87
      step113_415_row87_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource87
      step113_415_row87_W_le_source (D.A t) ⟨41, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource87
      step113_415_row87_W_le_source (D.A t) ⟨54, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_87 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨87, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨87, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource87 := by
    intro t h0
    exact step113_415_row87_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource87
    step113_415_row87_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨87, by decide⟩)
    hzero
    (contain415_87 D)
    15 step113_415_row87_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨87, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_88 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨88, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource88 := by
  rw [show activeSet415 ⟨88, by decide⟩ = {⟨1, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource88
      step113_415_row88_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource88
      step113_415_row88_W_le_source (D.A t) ⟨59, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource88
      step113_415_row88_W_le_source (D.A t) ⟨61, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_88 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨88, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨88, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource88 := by
    intro t h0
    exact step113_415_row88_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource88
    step113_415_row88_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨88, by decide⟩)
    hzero
    (contain415_88 D)
    15 step113_415_row88_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨88, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_89 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨89, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource89 := by
  rw [show activeSet415 ⟨89, by decide⟩ = {⟨2, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource89
      step113_415_row89_W_le_source (D.A t) ⟨2, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource89
      step113_415_row89_W_le_source (D.A t) ⟨59, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource89
      step113_415_row89_W_le_source (D.A t) ⟨62, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_89 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨89, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨89, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource89 := by
    intro t h0
    exact step113_415_row89_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource89
    step113_415_row89_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨89, by decide⟩)
    hzero
    (contain415_89 D)
    15 step113_415_row89_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨89, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_90 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨90, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource90 := by
  rw [show activeSet415 ⟨90, by decide⟩ = {⟨12, by decide⟩, ⟨22, by decide⟩, ⟨25, by decide⟩, ⟨35, by decide⟩, ⟨40, by decide⟩, ⟨50, by decide⟩, ⟨61, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource90
      step113_415_row90_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource90
      step113_415_row90_W_le_source (D.A t) ⟨22, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource90
      step113_415_row90_W_le_source (D.A t) ⟨25, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource90
      step113_415_row90_W_le_source (D.A t) ⟨35, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource90
      step113_415_row90_W_le_source (D.A t) ⟨40, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource90
      step113_415_row90_W_le_source (D.A t) ⟨50, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource90
      step113_415_row90_W_le_source (D.A t) ⟨61, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_90 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨90, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨90, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource90 := by
    intro t h0
    exact step113_415_row90_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource90
    step113_415_row90_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨90, by decide⟩)
    hzero
    (contain415_90 D)
    15 step113_415_row90_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨90, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_91 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨91, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource91 := by
  rw [show activeSet415 ⟨91, by decide⟩ = {⟨4, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩, ⟨39, by decide⟩, ⟨44, by decide⟩, ⟨48, by decide⟩, ⟨51, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource91
      step113_415_row91_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource91
      step113_415_row91_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource91
      step113_415_row91_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource91
      step113_415_row91_W_le_source (D.A t) ⟨39, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource91
      step113_415_row91_W_le_source (D.A t) ⟨44, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource91
      step113_415_row91_W_le_source (D.A t) ⟨48, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource91
      step113_415_row91_W_le_source (D.A t) ⟨51, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_91 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨91, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨91, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource91 := by
    intro t h0
    exact step113_415_row91_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource91
    step113_415_row91_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨91, by decide⟩)
    hzero
    (contain415_91 D)
    15 step113_415_row91_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨91, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_92 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨92, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource92 := by
  rw [show activeSet415 ⟨92, by decide⟩ = {⟨3, by decide⟩, ⟨24, by decide⟩, ⟨28, by decide⟩, ⟨32, by decide⟩, ⟨36, by decide⟩, ⟨55, by decide⟩, ⟨59, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource92
      step113_415_row92_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource92
      step113_415_row92_W_le_source (D.A t) ⟨24, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource92
      step113_415_row92_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource92
      step113_415_row92_W_le_source (D.A t) ⟨32, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource92
      step113_415_row92_W_le_source (D.A t) ⟨36, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource92
      step113_415_row92_W_le_source (D.A t) ⟨55, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource92
      step113_415_row92_W_le_source (D.A t) ⟨59, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_92 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨92, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨92, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource92 := by
    intro t h0
    exact step113_415_row92_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource92
    step113_415_row92_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨92, by decide⟩)
    hzero
    (contain415_92 D)
    15 step113_415_row92_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨92, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_93 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨93, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource93 := by
  rw [show activeSet415 ⟨93, by decide⟩ = {⟨4, by decide⟩, ⟨23, by decide⟩, ⟨28, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource93
      step113_415_row93_W_le_source (D.A t) ⟨4, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource93
      step113_415_row93_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource93
      step113_415_row93_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource93
      step113_415_row93_W_le_source (D.A t) ⟨32, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource93
      step113_415_row93_W_le_source (D.A t) ⟨35, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource93
      step113_415_row93_W_le_source (D.A t) ⟨56, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource93
      step113_415_row93_W_le_source (D.A t) ⟨59, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_93 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨93, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨93, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource93 := by
    intro t h0
    exact step113_415_row93_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource93
    step113_415_row93_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨93, by decide⟩)
    hzero
    (contain415_93 D)
    15 step113_415_row93_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨93, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_94 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨94, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource94 := by
  rw [show activeSet415 ⟨94, by decide⟩ = {⟨8, by decide⟩, ⟨16, by decide⟩, ⟨23, by decide⟩, ⟨36, by decide⟩, ⟨43, by decide⟩, ⟨51, by decide⟩, ⟨60, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource94
      step113_415_row94_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource94
      step113_415_row94_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource94
      step113_415_row94_W_le_source (D.A t) ⟨23, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource94
      step113_415_row94_W_le_source (D.A t) ⟨36, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource94
      step113_415_row94_W_le_source (D.A t) ⟨43, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource94
      step113_415_row94_W_le_source (D.A t) ⟨51, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource94
      step113_415_row94_W_le_source (D.A t) ⟨60, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_94 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨94, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨94, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource94 := by
    intro t h0
    exact step113_415_row94_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource94
    step113_415_row94_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨94, by decide⟩)
    hzero
    (contain415_94 D)
    15 step113_415_row94_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(1 : ℕ) : Int) = S_415.occRhs ⟨94, by decide⟩ := by decide
  rw [show (16 : ℕ) - 15 = 1 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_95 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨95, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource95 := by
  rw [show activeSet415 ⟨95, by decide⟩ = {⟨0, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource95
      step113_415_row95_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource95
      step113_415_row95_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource95
      step113_415_row95_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource95
      step113_415_row95_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource95
      step113_415_row95_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource95
      step113_415_row95_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource95
      step113_415_row95_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource95
      step113_415_row95_W_le_source (D.A t) ⟨37, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource95
      step113_415_row95_W_le_source (D.A t) ⟨38, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource95
      step113_415_row95_W_le_source (D.A t) ⟨39, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource95
      step113_415_row95_W_le_source (D.A t) ⟨40, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource95
      step113_415_row95_W_le_source (D.A t) ⟨51, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource95
      step113_415_row95_W_le_source (D.A t) ⟨52, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource95
      step113_415_row95_W_le_source (D.A t) ⟨57, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource95
      step113_415_row95_W_le_source (D.A t) ⟨58, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_95 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨95, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨95, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource95 := by
    intro t h0
    exact step113_415_row95_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource95
    step113_415_row95_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨95, by decide⟩)
    hzero
    (contain415_95 D)
    9 step113_415_row95_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(7 : ℕ) : Int) = S_415.occRhs ⟨95, by decide⟩ := by decide
  rw [show (16 : ℕ) - 9 = 7 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_96 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨96, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource96 := by
  rw [show activeSet415 ⟨96, by decide⟩ = {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource96
      step113_415_row96_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource96
      step113_415_row96_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource96
      step113_415_row96_W_le_source (D.A t) ⟨2, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource96
      step113_415_row96_W_le_source (D.A t) ⟨15, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource96
      step113_415_row96_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource96
      step113_415_row96_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource96
      step113_415_row96_W_le_source (D.A t) ⟨18, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource96
      step113_415_row96_W_le_source (D.A t) ⟨39, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource96
      step113_415_row96_W_le_source (D.A t) ⟨40, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource96
      step113_415_row96_W_le_source (D.A t) ⟨41, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource96
      step113_415_row96_W_le_source (D.A t) ⟨42, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource96
      step113_415_row96_W_le_source (D.A t) ⟨55, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource96
      step113_415_row96_W_le_source (D.A t) ⟨56, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource96
      step113_415_row96_W_le_source (D.A t) ⟨57, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource96
      step113_415_row96_W_le_source (D.A t) ⟨58, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_96 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨96, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨96, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource96 := by
    intro t h0
    exact step113_415_row96_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource96
    step113_415_row96_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨96, by decide⟩)
    hzero
    (contain415_96 D)
    9 step113_415_row96_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(7 : ℕ) : Int) = S_415.occRhs ⟨96, by decide⟩ := by decide
  rw [show (16 : ℕ) - 9 = 7 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_97 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨97, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource97 := by
  rw [show activeSet415 ⟨97, by decide⟩ = {⟨0, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource97
      step113_415_row97_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource97
      step113_415_row97_W_le_source (D.A t) ⟨5, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource97
      step113_415_row97_W_le_source (D.A t) ⟨6, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource97
      step113_415_row97_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource97
      step113_415_row97_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource97
      step113_415_row97_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource97
      step113_415_row97_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource97
      step113_415_row97_W_le_source (D.A t) ⟨49, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource97
      step113_415_row97_W_le_source (D.A t) ⟨50, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource97
      step113_415_row97_W_le_source (D.A t) ⟨51, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource97
      step113_415_row97_W_le_source (D.A t) ⟨52, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource97
      step113_415_row97_W_le_source (D.A t) ⟨57, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource97
      step113_415_row97_W_le_source (D.A t) ⟨58, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource97
      step113_415_row97_W_le_source (D.A t) ⟨59, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource97
      step113_415_row97_W_le_source (D.A t) ⟨60, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_97 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨97, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨97, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource97 := by
    intro t h0
    exact step113_415_row97_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource97
    step113_415_row97_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨97, by decide⟩)
    hzero
    (contain415_97 D)
    9 step113_415_row97_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(7 : ℕ) : Int) = S_415.occRhs ⟨97, by decide⟩ := by decide
  rw [show (16 : ℕ) - 9 = 7 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_98 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨98, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource98 := by
  rw [show activeSet415 ⟨98, by decide⟩ = {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource98
      step113_415_row98_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource98
      step113_415_row98_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource98
      step113_415_row98_W_le_source (D.A t) ⟨2, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource98
      step113_415_row98_W_le_source (D.A t) ⟨27, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource98
      step113_415_row98_W_le_source (D.A t) ⟨28, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource98
      step113_415_row98_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource98
      step113_415_row98_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource98
      step113_415_row98_W_le_source (D.A t) ⟨39, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource98
      step113_415_row98_W_le_source (D.A t) ⟨40, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource98
      step113_415_row98_W_le_source (D.A t) ⟨41, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource98
      step113_415_row98_W_le_source (D.A t) ⟨42, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource98
      step113_415_row98_W_le_source (D.A t) ⟨51, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource98
      step113_415_row98_W_le_source (D.A t) ⟨52, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource98
      step113_415_row98_W_le_source (D.A t) ⟨53, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource98
      step113_415_row98_W_le_source (D.A t) ⟨54, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_98 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨98, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨98, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource98 := by
    intro t h0
    exact step113_415_row98_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource98
    step113_415_row98_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨98, by decide⟩)
    hzero
    (contain415_98 D)
    9 step113_415_row98_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(7 : ℕ) : Int) = S_415.occRhs ⟨98, by decide⟩ := by decide
  rw [show (16 : ℕ) - 9 = 7 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_99 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨99, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource99 := by
  rw [show activeSet415 ⟨99, by decide⟩ = {⟨0, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource99
      step113_415_row99_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource99
      step113_415_row99_W_le_source (D.A t) ⟨13, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource99
      step113_415_row99_W_le_source (D.A t) ⟨14, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource99
      step113_415_row99_W_le_source (D.A t) ⟨15, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource99
      step113_415_row99_W_le_source (D.A t) ⟨16, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource99
      step113_415_row99_W_le_source (D.A t) ⟨29, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource99
      step113_415_row99_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource99
      step113_415_row99_W_le_source (D.A t) ⟨37, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource99
      step113_415_row99_W_le_source (D.A t) ⟨38, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource99
      step113_415_row99_W_le_source (D.A t) ⟨39, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource99
      step113_415_row99_W_le_source (D.A t) ⟨40, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource99
      step113_415_row99_W_le_source (D.A t) ⟨53, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource99
      step113_415_row99_W_le_source (D.A t) ⟨54, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource99
      step113_415_row99_W_le_source (D.A t) ⟨55, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource99
      step113_415_row99_W_le_source (D.A t) ⟨56, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_99 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨99, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨99, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource99 := by
    intro t h0
    exact step113_415_row99_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource99
    step113_415_row99_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨99, by decide⟩)
    hzero
    (contain415_99 D)
    9 step113_415_row99_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(7 : ℕ) : Int) = S_415.occRhs ⟨99, by decide⟩ := by decide
  rw [show (16 : ℕ) - 9 = 7 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem contain415_100 {r : ℕ} (D : QuotientTensorDecomp o415W r)
    (t : Fin r)
    (ht : label415 (D.A t) ∈ (activeSet415 ⟨100, by decide⟩).image Fin.succ) :
    D.A t ∈ step113_415ActualSource100 := by
  rw [show activeSet415 ⟨100, by decide⟩ = {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩} from rfl] at ht
  simp only [mem_image, mem_insert, mem_singleton] at ht
  obtain ⟨j, hj, hjl⟩ := ht
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply contain415_of_sec step113_415ActualSource100
      step113_415_row100_W_le_source (D.A t) ⟨0, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource100
      step113_415_row100_W_le_source (D.A t) ⟨1, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource100
      step113_415_row100_W_le_source (D.A t) ⟨2, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource100
      step113_415_row100_W_le_source (D.A t) ⟨7, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource100
      step113_415_row100_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource100
      step113_415_row100_W_le_source (D.A t) ⟨9, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource100
      step113_415_row100_W_le_source (D.A t) ⟨10, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource100
      step113_415_row100_W_le_source (D.A t) ⟨51, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource100
      step113_415_row100_W_le_source (D.A t) ⟨52, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource100
      step113_415_row100_W_le_source (D.A t) ⟨53, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource100
      step113_415_row100_W_le_source (D.A t) ⟨54, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource100
      step113_415_row100_W_le_source (D.A t) ⟨59, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource100
      step113_415_row100_W_le_source (D.A t) ⟨60, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource100
      step113_415_row100_W_le_source (D.A t) ⟨61, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)
  · apply contain415_of_sec step113_415ActualSource100
      step113_415_row100_W_le_source (D.A t) ⟨62, by decide⟩ hjl.symm
    exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide)

private theorem rowBound415_100 {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    ∑ j ∈ activeSet415 ⟨100, by decide⟩,
      occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩ j
    ≤ S_415.occRhs ⟨100, by decide⟩ := by
  have hzero : ∀ t : Fin r, label415 (D.A t) = 0 → D.A t ∈ step113_415ActualSource100 := by
    intro t h0
    exact step113_415_row100_W_le_source (label415_eq_zero_mem (D.A t) h0)
  have h := @live_labeled_fiber_occ_row_int_padded o415W step113_415ActualSource100
    step113_415_row100_W_le_source r 63 D
    (fun t : Fin r => label415 (D.A t))
    (activeSet415 ⟨100, by decide⟩)
    hzero
    (contain415_100 D)
    9 step113_415_row100_qr
    16 hr ⟨0, by decide⟩
  have hcap : (↑(7 : ℕ) : Int) = S_415.occRhs ⟨100, by decide⟩ := by decide
  rw [show (16 : ℕ) - 9 = 7 from by omega] at h
  exact le_trans h (le_of_eq hcap)

private theorem coeffMatch415_0 (j : Fin 63) :
    S_415.occCoeff ⟨0, by decide⟩ j = if j ∈ activeSet415 ⟨0, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_1 (j : Fin 63) :
    S_415.occCoeff ⟨1, by decide⟩ j = if j ∈ activeSet415 ⟨1, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_2 (j : Fin 63) :
    S_415.occCoeff ⟨2, by decide⟩ j = if j ∈ activeSet415 ⟨2, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_3 (j : Fin 63) :
    S_415.occCoeff ⟨3, by decide⟩ j = if j ∈ activeSet415 ⟨3, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_4 (j : Fin 63) :
    S_415.occCoeff ⟨4, by decide⟩ j = if j ∈ activeSet415 ⟨4, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_5 (j : Fin 63) :
    S_415.occCoeff ⟨5, by decide⟩ j = if j ∈ activeSet415 ⟨5, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_6 (j : Fin 63) :
    S_415.occCoeff ⟨6, by decide⟩ j = if j ∈ activeSet415 ⟨6, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_7 (j : Fin 63) :
    S_415.occCoeff ⟨7, by decide⟩ j = if j ∈ activeSet415 ⟨7, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_8 (j : Fin 63) :
    S_415.occCoeff ⟨8, by decide⟩ j = if j ∈ activeSet415 ⟨8, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_9 (j : Fin 63) :
    S_415.occCoeff ⟨9, by decide⟩ j = if j ∈ activeSet415 ⟨9, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_10 (j : Fin 63) :
    S_415.occCoeff ⟨10, by decide⟩ j = if j ∈ activeSet415 ⟨10, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_11 (j : Fin 63) :
    S_415.occCoeff ⟨11, by decide⟩ j = if j ∈ activeSet415 ⟨11, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_12 (j : Fin 63) :
    S_415.occCoeff ⟨12, by decide⟩ j = if j ∈ activeSet415 ⟨12, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_13 (j : Fin 63) :
    S_415.occCoeff ⟨13, by decide⟩ j = if j ∈ activeSet415 ⟨13, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_14 (j : Fin 63) :
    S_415.occCoeff ⟨14, by decide⟩ j = if j ∈ activeSet415 ⟨14, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_15 (j : Fin 63) :
    S_415.occCoeff ⟨15, by decide⟩ j = if j ∈ activeSet415 ⟨15, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_16 (j : Fin 63) :
    S_415.occCoeff ⟨16, by decide⟩ j = if j ∈ activeSet415 ⟨16, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_17 (j : Fin 63) :
    S_415.occCoeff ⟨17, by decide⟩ j = if j ∈ activeSet415 ⟨17, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_18 (j : Fin 63) :
    S_415.occCoeff ⟨18, by decide⟩ j = if j ∈ activeSet415 ⟨18, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_19 (j : Fin 63) :
    S_415.occCoeff ⟨19, by decide⟩ j = if j ∈ activeSet415 ⟨19, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_20 (j : Fin 63) :
    S_415.occCoeff ⟨20, by decide⟩ j = if j ∈ activeSet415 ⟨20, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_21 (j : Fin 63) :
    S_415.occCoeff ⟨21, by decide⟩ j = if j ∈ activeSet415 ⟨21, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_22 (j : Fin 63) :
    S_415.occCoeff ⟨22, by decide⟩ j = if j ∈ activeSet415 ⟨22, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_23 (j : Fin 63) :
    S_415.occCoeff ⟨23, by decide⟩ j = if j ∈ activeSet415 ⟨23, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_24 (j : Fin 63) :
    S_415.occCoeff ⟨24, by decide⟩ j = if j ∈ activeSet415 ⟨24, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_25 (j : Fin 63) :
    S_415.occCoeff ⟨25, by decide⟩ j = if j ∈ activeSet415 ⟨25, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_26 (j : Fin 63) :
    S_415.occCoeff ⟨26, by decide⟩ j = if j ∈ activeSet415 ⟨26, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_27 (j : Fin 63) :
    S_415.occCoeff ⟨27, by decide⟩ j = if j ∈ activeSet415 ⟨27, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_28 (j : Fin 63) :
    S_415.occCoeff ⟨28, by decide⟩ j = if j ∈ activeSet415 ⟨28, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_29 (j : Fin 63) :
    S_415.occCoeff ⟨29, by decide⟩ j = if j ∈ activeSet415 ⟨29, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_30 (j : Fin 63) :
    S_415.occCoeff ⟨30, by decide⟩ j = if j ∈ activeSet415 ⟨30, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_31 (j : Fin 63) :
    S_415.occCoeff ⟨31, by decide⟩ j = if j ∈ activeSet415 ⟨31, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_32 (j : Fin 63) :
    S_415.occCoeff ⟨32, by decide⟩ j = if j ∈ activeSet415 ⟨32, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_33 (j : Fin 63) :
    S_415.occCoeff ⟨33, by decide⟩ j = if j ∈ activeSet415 ⟨33, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_34 (j : Fin 63) :
    S_415.occCoeff ⟨34, by decide⟩ j = if j ∈ activeSet415 ⟨34, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_35 (j : Fin 63) :
    S_415.occCoeff ⟨35, by decide⟩ j = if j ∈ activeSet415 ⟨35, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_36 (j : Fin 63) :
    S_415.occCoeff ⟨36, by decide⟩ j = if j ∈ activeSet415 ⟨36, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_37 (j : Fin 63) :
    S_415.occCoeff ⟨37, by decide⟩ j = if j ∈ activeSet415 ⟨37, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_38 (j : Fin 63) :
    S_415.occCoeff ⟨38, by decide⟩ j = if j ∈ activeSet415 ⟨38, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_39 (j : Fin 63) :
    S_415.occCoeff ⟨39, by decide⟩ j = if j ∈ activeSet415 ⟨39, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_40 (j : Fin 63) :
    S_415.occCoeff ⟨40, by decide⟩ j = if j ∈ activeSet415 ⟨40, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_41 (j : Fin 63) :
    S_415.occCoeff ⟨41, by decide⟩ j = if j ∈ activeSet415 ⟨41, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_42 (j : Fin 63) :
    S_415.occCoeff ⟨42, by decide⟩ j = if j ∈ activeSet415 ⟨42, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_43 (j : Fin 63) :
    S_415.occCoeff ⟨43, by decide⟩ j = if j ∈ activeSet415 ⟨43, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_44 (j : Fin 63) :
    S_415.occCoeff ⟨44, by decide⟩ j = if j ∈ activeSet415 ⟨44, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_45 (j : Fin 63) :
    S_415.occCoeff ⟨45, by decide⟩ j = if j ∈ activeSet415 ⟨45, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_46 (j : Fin 63) :
    S_415.occCoeff ⟨46, by decide⟩ j = if j ∈ activeSet415 ⟨46, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_47 (j : Fin 63) :
    S_415.occCoeff ⟨47, by decide⟩ j = if j ∈ activeSet415 ⟨47, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_48 (j : Fin 63) :
    S_415.occCoeff ⟨48, by decide⟩ j = if j ∈ activeSet415 ⟨48, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_49 (j : Fin 63) :
    S_415.occCoeff ⟨49, by decide⟩ j = if j ∈ activeSet415 ⟨49, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_50 (j : Fin 63) :
    S_415.occCoeff ⟨50, by decide⟩ j = if j ∈ activeSet415 ⟨50, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_51 (j : Fin 63) :
    S_415.occCoeff ⟨51, by decide⟩ j = if j ∈ activeSet415 ⟨51, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_52 (j : Fin 63) :
    S_415.occCoeff ⟨52, by decide⟩ j = if j ∈ activeSet415 ⟨52, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_53 (j : Fin 63) :
    S_415.occCoeff ⟨53, by decide⟩ j = if j ∈ activeSet415 ⟨53, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_54 (j : Fin 63) :
    S_415.occCoeff ⟨54, by decide⟩ j = if j ∈ activeSet415 ⟨54, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_55 (j : Fin 63) :
    S_415.occCoeff ⟨55, by decide⟩ j = if j ∈ activeSet415 ⟨55, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_56 (j : Fin 63) :
    S_415.occCoeff ⟨56, by decide⟩ j = if j ∈ activeSet415 ⟨56, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_57 (j : Fin 63) :
    S_415.occCoeff ⟨57, by decide⟩ j = if j ∈ activeSet415 ⟨57, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_58 (j : Fin 63) :
    S_415.occCoeff ⟨58, by decide⟩ j = if j ∈ activeSet415 ⟨58, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_59 (j : Fin 63) :
    S_415.occCoeff ⟨59, by decide⟩ j = if j ∈ activeSet415 ⟨59, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_60 (j : Fin 63) :
    S_415.occCoeff ⟨60, by decide⟩ j = if j ∈ activeSet415 ⟨60, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_61 (j : Fin 63) :
    S_415.occCoeff ⟨61, by decide⟩ j = if j ∈ activeSet415 ⟨61, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_62 (j : Fin 63) :
    S_415.occCoeff ⟨62, by decide⟩ j = if j ∈ activeSet415 ⟨62, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_63 (j : Fin 63) :
    S_415.occCoeff ⟨63, by decide⟩ j = if j ∈ activeSet415 ⟨63, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_64 (j : Fin 63) :
    S_415.occCoeff ⟨64, by decide⟩ j = if j ∈ activeSet415 ⟨64, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_65 (j : Fin 63) :
    S_415.occCoeff ⟨65, by decide⟩ j = if j ∈ activeSet415 ⟨65, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_66 (j : Fin 63) :
    S_415.occCoeff ⟨66, by decide⟩ j = if j ∈ activeSet415 ⟨66, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_67 (j : Fin 63) :
    S_415.occCoeff ⟨67, by decide⟩ j = if j ∈ activeSet415 ⟨67, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_68 (j : Fin 63) :
    S_415.occCoeff ⟨68, by decide⟩ j = if j ∈ activeSet415 ⟨68, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_69 (j : Fin 63) :
    S_415.occCoeff ⟨69, by decide⟩ j = if j ∈ activeSet415 ⟨69, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_70 (j : Fin 63) :
    S_415.occCoeff ⟨70, by decide⟩ j = if j ∈ activeSet415 ⟨70, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_71 (j : Fin 63) :
    S_415.occCoeff ⟨71, by decide⟩ j = if j ∈ activeSet415 ⟨71, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_72 (j : Fin 63) :
    S_415.occCoeff ⟨72, by decide⟩ j = if j ∈ activeSet415 ⟨72, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_73 (j : Fin 63) :
    S_415.occCoeff ⟨73, by decide⟩ j = if j ∈ activeSet415 ⟨73, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_74 (j : Fin 63) :
    S_415.occCoeff ⟨74, by decide⟩ j = if j ∈ activeSet415 ⟨74, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_75 (j : Fin 63) :
    S_415.occCoeff ⟨75, by decide⟩ j = if j ∈ activeSet415 ⟨75, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_76 (j : Fin 63) :
    S_415.occCoeff ⟨76, by decide⟩ j = if j ∈ activeSet415 ⟨76, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_77 (j : Fin 63) :
    S_415.occCoeff ⟨77, by decide⟩ j = if j ∈ activeSet415 ⟨77, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_78 (j : Fin 63) :
    S_415.occCoeff ⟨78, by decide⟩ j = if j ∈ activeSet415 ⟨78, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_79 (j : Fin 63) :
    S_415.occCoeff ⟨79, by decide⟩ j = if j ∈ activeSet415 ⟨79, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_80 (j : Fin 63) :
    S_415.occCoeff ⟨80, by decide⟩ j = if j ∈ activeSet415 ⟨80, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_81 (j : Fin 63) :
    S_415.occCoeff ⟨81, by decide⟩ j = if j ∈ activeSet415 ⟨81, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_82 (j : Fin 63) :
    S_415.occCoeff ⟨82, by decide⟩ j = if j ∈ activeSet415 ⟨82, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_83 (j : Fin 63) :
    S_415.occCoeff ⟨83, by decide⟩ j = if j ∈ activeSet415 ⟨83, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_84 (j : Fin 63) :
    S_415.occCoeff ⟨84, by decide⟩ j = if j ∈ activeSet415 ⟨84, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_85 (j : Fin 63) :
    S_415.occCoeff ⟨85, by decide⟩ j = if j ∈ activeSet415 ⟨85, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_86 (j : Fin 63) :
    S_415.occCoeff ⟨86, by decide⟩ j = if j ∈ activeSet415 ⟨86, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_87 (j : Fin 63) :
    S_415.occCoeff ⟨87, by decide⟩ j = if j ∈ activeSet415 ⟨87, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_88 (j : Fin 63) :
    S_415.occCoeff ⟨88, by decide⟩ j = if j ∈ activeSet415 ⟨88, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_89 (j : Fin 63) :
    S_415.occCoeff ⟨89, by decide⟩ j = if j ∈ activeSet415 ⟨89, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_90 (j : Fin 63) :
    S_415.occCoeff ⟨90, by decide⟩ j = if j ∈ activeSet415 ⟨90, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_91 (j : Fin 63) :
    S_415.occCoeff ⟨91, by decide⟩ j = if j ∈ activeSet415 ⟨91, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_92 (j : Fin 63) :
    S_415.occCoeff ⟨92, by decide⟩ j = if j ∈ activeSet415 ⟨92, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_93 (j : Fin 63) :
    S_415.occCoeff ⟨93, by decide⟩ j = if j ∈ activeSet415 ⟨93, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_94 (j : Fin 63) :
    S_415.occCoeff ⟨94, by decide⟩ j = if j ∈ activeSet415 ⟨94, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_95 (j : Fin 63) :
    S_415.occCoeff ⟨95, by decide⟩ j = if j ∈ activeSet415 ⟨95, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_96 (j : Fin 63) :
    S_415.occCoeff ⟨96, by decide⟩ j = if j ∈ activeSet415 ⟨96, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_97 (j : Fin 63) :
    S_415.occCoeff ⟨97, by decide⟩ j = if j ∈ activeSet415 ⟨97, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_98 (j : Fin 63) :
    S_415.occCoeff ⟨98, by decide⟩ j = if j ∈ activeSet415 ⟨98, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_99 (j : Fin 63) :
    S_415.occCoeff ⟨99, by decide⟩ j = if j ∈ activeSet415 ⟨99, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415_100 (j : Fin 63) :
    S_415.occCoeff ⟨100, by decide⟩ j = if j ∈ activeSet415 ⟨100, by decide⟩ then 1 else 0 := by
  fin_cases j <;> decide

private theorem coeffMatch415 (i : Fin 101) (j : Fin 63) :
    S_415.occCoeff i j = if j ∈ activeSet415 i then 1 else 0 := by
  fin_cases i
  · exact coeffMatch415_0 j
  · exact coeffMatch415_1 j
  · exact coeffMatch415_2 j
  · exact coeffMatch415_3 j
  · exact coeffMatch415_4 j
  · exact coeffMatch415_5 j
  · exact coeffMatch415_6 j
  · exact coeffMatch415_7 j
  · exact coeffMatch415_8 j
  · exact coeffMatch415_9 j
  · exact coeffMatch415_10 j
  · exact coeffMatch415_11 j
  · exact coeffMatch415_12 j
  · exact coeffMatch415_13 j
  · exact coeffMatch415_14 j
  · exact coeffMatch415_15 j
  · exact coeffMatch415_16 j
  · exact coeffMatch415_17 j
  · exact coeffMatch415_18 j
  · exact coeffMatch415_19 j
  · exact coeffMatch415_20 j
  · exact coeffMatch415_21 j
  · exact coeffMatch415_22 j
  · exact coeffMatch415_23 j
  · exact coeffMatch415_24 j
  · exact coeffMatch415_25 j
  · exact coeffMatch415_26 j
  · exact coeffMatch415_27 j
  · exact coeffMatch415_28 j
  · exact coeffMatch415_29 j
  · exact coeffMatch415_30 j
  · exact coeffMatch415_31 j
  · exact coeffMatch415_32 j
  · exact coeffMatch415_33 j
  · exact coeffMatch415_34 j
  · exact coeffMatch415_35 j
  · exact coeffMatch415_36 j
  · exact coeffMatch415_37 j
  · exact coeffMatch415_38 j
  · exact coeffMatch415_39 j
  · exact coeffMatch415_40 j
  · exact coeffMatch415_41 j
  · exact coeffMatch415_42 j
  · exact coeffMatch415_43 j
  · exact coeffMatch415_44 j
  · exact coeffMatch415_45 j
  · exact coeffMatch415_46 j
  · exact coeffMatch415_47 j
  · exact coeffMatch415_48 j
  · exact coeffMatch415_49 j
  · exact coeffMatch415_50 j
  · exact coeffMatch415_51 j
  · exact coeffMatch415_52 j
  · exact coeffMatch415_53 j
  · exact coeffMatch415_54 j
  · exact coeffMatch415_55 j
  · exact coeffMatch415_56 j
  · exact coeffMatch415_57 j
  · exact coeffMatch415_58 j
  · exact coeffMatch415_59 j
  · exact coeffMatch415_60 j
  · exact coeffMatch415_61 j
  · exact coeffMatch415_62 j
  · exact coeffMatch415_63 j
  · exact coeffMatch415_64 j
  · exact coeffMatch415_65 j
  · exact coeffMatch415_66 j
  · exact coeffMatch415_67 j
  · exact coeffMatch415_68 j
  · exact coeffMatch415_69 j
  · exact coeffMatch415_70 j
  · exact coeffMatch415_71 j
  · exact coeffMatch415_72 j
  · exact coeffMatch415_73 j
  · exact coeffMatch415_74 j
  · exact coeffMatch415_75 j
  · exact coeffMatch415_76 j
  · exact coeffMatch415_77 j
  · exact coeffMatch415_78 j
  · exact coeffMatch415_79 j
  · exact coeffMatch415_80 j
  · exact coeffMatch415_81 j
  · exact coeffMatch415_82 j
  · exact coeffMatch415_83 j
  · exact coeffMatch415_84 j
  · exact coeffMatch415_85 j
  · exact coeffMatch415_86 j
  · exact coeffMatch415_87 j
  · exact coeffMatch415_88 j
  · exact coeffMatch415_89 j
  · exact coeffMatch415_90 j
  · exact coeffMatch415_91 j
  · exact coeffMatch415_92 j
  · exact coeffMatch415_93 j
  · exact coeffMatch415_94 j
  · exact coeffMatch415_95 j
  · exact coeffMatch415_96 j
  · exact coeffMatch415_97 j
  · exact coeffMatch415_98 j
  · exact coeffMatch415_99 j
  · exact coeffMatch415_100 j

private theorem o415_extractRootHolds {r : ℕ} (hr : r ≤ 16)
    (D : QuotientTensorDecomp o415W r) :
    S_415.RootHolds (occVectorIntPadded (fun t : Fin r => label415 (D.A t)) 16 ⟨0, by decide⟩) :=
  rootHolds_from_label_bounds S_415 _
    (fun j => occVectorIntPadded_nonneg _ ⟨0, by decide⟩ j)
    (o415_total hr D)
    activeSet415
    (fun i => by
      fin_cases i
      · exact rowBound415_0 hr D
      · exact rowBound415_1 hr D
      · exact rowBound415_2 hr D
      · exact rowBound415_3 hr D
      · exact rowBound415_4 hr D
      · exact rowBound415_5 hr D
      · exact rowBound415_6 hr D
      · exact rowBound415_7 hr D
      · exact rowBound415_8 hr D
      · exact rowBound415_9 hr D
      · exact rowBound415_10 hr D
      · exact rowBound415_11 hr D
      · exact rowBound415_12 hr D
      · exact rowBound415_13 hr D
      · exact rowBound415_14 hr D
      · exact rowBound415_15 hr D
      · exact rowBound415_16 hr D
      · exact rowBound415_17 hr D
      · exact rowBound415_18 hr D
      · exact rowBound415_19 hr D
      · exact rowBound415_20 hr D
      · exact rowBound415_21 hr D
      · exact rowBound415_22 hr D
      · exact rowBound415_23 hr D
      · exact rowBound415_24 hr D
      · exact rowBound415_25 hr D
      · exact rowBound415_26 hr D
      · exact rowBound415_27 hr D
      · exact rowBound415_28 hr D
      · exact rowBound415_29 hr D
      · exact rowBound415_30 hr D
      · exact rowBound415_31 hr D
      · exact rowBound415_32 hr D
      · exact rowBound415_33 hr D
      · exact rowBound415_34 hr D
      · exact rowBound415_35 hr D
      · exact rowBound415_36 hr D
      · exact rowBound415_37 hr D
      · exact rowBound415_38 hr D
      · exact rowBound415_39 hr D
      · exact rowBound415_40 hr D
      · exact rowBound415_41 hr D
      · exact rowBound415_42 hr D
      · exact rowBound415_43 hr D
      · exact rowBound415_44 hr D
      · exact rowBound415_45 hr D
      · exact rowBound415_46 hr D
      · exact rowBound415_47 hr D
      · exact rowBound415_48 hr D
      · exact rowBound415_49 hr D
      · exact rowBound415_50 hr D
      · exact rowBound415_51 hr D
      · exact rowBound415_52 hr D
      · exact rowBound415_53 hr D
      · exact rowBound415_54 hr D
      · exact rowBound415_55 hr D
      · exact rowBound415_56 hr D
      · exact rowBound415_57 hr D
      · exact rowBound415_58 hr D
      · exact rowBound415_59 hr D
      · exact rowBound415_60 hr D
      · exact rowBound415_61 hr D
      · exact rowBound415_62 hr D
      · exact rowBound415_63 hr D
      · exact rowBound415_64 hr D
      · exact rowBound415_65 hr D
      · exact rowBound415_66 hr D
      · exact rowBound415_67 hr D
      · exact rowBound415_68 hr D
      · exact rowBound415_69 hr D
      · exact rowBound415_70 hr D
      · exact rowBound415_71 hr D
      · exact rowBound415_72 hr D
      · exact rowBound415_73 hr D
      · exact rowBound415_74 hr D
      · exact rowBound415_75 hr D
      · exact rowBound415_76 hr D
      · exact rowBound415_77 hr D
      · exact rowBound415_78 hr D
      · exact rowBound415_79 hr D
      · exact rowBound415_80 hr D
      · exact rowBound415_81 hr D
      · exact rowBound415_82 hr D
      · exact rowBound415_83 hr D
      · exact rowBound415_84 hr D
      · exact rowBound415_85 hr D
      · exact rowBound415_86 hr D
      · exact rowBound415_87 hr D
      · exact rowBound415_88 hr D
      · exact rowBound415_89 hr D
      · exact rowBound415_90 hr D
      · exact rowBound415_91 hr D
      · exact rowBound415_92 hr D
      · exact rowBound415_93 hr D
      · exact rowBound415_94 hr D
      · exact rowBound415_95 hr D
      · exact rowBound415_96 hr D
      · exact rowBound415_97 hr D
      · exact rowBound415_98 hr D
      · exact rowBound415_99 hr D
      · exact rowBound415_100 hr D
    )
    (fun i j => coeffMatch415 i j)

/-- Unconditional orbit-415 quotient rank lower bound. -/
theorem step113_orbit415_lb17 : QuotientRankAtLeast o415W 17 := by
  apply branchBridge_quotientRankAtLeast o415W 16 S_415 orbit415_occupation_no_model
  intro r hr D
  exact ⟨_, o415_extractRootHolds hr D⟩

end QiushiMatmul
