import QiushiDirectCoverage
import QiushiFlattenSeeds
import QiushiOrbit13FP
import QiushiOrbit14FP
import QiushiOrbit8Closed
import QiushiStep81Qdim2Generated

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix Classical
namespace QiushiMatmul

def o82W : Submodule F2 Mat3 := spanCodes [292, 160, 96, 20, 10, 1]
def o82Basis : Fin 3 → Mat3
  | ⟨0, _⟩ => codeMat 276
  | ⟨1, _⟩ => codeMat 244
  | ⟨2, _⟩ => codeMat 10

def o82SourceU : Fin 7 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 276) ⊓ kerEvalFunc (codeMat 244)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 276 + codeMat 10) ⊓ kerEvalFunc (codeMat 244 + codeMat 10)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 276) ⊓ kerEvalFunc (codeMat 10)
  | ⟨3, _⟩ => kerEvalFunc (codeMat 276) ⊓ kerEvalFunc (codeMat 244 + codeMat 10)
  | ⟨4, _⟩ => kerEvalFunc (codeMat 244) ⊓ kerEvalFunc (codeMat 10)
  | ⟨5, _⟩ => kerEvalFunc (codeMat 276 + codeMat 10) ⊓ kerEvalFunc (codeMat 244)
  | ⟨6, _⟩ => kerEvalFunc (codeMat 276 + codeMat 244) ⊓ kerEvalFunc (codeMat 10)
def o82SourceLb : Fin 7 → ℕ
  | ⟨0, _⟩ => 12
  | ⟨1, _⟩ => 12
  | ⟨2, _⟩ => 12
  | ⟨3, _⟩ => 12
  | ⟨4, _⟩ => 12
  | ⟨5, _⟩ => 12
  | ⟨6, _⟩ => 9
def o82Lambda : Fin 7 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 1
  | ⟨5, _⟩ => 1
  | ⟨6, _⟩ => 1

def o82ScalarCoverB (i : Fin 7) (x0 x1 x2 : F2) : Bool :=
  match i with
  | ⟨0, _⟩ => decide ((x0 = 0 ∧ x1 = 0))
  | ⟨1, _⟩ => decide ((x0 + x2 = 0 ∧ x1 + x2 = 0))
  | ⟨2, _⟩ => decide ((x0 = 0 ∧ x2 = 0))
  | ⟨3, _⟩ => decide ((x0 = 0 ∧ x1 + x2 = 0))
  | ⟨4, _⟩ => decide ((x1 = 0 ∧ x2 = 0))
  | ⟨5, _⟩ => decide ((x0 + x2 = 0 ∧ x1 = 0))
  | ⟨6, _⟩ => decide ((x0 + x1 = 0 ∧ x2 = 0))

def o82Cover (i : Fin 7) (M : Mat3) : Prop :=
  o82ScalarCoverB i (evalFunc (o82Basis 0) M) (evalFunc (o82Basis 1) M) (evalFunc (o82Basis 2) M) = true

theorem o82ScalarCoverage :
    ∀ (x0 x1 x2 : F2), 1 ≤
    ∑ i : Fin 7, if o82ScalarCoverB i x0 x1 x2 = true then o82Lambda i else 0 := by
  intro x0 x1 x2
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> decide

theorem o82MatCoverage (M : Mat3) :
    1 ≤ ∑ i : Fin 7, if o82Cover i M then o82Lambda i else 0 := by
  have h := o82ScalarCoverage
    (evalFunc (o82Basis 0) M) (evalFunc (o82Basis 1) M) (evalFunc (o82Basis 2) M)
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o82ScalarCoverB i (evalFunc (o82Basis 0) M) (evalFunc (o82Basis 1) M) (evalFunc (o82Basis 2) M) <;>
    simp [o82Cover, hb]

private lemma mem_kerEvalFunc_iff82 {L M : Mat3} :
    M ∈ kerEvalFunc L ↔ evalFunc L M = 0 := Iff.rfl

theorem o82W_le_source (i : Fin 7) : o82W ≤ o82SourceU i := by
  intro M hM
  fin_cases i <;> simp only [o82W, o82SourceU, o82Basis]
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 276) [292, 160, 96, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 244) [292, 160, 96, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 286) [292, 160, 96, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 254) [292, 160, 96, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 276) [292, 160, 96, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 10) [292, 160, 96, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 276) [292, 160, 96, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 254) [292, 160, 96, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 244) [292, 160, 96, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 10) [292, 160, 96, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 286) [292, 160, 96, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 244) [292, 160, 96, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 480) [292, 160, 96, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 10) [292, 160, 96, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩

theorem o82CoverSound (i : Fin 7) (M : Mat3) (h : o82Cover i M) : M ∈ o82SourceU i := by
  fin_cases i <;>
    simp only [o82Cover, o82ScalarCoverB, o82SourceU, o82Basis, Submodule.mem_inf,
               mem_kerEvalFunc_iff82, evalFunc_add_left] at h ⊢ <;>
    exact of_decide_eq_true h

private theorem o82Cert : ((∑ i : Fin 7, o82Lambda i) - 1) * 13 < ∑ i : Fin 7, o82Lambda i * o82SourceLb i := by
  simp only [o82Lambda, o82SourceLb]; decide
private theorem o82LambdaSum : 1 ≤ ∑ i : Fin 7, o82Lambda i := by
  simp only [o82Lambda]; decide

theorem o82Lb14
    (hSource : ∀ i : Fin 7, QuotientRankAtLeast (o82SourceU i) (o82SourceLb i)) :
    QuotientRankAtLeast o82W 14 :=
  quotientRankAtLeast_of_contradiction o82W 14 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o82SourceU o82SourceLb
      o82Lambda 1 13
      o82Cover o82W_le_source hSource
      o82LambdaSum o82CoverSound
      (fun M => o82MatCoverage M) (by omega) o82Cert D)

end QiushiMatmul
