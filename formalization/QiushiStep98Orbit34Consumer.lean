import QiushiDirectCoverage
import QiushiFlattenSeeds
import QiushiOrbit11FP
import QiushiOrbit8Closed

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix Classical
namespace QiushiMatmul

def o34W : Submodule F2 Mat3 := spanCodes [256, 68, 20, 8, 2, 1]
def o34Basis : Fin 3 → Mat3
  | ⟨0, _⟩ => codeMat 128
  | ⟨1, _⟩ => codeMat 84
  | ⟨2, _⟩ => codeMat 32

def o34SourceU : Fin 5 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 84)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 84 + codeMat 32)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 84) ⊓ kerEvalFunc (codeMat 32)
  | ⟨3, _⟩ => kerEvalFunc (codeMat 128 + codeMat 84) ⊓ kerEvalFunc (codeMat 32)
  | ⟨4, _⟩ => kerEvalFunc (codeMat 128 + codeMat 32)
def o34SourceLb : Fin 5 → ℕ
  | ⟨0, _⟩ => 12
  | ⟨1, _⟩ => 12
  | ⟨2, _⟩ => 12
  | ⟨3, _⟩ => 12
  | ⟨4, _⟩ => 6
def o34Lambda : Fin 5 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 1

def o34ScalarCoverB (i : Fin 5) (x0 x1 x2 : F2) : Bool :=
  match i with
  | ⟨0, _⟩ => decide (x0 = 0 ∧ x1 = 0)
  | ⟨1, _⟩ => decide (x0 = 0 ∧ x1 + x2 = 0)
  | ⟨2, _⟩ => decide (x1 = 0 ∧ x2 = 0)
  | ⟨3, _⟩ => decide (x0 + x1 = 0 ∧ x2 = 0)
  | ⟨4, _⟩ => decide (x0 + x2 = 0)

def o34Cover (i : Fin 5) (M : Mat3) : Prop :=
  o34ScalarCoverB i (evalFunc (o34Basis 0) M) (evalFunc (o34Basis 1) M) (evalFunc (o34Basis 2) M) = true

theorem o34ScalarCoverage :
    ∀ (x0 x1 x2 : F2), 1 ≤
    ∑ i : Fin 5, if o34ScalarCoverB i x0 x1 x2 = true then o34Lambda i else 0 := by
  intro x0 x1 x2
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> decide

theorem o34MatCoverage (M : Mat3) :
    1 ≤ ∑ i : Fin 5, if o34Cover i M then o34Lambda i else 0 := by
  have h := o34ScalarCoverage
    (evalFunc (o34Basis 0) M) (evalFunc (o34Basis 1) M) (evalFunc (o34Basis 2) M)
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o34ScalarCoverB i (evalFunc (o34Basis 0) M) (evalFunc (o34Basis 1) M) (evalFunc (o34Basis 2) M) <;>
    simp [o34Cover, hb]

private lemma mem_kerEvalFunc_iff34 {L M : Mat3} :
    M ∈ kerEvalFunc L ↔ evalFunc L M = 0 := Iff.rfl

theorem o34W_le_source (i : Fin 5) : o34W ≤ o34SourceU i := by
  intro M hM
  fin_cases i <;> simp only [o34W, o34SourceU, o34Basis]
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 128) [256, 68, 20, 8, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 84) [256, 68, 20, 8, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 128) [256, 68, 20, 8, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 116) [256, 68, 20, 8, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 84) [256, 68, 20, 8, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 32) [256, 68, 20, 8, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 212) [256, 68, 20, 8, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 32) [256, 68, 20, 8, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact spanCodes_le_kerEvalFunc_of_gens' (codeMat 160) [256, 68, 20, 8, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM

theorem o34CoverSound (i : Fin 5) (M : Mat3) (h : o34Cover i M) : M ∈ o34SourceU i := by
  fin_cases i <;>
    simp only [o34Cover, o34ScalarCoverB, o34SourceU, o34Basis, Submodule.mem_inf,
               mem_kerEvalFunc_iff34, evalFunc_add_left] at h ⊢ <;>
    exact of_decide_eq_true h

private theorem o34Cert : ((∑ i : Fin 5, o34Lambda i) - 1) * 13 < ∑ i : Fin 5, o34Lambda i * o34SourceLb i := by
  simp only [o34Lambda, o34SourceLb]; decide
private theorem o34LambdaSum : 1 ≤ ∑ i : Fin 5, o34Lambda i := by
  simp only [o34Lambda]; decide

theorem o34Lb14
    (hSource : ∀ i : Fin 5, QuotientRankAtLeast (o34SourceU i) (o34SourceLb i)) :
    QuotientRankAtLeast o34W 14 :=
  quotientRankAtLeast_of_contradiction o34W 14 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o34SourceU o34SourceLb
      o34Lambda 1 13
      o34Cover o34W_le_source hSource
      o34LambdaSum o34CoverSound
      (fun M => o34MatCoverage M) (by omega) o34Cert D)

end QiushiMatmul
