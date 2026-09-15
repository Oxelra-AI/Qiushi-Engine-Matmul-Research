import QiushiDirectCoverage
import QiushiFlattenSeeds
import QiushiOrbit14FP
import QiushiOrbit8Closed
import QiushiStep81Qdim2Generated

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix Classical
namespace QiushiMatmul

def o76W : Submodule F2 Mat3 := spanCodes [288, 160, 68, 20, 10, 1]
def o76Basis : Fin 3 → Mat3
  | ⟨0, _⟩ => codeMat 416
  | ⟨1, _⟩ => codeMat 84
  | ⟨2, _⟩ => codeMat 10

def o76SourceU : Fin 5 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 416 + codeMat 10) ⊓ kerEvalFunc (codeMat 84 + codeMat 10)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 416) ⊓ kerEvalFunc (codeMat 10)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 416) ⊓ kerEvalFunc (codeMat 84 + codeMat 10)
  | ⟨3, _⟩ => kerEvalFunc (codeMat 416 + codeMat 84) ⊓ kerEvalFunc (codeMat 10)
  | ⟨4, _⟩ => kerEvalFunc (codeMat 84)
def o76SourceLb : Fin 5 → ℕ
  | ⟨0, _⟩ => 14
  | ⟨1, _⟩ => 12
  | ⟨2, _⟩ => 12
  | ⟨3, _⟩ => 12
  | ⟨4, _⟩ => 9
def o76Lambda : Fin 5 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 1

def o76ScalarCoverB (i : Fin 5) (x0 x1 x2 : F2) : Bool :=
  match i with
  | ⟨0, _⟩ => decide ((x0 + x2 = 0 ∧ x1 + x2 = 0))
  | ⟨1, _⟩ => decide ((x0 = 0 ∧ x2 = 0))
  | ⟨2, _⟩ => decide ((x0 = 0 ∧ x1 + x2 = 0))
  | ⟨3, _⟩ => decide ((x0 + x1 = 0 ∧ x2 = 0))
  | ⟨4, _⟩ => decide (x1 = 0)

def o76Cover (i : Fin 5) (M : Mat3) : Prop :=
  o76ScalarCoverB i (evalFunc (o76Basis 0) M) (evalFunc (o76Basis 1) M) (evalFunc (o76Basis 2) M) = true

theorem o76ScalarCoverage :
    ∀ (x0 x1 x2 : F2), 1 ≤
    ∑ i : Fin 5, if o76ScalarCoverB i x0 x1 x2 = true then o76Lambda i else 0 := by
  intro x0 x1 x2
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> decide

theorem o76MatCoverage (M : Mat3) :
    1 ≤ ∑ i : Fin 5, if o76Cover i M then o76Lambda i else 0 := by
  have h := o76ScalarCoverage
    (evalFunc (o76Basis 0) M) (evalFunc (o76Basis 1) M) (evalFunc (o76Basis 2) M)
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o76ScalarCoverB i (evalFunc (o76Basis 0) M) (evalFunc (o76Basis 1) M) (evalFunc (o76Basis 2) M) <;>
    simp [o76Cover, hb]

private lemma mem_kerEvalFunc_iff76 {L M : Mat3} :
    M ∈ kerEvalFunc L ↔ evalFunc L M = 0 := Iff.rfl

theorem o76W_le_source (i : Fin 5) : o76W ≤ o76SourceU i := by
  intro M hM
  fin_cases i <;> simp only [o76W, o76SourceU, o76Basis]
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 426) [288, 160, 68, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 94) [288, 160, 68, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 416) [288, 160, 68, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 10) [288, 160, 68, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 416) [288, 160, 68, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 94) [288, 160, 68, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 500) [288, 160, 68, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 10) [288, 160, 68, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact spanCodes_le_kerEvalFunc_of_gens' (codeMat 84) [288, 160, 68, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM

theorem o76CoverSound (i : Fin 5) (M : Mat3) (h : o76Cover i M) : M ∈ o76SourceU i := by
  fin_cases i <;>
    simp only [o76Cover, o76ScalarCoverB, o76SourceU, o76Basis, Submodule.mem_inf,
               mem_kerEvalFunc_iff76, evalFunc_add_left] at h ⊢ <;>
    exact of_decide_eq_true h

private theorem o76Cert : ((∑ i : Fin 5, o76Lambda i) - 1) * 14 < ∑ i : Fin 5, o76Lambda i * o76SourceLb i := by
  simp only [o76Lambda, o76SourceLb]; decide
private theorem o76LambdaSum : 1 ≤ ∑ i : Fin 5, o76Lambda i := by
  simp only [o76Lambda]; decide

theorem o76Lb15
    (hSource : ∀ i : Fin 5, QuotientRankAtLeast (o76SourceU i) (o76SourceLb i)) :
    QuotientRankAtLeast o76W 15 :=
  quotientRankAtLeast_of_contradiction o76W 15 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o76SourceU o76SourceLb
      o76Lambda 1 14
      o76Cover o76W_le_source hSource
      o76LambdaSum o76CoverSound
      (fun M => o76MatCoverage M) (by omega) o76Cert D)

end QiushiMatmul
