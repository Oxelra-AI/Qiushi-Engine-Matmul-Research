import QiushiDirectCoverage
import QiushiFlattenSeeds
import QiushiOrbit10FP
import QiushiOrbit8Closed

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix Classical
namespace QiushiMatmul

def o67W : Submodule F2 Mat3 := spanCodes [262, 164, 68, 16, 10, 1]
def o67Basis : Fin 3 → Mat3
  | ⟨0, _⟩ => codeMat 266
  | ⟨1, _⟩ => codeMat 160
  | ⟨2, _⟩ => codeMat 110

def o67SourceU : Fin 5 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 266 + codeMat 110) ⊓ kerEvalFunc (codeMat 160)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 266)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 110)
  | ⟨3, _⟩ => kerEvalFunc (codeMat 160 + codeMat 110)
  | ⟨4, _⟩ => kerEvalFunc (codeMat 266 + codeMat 160)
def o67SourceLb : Fin 5 → ℕ
  | ⟨0, _⟩ => 12
  | ⟨1, _⟩ => 9
  | ⟨2, _⟩ => 9
  | ⟨3, _⟩ => 9
  | ⟨4, _⟩ => 9
def o67Lambda : Fin 5 → ℕ
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 1

def o67ScalarCoverB (i : Fin 5) (x0 x1 x2 : F2) : Bool :=
  match i with
  | ⟨0, _⟩ => decide (x0 + x2 = 0 ∧ x1 = 0)
  | ⟨1, _⟩ => decide (x0 = 0)
  | ⟨2, _⟩ => decide (x2 = 0)
  | ⟨3, _⟩ => decide (x1 + x2 = 0)
  | ⟨4, _⟩ => decide (x0 + x1 = 0)

def o67Cover (i : Fin 5) (M : Mat3) : Prop :=
  o67ScalarCoverB i (evalFunc (o67Basis 0) M) (evalFunc (o67Basis 1) M) (evalFunc (o67Basis 2) M) = true

theorem o67ScalarCoverage :
    ∀ (x0 x1 x2 : F2), 2 ≤
    ∑ i : Fin 5, if o67ScalarCoverB i x0 x1 x2 = true then o67Lambda i else 0 := by
  intro x0 x1 x2
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> decide

theorem o67MatCoverage (M : Mat3) :
    2 ≤ ∑ i : Fin 5, if o67Cover i M then o67Lambda i else 0 := by
  have h := o67ScalarCoverage
    (evalFunc (o67Basis 0) M) (evalFunc (o67Basis 1) M) (evalFunc (o67Basis 2) M)
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o67ScalarCoverB i (evalFunc (o67Basis 0) M) (evalFunc (o67Basis 1) M) (evalFunc (o67Basis 2) M) <;>
    simp [o67Cover, hb]

private lemma mem_kerEvalFunc_iff67 {L M : Mat3} :
    M ∈ kerEvalFunc L ↔ evalFunc L M = 0 := Iff.rfl

theorem o67W_le_source (i : Fin 5) : o67W ≤ o67SourceU i := by
  intro M hM
  fin_cases i <;> simp only [o67W, o67SourceU, o67Basis]
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 356) [262, 164, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 160) [262, 164, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact spanCodes_le_kerEvalFunc_of_gens' (codeMat 266) [262, 164, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM
  · exact spanCodes_le_kerEvalFunc_of_gens' (codeMat 110) [262, 164, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM
  · exact spanCodes_le_kerEvalFunc_of_gens' (codeMat 206) [262, 164, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM
  · exact spanCodes_le_kerEvalFunc_of_gens' (codeMat 426) [262, 164, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM

theorem o67CoverSound (i : Fin 5) (M : Mat3) (h : o67Cover i M) : M ∈ o67SourceU i := by
  fin_cases i <;>
    simp only [o67Cover, o67ScalarCoverB, o67SourceU, o67Basis, Submodule.mem_inf,
               mem_kerEvalFunc_iff67, evalFunc_add_left] at h ⊢ <;>
    exact of_decide_eq_true h

private theorem o67Cert : ((∑ i : Fin 5, o67Lambda i) - 2) * 14 < ∑ i : Fin 5, o67Lambda i * o67SourceLb i := by
  simp only [o67Lambda, o67SourceLb]; decide
private theorem o67LambdaSum : 2 ≤ ∑ i : Fin 5, o67Lambda i := by
  simp only [o67Lambda]; decide

theorem o67Lb15
    (hSource : ∀ i : Fin 5, QuotientRankAtLeast (o67SourceU i) (o67SourceLb i)) :
    QuotientRankAtLeast o67W 15 :=
  quotientRankAtLeast_of_contradiction o67W 15 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o67SourceU o67SourceLb
      o67Lambda 2 14
      o67Cover o67W_le_source hSource
      o67LambdaSum o67CoverSound
      (fun M => o67MatCoverage M) (by omega) o67Cert D)

end QiushiMatmul
