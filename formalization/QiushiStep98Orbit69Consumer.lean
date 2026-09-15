import QiushiDirectCoverage
import QiushiFlattenSeeds
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiOrbit8Closed

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix Classical
namespace QiushiMatmul

def o69W : Submodule F2 Mat3 := spanCodes [256, 164, 96, 16, 10, 1]
def o69Basis : Fin 3 → Mat3
  | ⟨0, _⟩ => codeMat 132
  | ⟨1, _⟩ => codeMat 100
  | ⟨2, _⟩ => codeMat 10

def o69SourceU : Fin 7 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 132) ⊓ kerEvalFunc (codeMat 100)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 132 + codeMat 100) ⊓ kerEvalFunc (codeMat 10)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 132) ⊓ kerEvalFunc (codeMat 10)
  | ⟨3, _⟩ => kerEvalFunc (codeMat 100) ⊓ kerEvalFunc (codeMat 10)
  | ⟨4, _⟩ => kerEvalFunc (codeMat 100 + codeMat 10)
  | ⟨5, _⟩ => kerEvalFunc (codeMat 132 + codeMat 10)
  | ⟨6, _⟩ => kerEvalFunc (codeMat 132 + codeMat 100 + codeMat 10)
def o69SourceLb : Fin 7 → ℕ
  | ⟨0, _⟩ => 12
  | ⟨1, _⟩ => 12
  | ⟨2, _⟩ => 12
  | ⟨3, _⟩ => 12
  | ⟨4, _⟩ => 9
  | ⟨5, _⟩ => 9
  | ⟨6, _⟩ => 9
def o69Lambda : Fin 7 → ℕ
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 1
  | ⟨5, _⟩ => 1
  | ⟨6, _⟩ => 1

def o69ScalarCoverB (i : Fin 7) (x0 x1 x2 : F2) : Bool :=
  match i with
  | ⟨0, _⟩ => decide ((x0 = 0 ∧ x1 = 0))
  | ⟨1, _⟩ => decide ((x0 + x1 = 0 ∧ x2 = 0))
  | ⟨2, _⟩ => decide ((x0 = 0 ∧ x2 = 0))
  | ⟨3, _⟩ => decide ((x1 = 0 ∧ x2 = 0))
  | ⟨4, _⟩ => decide (x1 + x2 = 0)
  | ⟨5, _⟩ => decide (x0 + x2 = 0)
  | ⟨6, _⟩ => decide (x0 + x1 + x2 = 0)

def o69Cover (i : Fin 7) (M : Mat3) : Prop :=
  o69ScalarCoverB i (evalFunc (o69Basis 0) M) (evalFunc (o69Basis 1) M) (evalFunc (o69Basis 2) M) = true

theorem o69ScalarCoverage :
    ∀ (x0 x1 x2 : F2), 2 ≤
    ∑ i : Fin 7, if o69ScalarCoverB i x0 x1 x2 = true then o69Lambda i else 0 := by
  intro x0 x1 x2
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> decide

theorem o69MatCoverage (M : Mat3) :
    2 ≤ ∑ i : Fin 7, if o69Cover i M then o69Lambda i else 0 := by
  have h := o69ScalarCoverage
    (evalFunc (o69Basis 0) M) (evalFunc (o69Basis 1) M) (evalFunc (o69Basis 2) M)
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o69ScalarCoverB i (evalFunc (o69Basis 0) M) (evalFunc (o69Basis 1) M) (evalFunc (o69Basis 2) M) <;>
    simp [o69Cover, hb]

private lemma mem_kerEvalFunc_iff69 {L M : Mat3} :
    M ∈ kerEvalFunc L ↔ evalFunc L M = 0 := Iff.rfl

theorem o69W_le_source (i : Fin 7) : o69W ≤ o69SourceU i := by
  intro M hM
  fin_cases i <;> simp only [o69W, o69SourceU, o69Basis]
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 132) [256, 164, 96, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 100) [256, 164, 96, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 224) [256, 164, 96, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 10) [256, 164, 96, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 132) [256, 164, 96, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 10) [256, 164, 96, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 100) [256, 164, 96, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 10) [256, 164, 96, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact spanCodes_le_kerEvalFunc_of_gens' (codeMat 110) [256, 164, 96, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM
  · exact spanCodes_le_kerEvalFunc_of_gens' (codeMat 142) [256, 164, 96, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM
  · exact spanCodes_le_kerEvalFunc_of_gens' (codeMat 234) [256, 164, 96, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM

theorem o69CoverSound (i : Fin 7) (M : Mat3) (h : o69Cover i M) : M ∈ o69SourceU i := by
  fin_cases i <;>
    simp only [o69Cover, o69ScalarCoverB, o69SourceU, o69Basis, Submodule.mem_inf,
               mem_kerEvalFunc_iff69, evalFunc_add_left] at h ⊢ <;>
    exact of_decide_eq_true h

private theorem o69Cert : ((∑ i : Fin 7, o69Lambda i) - 2) * 14 < ∑ i : Fin 7, o69Lambda i * o69SourceLb i := by
  simp only [o69Lambda, o69SourceLb]; decide
private theorem o69LambdaSum : 2 ≤ ∑ i : Fin 7, o69Lambda i := by
  simp only [o69Lambda]; decide

theorem o69Lb15
    (hSource : ∀ i : Fin 7, QuotientRankAtLeast (o69SourceU i) (o69SourceLb i)) :
    QuotientRankAtLeast o69W 15 :=
  quotientRankAtLeast_of_contradiction o69W 15 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o69SourceU o69SourceLb
      o69Lambda 2 14
      o69Cover o69W_le_source hSource
      o69LambdaSum o69CoverSound
      (fun M => o69MatCoverage M) (by omega) o69Cert D)

end QiushiMatmul
