import QiushiDirectCoverage
import QiushiFlattenSeeds
import QiushiOrbit14FP
import QiushiOrbit8Closed
import QiushiStep81Qdim2Generated

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix Classical
namespace QiushiMatmul

def o77W : Submodule F2 Mat3 := spanCodes [260, 128, 96, 20, 10, 1]
def o77Basis : Fin 3 → Mat3
  | ⟨0, _⟩ => codeMat 276
  | ⟨1, _⟩ => codeMat 96
  | ⟨2, _⟩ => codeMat 10

def o77SourceU : Fin 5 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 276 + codeMat 10) ⊓ kerEvalFunc (codeMat 96 + codeMat 10)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 276) ⊓ kerEvalFunc (codeMat 96)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 96) ⊓ kerEvalFunc (codeMat 10)
  | ⟨3, _⟩ => kerEvalFunc (codeMat 276) ⊓ kerEvalFunc (codeMat 10)
  | ⟨4, _⟩ => kerEvalFunc (codeMat 276 + codeMat 96 + codeMat 10)
def o77SourceLb : Fin 5 → ℕ
  | ⟨0, _⟩ => 14
  | ⟨1, _⟩ => 12
  | ⟨2, _⟩ => 12
  | ⟨3, _⟩ => 12
  | ⟨4, _⟩ => 9
def o77Lambda : Fin 5 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 1

def o77ScalarCoverB (i : Fin 5) (x0 x1 x2 : F2) : Bool :=
  match i with
  | ⟨0, _⟩ => decide ((x0 + x2 = 0 ∧ x1 + x2 = 0))
  | ⟨1, _⟩ => decide ((x0 = 0 ∧ x1 = 0))
  | ⟨2, _⟩ => decide ((x1 = 0 ∧ x2 = 0))
  | ⟨3, _⟩ => decide ((x0 = 0 ∧ x2 = 0))
  | ⟨4, _⟩ => decide (x0 + x1 + x2 = 0)

def o77Cover (i : Fin 5) (M : Mat3) : Prop :=
  o77ScalarCoverB i (evalFunc (o77Basis 0) M) (evalFunc (o77Basis 1) M) (evalFunc (o77Basis 2) M) = true

theorem o77ScalarCoverage :
    ∀ (x0 x1 x2 : F2), 1 ≤
    ∑ i : Fin 5, if o77ScalarCoverB i x0 x1 x2 = true then o77Lambda i else 0 := by
  intro x0 x1 x2
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> decide

theorem o77MatCoverage (M : Mat3) :
    1 ≤ ∑ i : Fin 5, if o77Cover i M then o77Lambda i else 0 := by
  have h := o77ScalarCoverage
    (evalFunc (o77Basis 0) M) (evalFunc (o77Basis 1) M) (evalFunc (o77Basis 2) M)
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o77ScalarCoverB i (evalFunc (o77Basis 0) M) (evalFunc (o77Basis 1) M) (evalFunc (o77Basis 2) M) <;>
    simp [o77Cover, hb]

private lemma mem_kerEvalFunc_iff77 {L M : Mat3} :
    M ∈ kerEvalFunc L ↔ evalFunc L M = 0 := Iff.rfl

theorem o77W_le_source (i : Fin 5) : o77W ≤ o77SourceU i := by
  intro M hM
  fin_cases i <;> simp only [o77W, o77SourceU, o77Basis]
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 286) [260, 128, 96, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 106) [260, 128, 96, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 276) [260, 128, 96, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 96) [260, 128, 96, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 96) [260, 128, 96, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 10) [260, 128, 96, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 276) [260, 128, 96, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 10) [260, 128, 96, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact spanCodes_le_kerEvalFunc_of_gens' (codeMat 382) [260, 128, 96, 20, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM

theorem o77CoverSound (i : Fin 5) (M : Mat3) (h : o77Cover i M) : M ∈ o77SourceU i := by
  fin_cases i <;>
    simp only [o77Cover, o77ScalarCoverB, o77SourceU, o77Basis, Submodule.mem_inf,
               mem_kerEvalFunc_iff77, evalFunc_add_left] at h ⊢ <;>
    exact of_decide_eq_true h

private theorem o77Cert : ((∑ i : Fin 5, o77Lambda i) - 1) * 14 < ∑ i : Fin 5, o77Lambda i * o77SourceLb i := by
  simp only [o77Lambda, o77SourceLb]; decide
private theorem o77LambdaSum : 1 ≤ ∑ i : Fin 5, o77Lambda i := by
  simp only [o77Lambda]; decide

theorem o77Lb15
    (hSource : ∀ i : Fin 5, QuotientRankAtLeast (o77SourceU i) (o77SourceLb i)) :
    QuotientRankAtLeast o77W 15 :=
  quotientRankAtLeast_of_contradiction o77W 15 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o77SourceU o77SourceLb
      o77Lambda 1 14
      o77Cover o77W_le_source hSource
      o77LambdaSum o77CoverSound
      (fun M => o77MatCoverage M) (by omega) o77Cert D)

end QiushiMatmul
