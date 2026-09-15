import QiushiDirectCoverage
import QiushiFlattenSeeds
import QiushiOrbit10FP
import QiushiOrbit8Closed

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix Classical
namespace QiushiMatmul

def o231W : Submodule F2 Mat3 := spanCodes [256, 140, 98, 16, 1]
def o231Basis : Fin 4 → Mat3
  | ⟨0, _⟩ => codeMat 132
  | ⟨1, _⟩ => codeMat 66
  | ⟨2, _⟩ => codeMat 34
  | ⟨3, _⟩ => codeMat 12

def o231SourceU : Fin 6 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 132) ⊓ kerEvalFunc (codeMat 66 + codeMat 34)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 132 + codeMat 12) ⊓ kerEvalFunc (codeMat 34)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 132 + codeMat 34 + codeMat 12) ⊓ kerEvalFunc (codeMat 66 + codeMat 34 + codeMat 12)
  | ⟨3, _⟩ => kerEvalFunc (codeMat 66) ⊓ kerEvalFunc (codeMat 12)
  | ⟨4, _⟩ => kerEvalFunc (codeMat 132 + codeMat 34) ⊓ kerEvalFunc (codeMat 66 + codeMat 12)
  | ⟨5, _⟩ => kerEvalFunc (codeMat 132 + codeMat 66 + codeMat 12) ⊓ kerEvalFunc (codeMat 34 + codeMat 12)
def o231SourceLb : Fin 6 → ℕ
  | ⟨0, _⟩ => 12
  | ⟨1, _⟩ => 12
  | ⟨2, _⟩ => 12
  | ⟨3, _⟩ => 12
  | ⟨4, _⟩ => 12
  | ⟨5, _⟩ => 12
def o231Lambda : Fin 6 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 1
  | ⟨5, _⟩ => 1

def o231ScalarCoverB (i : Fin 6) (x0 x1 x2 x3 : F2) : Bool :=
  match i with
  | ⟨0, _⟩ => decide (x0 = 0 ∧ x1 + x2 = 0)
  | ⟨1, _⟩ => decide (x0 + x3 = 0 ∧ x2 = 0)
  | ⟨2, _⟩ => decide (x0 + x2 + x3 = 0 ∧ x1 + x2 + x3 = 0)
  | ⟨3, _⟩ => decide (x1 = 0 ∧ x3 = 0)
  | ⟨4, _⟩ => decide (x0 + x2 = 0 ∧ x1 + x3 = 0)
  | ⟨5, _⟩ => decide (x0 + x1 + x3 = 0 ∧ x2 + x3 = 0)

def o231Cover (i : Fin 6) (M : Mat3) : Prop :=
  o231ScalarCoverB i (evalFunc (o231Basis 0) M) (evalFunc (o231Basis 1) M) (evalFunc (o231Basis 2) M) (evalFunc (o231Basis 3) M) = true

theorem o231ScalarCoverage :
    ∀ (x0 x1 x2 x3 : F2), 1 ≤
    ∑ i : Fin 6, if o231ScalarCoverB i x0 x1 x2 x3 = true then o231Lambda i else 0 := by
  intro x0 x1 x2 x3
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;> decide

theorem o231MatCoverage (M : Mat3) :
    1 ≤ ∑ i : Fin 6, if o231Cover i M then o231Lambda i else 0 := by
  have h := o231ScalarCoverage
    (evalFunc (o231Basis 0) M) (evalFunc (o231Basis 1) M) (evalFunc (o231Basis 2) M) (evalFunc (o231Basis 3) M)
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o231ScalarCoverB i (evalFunc (o231Basis 0) M) (evalFunc (o231Basis 1) M) (evalFunc (o231Basis 2) M) (evalFunc (o231Basis 3) M) <;>
    simp [o231Cover, hb]

private lemma mem_kerEvalFunc_iff231 {L M : Mat3} :
    M ∈ kerEvalFunc L ↔ evalFunc L M = 0 := Iff.rfl

theorem o231W_le_source (i : Fin 6) : o231W ≤ o231SourceU i := by
  intro M hM
  fin_cases i <;> simp only [o231W, o231SourceU, o231Basis]
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 132) [256, 140, 98, 16, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 96) [256, 140, 98, 16, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 136) [256, 140, 98, 16, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 34) [256, 140, 98, 16, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 170) [256, 140, 98, 16, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 108) [256, 140, 98, 16, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 66) [256, 140, 98, 16, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 12) [256, 140, 98, 16, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 166) [256, 140, 98, 16, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 78) [256, 140, 98, 16, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 202) [256, 140, 98, 16, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 46) [256, 140, 98, 16, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩

theorem o231CoverSound (i : Fin 6) (M : Mat3) (h : o231Cover i M) : M ∈ o231SourceU i := by
  fin_cases i <;>
    simp only [o231Cover, o231ScalarCoverB, o231SourceU, o231Basis, Submodule.mem_inf,
               mem_kerEvalFunc_iff231, evalFunc_add_left] at h ⊢ <;>
    exact of_decide_eq_true h

private theorem o231Cert : ((∑ i : Fin 6, o231Lambda i) - 1) * 14 < ∑ i : Fin 6, o231Lambda i * o231SourceLb i := by
  simp only [o231Lambda, o231SourceLb]; decide
private theorem o231LambdaSum : 1 ≤ ∑ i : Fin 6, o231Lambda i := by
  simp only [o231Lambda]; decide

theorem o231Lb15
    (hSource : ∀ i : Fin 6, QuotientRankAtLeast (o231SourceU i) (o231SourceLb i)) :
    QuotientRankAtLeast o231W 15 :=
  quotientRankAtLeast_of_contradiction o231W 15 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o231SourceU o231SourceLb
      o231Lambda 1 14
      o231Cover o231W_le_source hSource
      o231LambdaSum o231CoverSound
      (fun M => o231MatCoverage M) (by omega) o231Cert D)

end QiushiMatmul
