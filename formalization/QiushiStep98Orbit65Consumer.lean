import QiushiDirectCoverage
import QiushiFlattenSeeds
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiOrbit8Closed

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix Classical
namespace QiushiMatmul

def o65W : Submodule F2 Mat3 := spanCodes [260, 160, 68, 16, 10, 1]
def o65Basis : Fin 3 → Mat3
  | ⟨0, _⟩ => codeMat 324
  | ⟨1, _⟩ => codeMat 160
  | ⟨2, _⟩ => codeMat 10

def o65SourceU : Fin 5 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 324) ⊓ kerEvalFunc (codeMat 160)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 160) ⊓ kerEvalFunc (codeMat 10)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 324) ⊓ kerEvalFunc (codeMat 10)
  | ⟨3, _⟩ => kerEvalFunc (codeMat 324 + codeMat 10) ⊓ kerEvalFunc (codeMat 160 + codeMat 10)
  | ⟨4, _⟩ => kerEvalFunc (codeMat 324 + codeMat 160 + codeMat 10)
def o65SourceLb : Fin 5 → ℕ
  | ⟨0, _⟩ => 12
  | ⟨1, _⟩ => 12
  | ⟨2, _⟩ => 12
  | ⟨3, _⟩ => 12
  | ⟨4, _⟩ => 9
def o65Lambda : Fin 5 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 1

def o65ScalarCoverB (i : Fin 5) (x0 x1 x2 : F2) : Bool :=
  match i with
  | ⟨0, _⟩ => decide (x0 = 0 ∧ x1 = 0)
  | ⟨1, _⟩ => decide (x1 = 0 ∧ x2 = 0)
  | ⟨2, _⟩ => decide (x0 = 0 ∧ x2 = 0)
  | ⟨3, _⟩ => decide (x0 + x2 = 0 ∧ x1 + x2 = 0)
  | ⟨4, _⟩ => decide (x0 + x1 + x2 = 0)

def o65Cover (i : Fin 5) (M : Mat3) : Prop :=
  o65ScalarCoverB i (evalFunc (o65Basis 0) M) (evalFunc (o65Basis 1) M) (evalFunc (o65Basis 2) M) = true

theorem o65ScalarCoverage :
    ∀ (x0 x1 x2 : F2), 1 ≤
    ∑ i : Fin 5, if o65ScalarCoverB i x0 x1 x2 = true then o65Lambda i else 0 := by
  intro x0 x1 x2
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> decide

theorem o65MatCoverage (M : Mat3) :
    1 ≤ ∑ i : Fin 5, if o65Cover i M then o65Lambda i else 0 := by
  have h := o65ScalarCoverage
    (evalFunc (o65Basis 0) M) (evalFunc (o65Basis 1) M) (evalFunc (o65Basis 2) M)
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o65ScalarCoverB i (evalFunc (o65Basis 0) M) (evalFunc (o65Basis 1) M) (evalFunc (o65Basis 2) M) <;>
    simp [o65Cover, hb]

private lemma mem_kerEvalFunc_iff65 {L M : Mat3} :
    M ∈ kerEvalFunc L ↔ evalFunc L M = 0 := Iff.rfl

theorem o65W_le_source (i : Fin 5) : o65W ≤ o65SourceU i := by
  intro M hM
  fin_cases i <;> simp only [o65W, o65SourceU, o65Basis]
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 324) [260, 160, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 160) [260, 160, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 160) [260, 160, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 10) [260, 160, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 324) [260, 160, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 10) [260, 160, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 334) [260, 160, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 170) [260, 160, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact spanCodes_le_kerEvalFunc_of_gens' (codeMat 494) [260, 160, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM

theorem o65CoverSound (i : Fin 5) (M : Mat3) (h : o65Cover i M) : M ∈ o65SourceU i := by
  fin_cases i <;>
    simp only [o65Cover, o65ScalarCoverB, o65SourceU, o65Basis, Submodule.mem_inf,
               mem_kerEvalFunc_iff65, evalFunc_add_left] at h ⊢ <;>
    exact of_decide_eq_true h

private theorem o65Cert : ((∑ i : Fin 5, o65Lambda i) - 1) * 14 < ∑ i : Fin 5, o65Lambda i * o65SourceLb i := by
  simp only [o65Lambda, o65SourceLb]; decide
private theorem o65LambdaSum : 1 ≤ ∑ i : Fin 5, o65Lambda i := by
  simp only [o65Lambda]; decide

theorem o65Lb15
    (hSource : ∀ i : Fin 5, QuotientRankAtLeast (o65SourceU i) (o65SourceLb i)) :
    QuotientRankAtLeast o65W 15 :=
  quotientRankAtLeast_of_contradiction o65W 15 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o65SourceU o65SourceLb
      o65Lambda 1 14
      o65Cover o65W_le_source hSource
      o65LambdaSum o65CoverSound
      (fun M => o65MatCoverage M) (by omega) o65Cert D)

end QiushiMatmul
