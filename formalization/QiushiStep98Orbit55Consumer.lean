import QiushiDirectCoverage
import QiushiFlattenSeeds
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiOrbit8Closed

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix Classical
namespace QiushiMatmul

def o55W : Submodule F2 Mat3 := spanCodes [272, 132, 32, 12, 2, 1]
def o55Basis : Fin 3 → Mat3
  | ⟨0, _⟩ => codeMat 272
  | ⟨1, _⟩ => codeMat 140
  | ⟨2, _⟩ => codeMat 64

def o55SourceU : Fin 5 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 140) ⊓ kerEvalFunc (codeMat 64)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 272) ⊓ kerEvalFunc (codeMat 140 + codeMat 64)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 272 + codeMat 64) ⊓ kerEvalFunc (codeMat 140)
  | ⟨3, _⟩ => kerEvalFunc (codeMat 272) ⊓ kerEvalFunc (codeMat 64)
  | ⟨4, _⟩ => kerEvalFunc (codeMat 272 + codeMat 140)
def o55SourceLb : Fin 5 → ℕ
  | ⟨0, _⟩ => 12
  | ⟨1, _⟩ => 12
  | ⟨2, _⟩ => 12
  | ⟨3, _⟩ => 9
  | ⟨4, _⟩ => 9
def o55Lambda : Fin 5 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 1

def o55ScalarCoverB (i : Fin 5) (x0 x1 x2 : F2) : Bool :=
  match i with
  | ⟨0, _⟩ => decide (x1 = 0 ∧ x2 = 0)
  | ⟨1, _⟩ => decide (x0 = 0 ∧ x1 + x2 = 0)
  | ⟨2, _⟩ => decide (x0 + x2 = 0 ∧ x1 = 0)
  | ⟨3, _⟩ => decide (x0 = 0 ∧ x2 = 0)
  | ⟨4, _⟩ => decide (x0 + x1 = 0)

def o55Cover (i : Fin 5) (M : Mat3) : Prop :=
  o55ScalarCoverB i (evalFunc (o55Basis 0) M) (evalFunc (o55Basis 1) M) (evalFunc (o55Basis 2) M) = true

theorem o55ScalarCoverage :
    ∀ (x0 x1 x2 : F2), 1 ≤
    ∑ i : Fin 5, if o55ScalarCoverB i x0 x1 x2 = true then o55Lambda i else 0 := by
  intro x0 x1 x2
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> decide

theorem o55MatCoverage (M : Mat3) :
    1 ≤ ∑ i : Fin 5, if o55Cover i M then o55Lambda i else 0 := by
  have h := o55ScalarCoverage
    (evalFunc (o55Basis 0) M) (evalFunc (o55Basis 1) M) (evalFunc (o55Basis 2) M)
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o55ScalarCoverB i (evalFunc (o55Basis 0) M) (evalFunc (o55Basis 1) M) (evalFunc (o55Basis 2) M) <;>
    simp [o55Cover, hb]

private lemma mem_kerEvalFunc_iff55 {L M : Mat3} :
    M ∈ kerEvalFunc L ↔ evalFunc L M = 0 := Iff.rfl

theorem o55W_le_source (i : Fin 5) : o55W ≤ o55SourceU i := by
  intro M hM
  fin_cases i <;> simp only [o55W, o55SourceU, o55Basis]
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 140) [272, 132, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 64) [272, 132, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 272) [272, 132, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 204) [272, 132, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 336) [272, 132, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 140) [272, 132, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 272) [272, 132, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 64) [272, 132, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact spanCodes_le_kerEvalFunc_of_gens' (codeMat 412) [272, 132, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM

theorem o55CoverSound (i : Fin 5) (M : Mat3) (h : o55Cover i M) : M ∈ o55SourceU i := by
  fin_cases i <;>
    simp only [o55Cover, o55ScalarCoverB, o55SourceU, o55Basis, Submodule.mem_inf,
               mem_kerEvalFunc_iff55, evalFunc_add_left] at h ⊢ <;>
    exact of_decide_eq_true h

private theorem o55Cert : ((∑ i : Fin 5, o55Lambda i) - 1) * 13 < ∑ i : Fin 5, o55Lambda i * o55SourceLb i := by
  simp only [o55Lambda, o55SourceLb]; decide
private theorem o55LambdaSum : 1 ≤ ∑ i : Fin 5, o55Lambda i := by
  simp only [o55Lambda]; decide

theorem o55Lb14
    (hSource : ∀ i : Fin 5, QuotientRankAtLeast (o55SourceU i) (o55SourceLb i)) :
    QuotientRankAtLeast o55W 14 :=
  quotientRankAtLeast_of_contradiction o55W 14 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o55SourceU o55SourceLb
      o55Lambda 1 13
      o55Cover o55W_le_source hSource
      o55LambdaSum o55CoverSound
      (fun M => o55MatCoverage M) (by omega) o55Cert D)

end QiushiMatmul
