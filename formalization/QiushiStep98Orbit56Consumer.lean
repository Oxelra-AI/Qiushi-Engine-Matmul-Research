import QiushiDirectCoverage
import QiushiFlattenSeeds
import QiushiOrbit14FP
import QiushiOrbit8Closed

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix Classical
namespace QiushiMatmul

def o56W : Submodule F2 Mat3 := spanCodes [256, 160, 80, 12, 2, 1]
def o56Basis : Fin 3 → Mat3
  | ⟨0, _⟩ => codeMat 160
  | ⟨1, _⟩ => codeMat 80
  | ⟨2, _⟩ => codeMat 12

def o56SourceU : Fin 5 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 160) ⊓ kerEvalFunc (codeMat 12)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 160) ⊓ kerEvalFunc (codeMat 80 + codeMat 12)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 80) ⊓ kerEvalFunc (codeMat 12)
  | ⟨3, _⟩ => kerEvalFunc (codeMat 160 + codeMat 12) ⊓ kerEvalFunc (codeMat 80)
  | ⟨4, _⟩ => kerEvalFunc (codeMat 160 + codeMat 80)
def o56SourceLb : Fin 5 → ℕ
  | ⟨0, _⟩ => 12
  | ⟨1, _⟩ => 12
  | ⟨2, _⟩ => 12
  | ⟨3, _⟩ => 12
  | ⟨4, _⟩ => 6
def o56Lambda : Fin 5 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 1

def o56ScalarCoverB (i : Fin 5) (x0 x1 x2 : F2) : Bool :=
  match i with
  | ⟨0, _⟩ => decide ((x0 = 0 ∧ x2 = 0))
  | ⟨1, _⟩ => decide ((x0 = 0 ∧ x1 + x2 = 0))
  | ⟨2, _⟩ => decide ((x1 = 0 ∧ x2 = 0))
  | ⟨3, _⟩ => decide ((x0 + x2 = 0 ∧ x1 = 0))
  | ⟨4, _⟩ => decide (x0 + x1 = 0)

def o56Cover (i : Fin 5) (M : Mat3) : Prop :=
  o56ScalarCoverB i (evalFunc (o56Basis 0) M) (evalFunc (o56Basis 1) M) (evalFunc (o56Basis 2) M) = true

theorem o56ScalarCoverage :
    ∀ (x0 x1 x2 : F2), 1 ≤
    ∑ i : Fin 5, if o56ScalarCoverB i x0 x1 x2 = true then o56Lambda i else 0 := by
  intro x0 x1 x2
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> decide

theorem o56MatCoverage (M : Mat3) :
    1 ≤ ∑ i : Fin 5, if o56Cover i M then o56Lambda i else 0 := by
  have h := o56ScalarCoverage
    (evalFunc (o56Basis 0) M) (evalFunc (o56Basis 1) M) (evalFunc (o56Basis 2) M)
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o56ScalarCoverB i (evalFunc (o56Basis 0) M) (evalFunc (o56Basis 1) M) (evalFunc (o56Basis 2) M) <;>
    simp [o56Cover, hb]

private lemma mem_kerEvalFunc_iff56 {L M : Mat3} :
    M ∈ kerEvalFunc L ↔ evalFunc L M = 0 := Iff.rfl

theorem o56W_le_source (i : Fin 5) : o56W ≤ o56SourceU i := by
  intro M hM
  fin_cases i <;> simp only [o56W, o56SourceU, o56Basis]
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 160) [256, 160, 80, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 12) [256, 160, 80, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 160) [256, 160, 80, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 92) [256, 160, 80, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 80) [256, 160, 80, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 12) [256, 160, 80, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 172) [256, 160, 80, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 80) [256, 160, 80, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact spanCodes_le_kerEvalFunc_of_gens' (codeMat 240) [256, 160, 80, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM

theorem o56CoverSound (i : Fin 5) (M : Mat3) (h : o56Cover i M) : M ∈ o56SourceU i := by
  fin_cases i <;>
    simp only [o56Cover, o56ScalarCoverB, o56SourceU, o56Basis, Submodule.mem_inf,
               mem_kerEvalFunc_iff56, evalFunc_add_left] at h ⊢ <;>
    exact of_decide_eq_true h

private theorem o56Cert : ((∑ i : Fin 5, o56Lambda i) - 1) * 13 < ∑ i : Fin 5, o56Lambda i * o56SourceLb i := by
  simp only [o56Lambda, o56SourceLb]; decide
private theorem o56LambdaSum : 1 ≤ ∑ i : Fin 5, o56Lambda i := by
  simp only [o56Lambda]; decide

theorem o56Lb14
    (hSource : ∀ i : Fin 5, QuotientRankAtLeast (o56SourceU i) (o56SourceLb i)) :
    QuotientRankAtLeast o56W 14 :=
  quotientRankAtLeast_of_contradiction o56W 14 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o56SourceU o56SourceLb
      o56Lambda 1 13
      o56Cover o56W_le_source hSource
      o56LambdaSum o56CoverSound
      (fun M => o56MatCoverage M) (by omega) o56Cert D)

end QiushiMatmul
