import QiushiDirectCoverage
import QiushiFlattenSeeds
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiOrbit8Closed

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix Classical
namespace QiushiMatmul

def o144W : Submodule F2 Mat3 := spanCodes [408, 84, 32, 2, 1]
def o144Basis : Fin 4 → Mat3
  | ⟨0, _⟩ => codeMat 264
  | ⟨1, _⟩ => codeMat 136
  | ⟨2, _⟩ => codeMat 68
  | ⟨3, _⟩ => codeMat 28

def o144SourceU : Fin 5 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 264 + codeMat 68) ⊓ kerEvalFunc (codeMat 136 + codeMat 28)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 264) ⊓ kerEvalFunc (codeMat 28)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 136) ⊓ kerEvalFunc (codeMat 68)
  | ⟨3, _⟩ => kerEvalFunc (codeMat 264 + codeMat 136 + codeMat 28) ⊓ kerEvalFunc (codeMat 68 + codeMat 28)
  | ⟨4, _⟩ => kerEvalFunc (codeMat 264 + codeMat 68 + codeMat 28) ⊓ kerEvalFunc (codeMat 136 + codeMat 68 + codeMat 28)
def o144SourceLb : Fin 5 → ℕ
  | ⟨0, _⟩ => 12
  | ⟨1, _⟩ => 12
  | ⟨2, _⟩ => 12
  | ⟨3, _⟩ => 12
  | ⟨4, _⟩ => 9
def o144Lambda : Fin 5 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 1

def o144ScalarCoverB (i : Fin 5) (x0 x1 x2 x3 : F2) : Bool :=
  match i with
  | ⟨0, _⟩ => decide ((x0 + x2 = 0 ∧ x1 + x3 = 0))
  | ⟨1, _⟩ => decide ((x0 = 0 ∧ x3 = 0))
  | ⟨2, _⟩ => decide ((x1 = 0 ∧ x2 = 0))
  | ⟨3, _⟩ => decide ((x0 + x1 + x3 = 0 ∧ x2 + x3 = 0))
  | ⟨4, _⟩ => decide ((x0 + x2 + x3 = 0 ∧ x1 + x2 + x3 = 0))

def o144Cover (i : Fin 5) (M : Mat3) : Prop :=
  o144ScalarCoverB i (evalFunc (o144Basis 0) M) (evalFunc (o144Basis 1) M) (evalFunc (o144Basis 2) M) (evalFunc (o144Basis 3) M) = true

theorem o144ScalarCoverage :
    ∀ (x0 x1 x2 x3 : F2), 1 ≤
    ∑ i : Fin 5, if o144ScalarCoverB i x0 x1 x2 x3 = true then o144Lambda i else 0 := by
  intro x0 x1 x2 x3
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;> decide

theorem o144MatCoverage (M : Mat3) :
    1 ≤ ∑ i : Fin 5, if o144Cover i M then o144Lambda i else 0 := by
  have h := o144ScalarCoverage
    (evalFunc (o144Basis 0) M) (evalFunc (o144Basis 1) M) (evalFunc (o144Basis 2) M) (evalFunc (o144Basis 3) M)
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o144ScalarCoverB i (evalFunc (o144Basis 0) M) (evalFunc (o144Basis 1) M) (evalFunc (o144Basis 2) M) (evalFunc (o144Basis 3) M) <;>
    simp [o144Cover, hb]

private lemma mem_kerEvalFunc_iff144 {L M : Mat3} :
    M ∈ kerEvalFunc L ↔ evalFunc L M = 0 := Iff.rfl

theorem o144W_le_source (i : Fin 5) : o144W ≤ o144SourceU i := by
  intro M hM
  fin_cases i <;> simp only [o144W, o144SourceU, o144Basis]
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 332) [408, 84, 32, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 148) [408, 84, 32, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 264) [408, 84, 32, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 28) [408, 84, 32, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 136) [408, 84, 32, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 68) [408, 84, 32, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 412) [408, 84, 32, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 88) [408, 84, 32, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 336) [408, 84, 32, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 208) [408, 84, 32, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩

theorem o144CoverSound (i : Fin 5) (M : Mat3) (h : o144Cover i M) : M ∈ o144SourceU i := by
  fin_cases i <;>
    simp only [o144Cover, o144ScalarCoverB, o144SourceU, o144Basis, Submodule.mem_inf,
               mem_kerEvalFunc_iff144, evalFunc_add_left] at h ⊢ <;>
    exact of_decide_eq_true h

private theorem o144Cert : ((∑ i : Fin 5, o144Lambda i) - 1) * 14 < ∑ i : Fin 5, o144Lambda i * o144SourceLb i := by
  simp only [o144Lambda, o144SourceLb]; decide
private theorem o144LambdaSum : 1 ≤ ∑ i : Fin 5, o144Lambda i := by
  simp only [o144Lambda]; decide

theorem o144Lb15
    (hSource : ∀ i : Fin 5, QuotientRankAtLeast (o144SourceU i) (o144SourceLb i)) :
    QuotientRankAtLeast o144W 15 :=
  quotientRankAtLeast_of_contradiction o144W 15 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o144SourceU o144SourceLb
      o144Lambda 1 14
      o144Cover o144W_le_source hSource
      o144LambdaSum o144CoverSound
      (fun M => o144MatCoverage M) (by omega) o144Cert D)

end QiushiMatmul
