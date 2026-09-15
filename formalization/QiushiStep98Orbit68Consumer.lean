import QiushiDirectCoverage
import QiushiFlattenSeeds
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiOrbit8Closed
import QiushiStep81Qdim2Generated

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix Classical
namespace QiushiMatmul

def o68W : Submodule F2 Mat3 := spanCodes [288, 164, 68, 16, 10, 1]
def o68Basis : Fin 3 → Mat3
  | ⟨0, _⟩ => codeMat 356
  | ⟨1, _⟩ => codeMat 196
  | ⟨2, _⟩ => codeMat 10

def o68SourceU : Fin 7 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 356) ⊓ kerEvalFunc (codeMat 196)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 356 + codeMat 196) ⊓ kerEvalFunc (codeMat 10)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 356 + codeMat 10) ⊓ kerEvalFunc (codeMat 196 + codeMat 10)
  | ⟨3, _⟩ => kerEvalFunc (codeMat 196) ⊓ kerEvalFunc (codeMat 10)
  | ⟨4, _⟩ => kerEvalFunc (codeMat 356 + codeMat 10) ⊓ kerEvalFunc (codeMat 196)
  | ⟨5, _⟩ => kerEvalFunc (codeMat 356) ⊓ kerEvalFunc (codeMat 196 + codeMat 10)
  | ⟨6, _⟩ => kerEvalFunc (codeMat 356) ⊓ kerEvalFunc (codeMat 10)
def o68SourceLb : Fin 7 → ℕ
  | ⟨0, _⟩ => 12
  | ⟨1, _⟩ => 12
  | ⟨2, _⟩ => 12
  | ⟨3, _⟩ => 12
  | ⟨4, _⟩ => 12
  | ⟨5, _⟩ => 12
  | ⟨6, _⟩ => 9
def o68Lambda : Fin 7 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 1
  | ⟨5, _⟩ => 1
  | ⟨6, _⟩ => 1

def o68ScalarCoverB (i : Fin 7) (x0 x1 x2 : F2) : Bool :=
  match i with
  | ⟨0, _⟩ => decide ((x0 = 0 ∧ x1 = 0))
  | ⟨1, _⟩ => decide ((x0 + x1 = 0 ∧ x2 = 0))
  | ⟨2, _⟩ => decide ((x0 + x2 = 0 ∧ x1 + x2 = 0))
  | ⟨3, _⟩ => decide ((x1 = 0 ∧ x2 = 0))
  | ⟨4, _⟩ => decide ((x0 + x2 = 0 ∧ x1 = 0))
  | ⟨5, _⟩ => decide ((x0 = 0 ∧ x1 + x2 = 0))
  | ⟨6, _⟩ => decide ((x0 = 0 ∧ x2 = 0))

def o68Cover (i : Fin 7) (M : Mat3) : Prop :=
  o68ScalarCoverB i (evalFunc (o68Basis 0) M) (evalFunc (o68Basis 1) M) (evalFunc (o68Basis 2) M) = true

theorem o68ScalarCoverage :
    ∀ (x0 x1 x2 : F2), 1 ≤
    ∑ i : Fin 7, if o68ScalarCoverB i x0 x1 x2 = true then o68Lambda i else 0 := by
  intro x0 x1 x2
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> decide

theorem o68MatCoverage (M : Mat3) :
    1 ≤ ∑ i : Fin 7, if o68Cover i M then o68Lambda i else 0 := by
  have h := o68ScalarCoverage
    (evalFunc (o68Basis 0) M) (evalFunc (o68Basis 1) M) (evalFunc (o68Basis 2) M)
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o68ScalarCoverB i (evalFunc (o68Basis 0) M) (evalFunc (o68Basis 1) M) (evalFunc (o68Basis 2) M) <;>
    simp [o68Cover, hb]

private lemma mem_kerEvalFunc_iff68 {L M : Mat3} :
    M ∈ kerEvalFunc L ↔ evalFunc L M = 0 := Iff.rfl

theorem o68W_le_source (i : Fin 7) : o68W ≤ o68SourceU i := by
  intro M hM
  fin_cases i <;> simp only [o68W, o68SourceU, o68Basis]
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 356) [288, 164, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 196) [288, 164, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 416) [288, 164, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 10) [288, 164, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 366) [288, 164, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 206) [288, 164, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 196) [288, 164, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 10) [288, 164, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 366) [288, 164, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 196) [288, 164, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 356) [288, 164, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 206) [288, 164, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 356) [288, 164, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 10) [288, 164, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩

theorem o68CoverSound (i : Fin 7) (M : Mat3) (h : o68Cover i M) : M ∈ o68SourceU i := by
  fin_cases i <;>
    simp only [o68Cover, o68ScalarCoverB, o68SourceU, o68Basis, Submodule.mem_inf,
               mem_kerEvalFunc_iff68, evalFunc_add_left] at h ⊢ <;>
    exact of_decide_eq_true h

private theorem o68Cert : ((∑ i : Fin 7, o68Lambda i) - 1) * 13 < ∑ i : Fin 7, o68Lambda i * o68SourceLb i := by
  simp only [o68Lambda, o68SourceLb]; decide
private theorem o68LambdaSum : 1 ≤ ∑ i : Fin 7, o68Lambda i := by
  simp only [o68Lambda]; decide

theorem o68Lb14
    (hSource : ∀ i : Fin 7, QuotientRankAtLeast (o68SourceU i) (o68SourceLb i)) :
    QuotientRankAtLeast o68W 14 :=
  quotientRankAtLeast_of_contradiction o68W 14 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o68SourceU o68SourceLb
      o68Lambda 1 13
      o68Cover o68W_le_source hSource
      o68LambdaSum o68CoverSound
      (fun M => o68MatCoverage M) (by omega) o68Cert D)

end QiushiMatmul
