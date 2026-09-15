import QiushiDirectCoverage
import QiushiFlattenSeeds
import QiushiOrbit10FP
import QiushiOrbit8Closed

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix Classical
namespace QiushiMatmul

def o120W : Submodule F2 Mat3 := spanCodes [272, 32, 12, 2, 1]
def o120Basis : Fin 4 → Mat3
  | ⟨0, _⟩ => codeMat 272
  | ⟨1, _⟩ => codeMat 128
  | ⟨2, _⟩ => codeMat 64
  | ⟨3, _⟩ => codeMat 12

def o120SourceU : Fin 9 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 272) ⊓ kerEvalFunc (codeMat 128 + codeMat 12) ⊓ kerEvalFunc (codeMat 64)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 272 + codeMat 12) ⊓ kerEvalFunc (codeMat 128 + codeMat 12) ⊓ kerEvalFunc (codeMat 64)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 272) ⊓ kerEvalFunc (codeMat 128 + codeMat 12) ⊓ kerEvalFunc (codeMat 64 + codeMat 12)
  | ⟨3, _⟩ => kerEvalFunc (codeMat 272 + codeMat 64) ⊓ kerEvalFunc (codeMat 128 + codeMat 64) ⊓ kerEvalFunc (codeMat 12)
  | ⟨4, _⟩ => kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 64) ⊓ kerEvalFunc (codeMat 12)
  | ⟨5, _⟩ => kerEvalFunc (codeMat 272 + codeMat 12) ⊓ kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 64)
  | ⟨6, _⟩ => kerEvalFunc (codeMat 272) ⊓ kerEvalFunc (codeMat 12)
  | ⟨7, _⟩ => kerEvalFunc (codeMat 272 + codeMat 128) ⊓ kerEvalFunc (codeMat 64 + codeMat 12)
  | ⟨8, _⟩ => kerEvalFunc (codeMat 272 + codeMat 64) ⊓ kerEvalFunc (codeMat 128)
def o120SourceLb : Fin 9 → ℕ
  | ⟨0, _⟩ => 14
  | ⟨1, _⟩ => 14
  | ⟨2, _⟩ => 14
  | ⟨3, _⟩ => 14
  | ⟨4, _⟩ => 12
  | ⟨5, _⟩ => 12
  | ⟨6, _⟩ => 12
  | ⟨7, _⟩ => 12
  | ⟨8, _⟩ => 9
def o120Lambda : Fin 9 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 1
  | ⟨5, _⟩ => 1
  | ⟨6, _⟩ => 1
  | ⟨7, _⟩ => 1
  | ⟨8, _⟩ => 1

def o120ScalarCoverB (i : Fin 9) (x0 x1 x2 x3 : F2) : Bool :=
  match i with
  | ⟨0, _⟩ => decide (((x0 = 0 ∧ x1 + x3 = 0) ∧ x2 = 0))
  | ⟨1, _⟩ => decide (((x0 + x3 = 0 ∧ x1 + x3 = 0) ∧ x2 = 0))
  | ⟨2, _⟩ => decide (((x0 = 0 ∧ x1 + x3 = 0) ∧ x2 + x3 = 0))
  | ⟨3, _⟩ => decide (((x0 + x2 = 0 ∧ x1 + x2 = 0) ∧ x3 = 0))
  | ⟨4, _⟩ => decide (((x1 = 0 ∧ x2 = 0) ∧ x3 = 0))
  | ⟨5, _⟩ => decide (((x0 + x3 = 0 ∧ x1 = 0) ∧ x2 = 0))
  | ⟨6, _⟩ => decide ((x0 = 0 ∧ x3 = 0))
  | ⟨7, _⟩ => decide ((x0 + x1 = 0 ∧ x2 + x3 = 0))
  | ⟨8, _⟩ => decide ((x0 + x2 = 0 ∧ x1 = 0))

def o120Cover (i : Fin 9) (M : Mat3) : Prop :=
  o120ScalarCoverB i (evalFunc (o120Basis 0) M) (evalFunc (o120Basis 1) M) (evalFunc (o120Basis 2) M) (evalFunc (o120Basis 3) M) = true

theorem o120ScalarCoverage :
    ∀ (x0 x1 x2 x3 : F2), 1 ≤
    ∑ i : Fin 9, if o120ScalarCoverB i x0 x1 x2 x3 = true then o120Lambda i else 0 := by
  intro x0 x1 x2 x3
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;> decide

theorem o120MatCoverage (M : Mat3) :
    1 ≤ ∑ i : Fin 9, if o120Cover i M then o120Lambda i else 0 := by
  have h := o120ScalarCoverage
    (evalFunc (o120Basis 0) M) (evalFunc (o120Basis 1) M) (evalFunc (o120Basis 2) M) (evalFunc (o120Basis 3) M)
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o120ScalarCoverB i (evalFunc (o120Basis 0) M) (evalFunc (o120Basis 1) M) (evalFunc (o120Basis 2) M) (evalFunc (o120Basis 3) M) <;>
    simp [o120Cover, hb]

private lemma mem_kerEvalFunc_iff120 {L M : Mat3} :
    M ∈ kerEvalFunc L ↔ evalFunc L M = 0 := Iff.rfl

theorem o120W_le_source (i : Fin 9) : o120W ≤ o120SourceU i := by
  intro M hM
  fin_cases i <;> simp only [o120W, o120SourceU, o120Basis]
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 272) [272, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 140) [272, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 64) [272, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 284) [272, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 140) [272, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 64) [272, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 272) [272, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 140) [272, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 76) [272, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 336) [272, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 192) [272, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 12) [272, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 128) [272, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 64) [272, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 12) [272, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 284) [272, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 128) [272, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 64) [272, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 272) [272, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 12) [272, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 400) [272, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 76) [272, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 336) [272, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 128) [272, 32, 12, 2, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩

theorem o120CoverSound (i : Fin 9) (M : Mat3) (h : o120Cover i M) : M ∈ o120SourceU i := by
  fin_cases i <;>
    simp only [o120Cover, o120ScalarCoverB, o120SourceU, o120Basis, Submodule.mem_inf,
               mem_kerEvalFunc_iff120, evalFunc_add_left] at h ⊢ <;>
    exact of_decide_eq_true h

private theorem o120Cert : ((∑ i : Fin 9, o120Lambda i) - 1) * 14 < ∑ i : Fin 9, o120Lambda i * o120SourceLb i := by
  simp only [o120Lambda, o120SourceLb]; decide
private theorem o120LambdaSum : 1 ≤ ∑ i : Fin 9, o120Lambda i := by
  simp only [o120Lambda]; decide

theorem o120Lb15
    (hSource : ∀ i : Fin 9, QuotientRankAtLeast (o120SourceU i) (o120SourceLb i)) :
    QuotientRankAtLeast o120W 15 :=
  quotientRankAtLeast_of_contradiction o120W 15 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o120SourceU o120SourceLb
      o120Lambda 1 14
      o120Cover o120W_le_source hSource
      o120LambdaSum o120CoverSound
      (fun M => o120MatCoverage M) (by omega) o120Cert D)

end QiushiMatmul
