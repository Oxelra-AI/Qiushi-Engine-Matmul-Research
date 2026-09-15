import QiushiDirectCoverage
import QiushiFlattenSeeds
import QiushiOrbit8Closed

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix Classical
namespace QiushiMatmul

def o150W : Submodule F2 Mat3 := spanCodes [258, 68, 16, 10, 1]
def o150Basis : Fin 4 → Mat3
  | ⟨0, _⟩ => codeMat 266
  | ⟨1, _⟩ => codeMat 128
  | ⟨2, _⟩ => codeMat 68
  | ⟨3, _⟩ => codeMat 32

def o150SourceU : Fin 9 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 266 + codeMat 32) ⊓ kerEvalFunc (codeMat 128 + codeMat 32) ⊓ kerEvalFunc (codeMat 68)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 266) ⊓ kerEvalFunc (codeMat 128 + codeMat 32) ⊓ kerEvalFunc (codeMat 68 + codeMat 32)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 266) ⊓ kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 32)
  | ⟨3, _⟩ => kerEvalFunc (codeMat 266 + codeMat 32) ⊓ kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 68)
  | ⟨4, _⟩ => kerEvalFunc (codeMat 266) ⊓ kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 68 + codeMat 32)
  | ⟨5, _⟩ => kerEvalFunc (codeMat 266 + codeMat 128) ⊓ kerEvalFunc (codeMat 68) ⊓ kerEvalFunc (codeMat 32)
  | ⟨6, _⟩ => kerEvalFunc (codeMat 266) ⊓ kerEvalFunc (codeMat 128 + codeMat 68) ⊓ kerEvalFunc (codeMat 32)
  | ⟨7, _⟩ => kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 68) ⊓ kerEvalFunc (codeMat 32)
  | ⟨8, _⟩ => kerEvalFunc (codeMat 266 + codeMat 68)
def o150SourceLb : Fin 9 → ℕ
  | ⟨0, _⟩ => 15
  | ⟨1, _⟩ => 15
  | ⟨2, _⟩ => 14
  | ⟨3, _⟩ => 14
  | ⟨4, _⟩ => 14
  | ⟨5, _⟩ => 14
  | ⟨6, _⟩ => 14
  | ⟨7, _⟩ => 12
  | ⟨8, _⟩ => 9
def o150Lambda : Fin 9 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 1
  | ⟨5, _⟩ => 1
  | ⟨6, _⟩ => 1
  | ⟨7, _⟩ => 1
  | ⟨8, _⟩ => 1

def o150ScalarCoverB (i : Fin 9) (x0 x1 x2 x3 : F2) : Bool :=
  match i with
  | ⟨0, _⟩ => decide (((x0 + x3 = 0 ∧ x1 + x3 = 0) ∧ x2 = 0))
  | ⟨1, _⟩ => decide (((x0 = 0 ∧ x1 + x3 = 0) ∧ x2 + x3 = 0))
  | ⟨2, _⟩ => decide (((x0 = 0 ∧ x1 = 0) ∧ x3 = 0))
  | ⟨3, _⟩ => decide (((x0 + x3 = 0 ∧ x1 = 0) ∧ x2 = 0))
  | ⟨4, _⟩ => decide (((x0 = 0 ∧ x1 = 0) ∧ x2 + x3 = 0))
  | ⟨5, _⟩ => decide (((x0 + x1 = 0 ∧ x2 = 0) ∧ x3 = 0))
  | ⟨6, _⟩ => decide (((x0 = 0 ∧ x1 + x2 = 0) ∧ x3 = 0))
  | ⟨7, _⟩ => decide (((x1 = 0 ∧ x2 = 0) ∧ x3 = 0))
  | ⟨8, _⟩ => decide (x0 + x2 = 0)

def o150Cover (i : Fin 9) (M : Mat3) : Prop :=
  o150ScalarCoverB i (evalFunc (o150Basis 0) M) (evalFunc (o150Basis 1) M) (evalFunc (o150Basis 2) M) (evalFunc (o150Basis 3) M) = true

theorem o150ScalarCoverage :
    ∀ (x0 x1 x2 x3 : F2), 1 ≤
    ∑ i : Fin 9, if o150ScalarCoverB i x0 x1 x2 x3 = true then o150Lambda i else 0 := by
  intro x0 x1 x2 x3
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;> decide

theorem o150MatCoverage (M : Mat3) :
    1 ≤ ∑ i : Fin 9, if o150Cover i M then o150Lambda i else 0 := by
  have h := o150ScalarCoverage
    (evalFunc (o150Basis 0) M) (evalFunc (o150Basis 1) M) (evalFunc (o150Basis 2) M) (evalFunc (o150Basis 3) M)
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o150ScalarCoverB i (evalFunc (o150Basis 0) M) (evalFunc (o150Basis 1) M) (evalFunc (o150Basis 2) M) (evalFunc (o150Basis 3) M) <;>
    simp [o150Cover, hb]

private lemma mem_kerEvalFunc_iff150 {L M : Mat3} :
    M ∈ kerEvalFunc L ↔ evalFunc L M = 0 := Iff.rfl

theorem o150W_le_source (i : Fin 9) : o150W ≤ o150SourceU i := by
  intro M hM
  fin_cases i <;> simp only [o150W, o150SourceU, o150Basis]
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 298) [258, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 160) [258, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 68) [258, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 266) [258, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 160) [258, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 100) [258, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 266) [258, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 128) [258, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 32) [258, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 298) [258, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 128) [258, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 68) [258, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 266) [258, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 128) [258, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 100) [258, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 394) [258, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 68) [258, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 32) [258, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 266) [258, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 196) [258, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 32) [258, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 128) [258, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 68) [258, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 32) [258, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact spanCodes_le_kerEvalFunc_of_gens' (codeMat 334) [258, 68, 16, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM

theorem o150CoverSound (i : Fin 9) (M : Mat3) (h : o150Cover i M) : M ∈ o150SourceU i := by
  fin_cases i <;>
    simp only [o150Cover, o150ScalarCoverB, o150SourceU, o150Basis, Submodule.mem_inf,
               mem_kerEvalFunc_iff150, evalFunc_add_left] at h ⊢ <;>
    exact of_decide_eq_true h

private theorem o150Cert : ((∑ i : Fin 9, o150Lambda i) - 1) * 15 < ∑ i : Fin 9, o150Lambda i * o150SourceLb i := by
  simp only [o150Lambda, o150SourceLb]; decide
private theorem o150LambdaSum : 1 ≤ ∑ i : Fin 9, o150Lambda i := by
  simp only [o150Lambda]; decide

theorem o150Lb16
    (hSource : ∀ i : Fin 9, QuotientRankAtLeast (o150SourceU i) (o150SourceLb i)) :
    QuotientRankAtLeast o150W 16 :=
  quotientRankAtLeast_of_contradiction o150W 16 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o150SourceU o150SourceLb
      o150Lambda 1 15
      o150Cover o150W_le_source hSource
      o150LambdaSum o150CoverSound
      (fun M => o150MatCoverage M) (by omega) o150Cert D)

end QiushiMatmul
