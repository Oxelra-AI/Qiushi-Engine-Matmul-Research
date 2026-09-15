import QiushiDirectCoverage
import QiushiFlattenSeeds
import QiushiOrbit8Closed

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix Classical
namespace QiushiMatmul

def o237W : Submodule F2 Mat3 := spanCodes [266, 136, 96, 20, 1]
def o237Basis : Fin 4 → Mat3
  | ⟨0, _⟩ => codeMat 258
  | ⟨1, _⟩ => codeMat 138
  | ⟨2, _⟩ => codeMat 96
  | ⟨3, _⟩ => codeMat 20

def o237SourceU : Fin 15 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 138) ⊓ kerEvalFunc (codeMat 96) ⊓ kerEvalFunc (codeMat 20)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 258) ⊓ kerEvalFunc (codeMat 138 + codeMat 20) ⊓ kerEvalFunc (codeMat 96)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 258 + codeMat 96) ⊓ kerEvalFunc (codeMat 138 + codeMat 96) ⊓ kerEvalFunc (codeMat 20)
  | ⟨3, _⟩ => kerEvalFunc (codeMat 258 + codeMat 20) ⊓ kerEvalFunc (codeMat 138 + codeMat 20) ⊓ kerEvalFunc (codeMat 96 + codeMat 20)
  | ⟨4, _⟩ => kerEvalFunc (codeMat 258) ⊓ kerEvalFunc (codeMat 138 + codeMat 20) ⊓ kerEvalFunc (codeMat 96 + codeMat 20)
  | ⟨5, _⟩ => kerEvalFunc (codeMat 258 + codeMat 20) ⊓ kerEvalFunc (codeMat 138) ⊓ kerEvalFunc (codeMat 96 + codeMat 20)
  | ⟨6, _⟩ => kerEvalFunc (codeMat 258 + codeMat 138) ⊓ kerEvalFunc (codeMat 96) ⊓ kerEvalFunc (codeMat 20)
  | ⟨7, _⟩ => kerEvalFunc (codeMat 258) ⊓ kerEvalFunc (codeMat 138) ⊓ kerEvalFunc (codeMat 96)
  | ⟨8, _⟩ => kerEvalFunc (codeMat 258 + codeMat 20) ⊓ kerEvalFunc (codeMat 138 + codeMat 20) ⊓ kerEvalFunc (codeMat 96)
  | ⟨9, _⟩ => kerEvalFunc (codeMat 258) ⊓ kerEvalFunc (codeMat 96) ⊓ kerEvalFunc (codeMat 20)
  | ⟨10, _⟩ => kerEvalFunc (codeMat 258 + codeMat 20) ⊓ kerEvalFunc (codeMat 138) ⊓ kerEvalFunc (codeMat 96)
  | ⟨11, _⟩ => kerEvalFunc (codeMat 258) ⊓ kerEvalFunc (codeMat 138) ⊓ kerEvalFunc (codeMat 20)
  | ⟨12, _⟩ => kerEvalFunc (codeMat 258) ⊓ kerEvalFunc (codeMat 138) ⊓ kerEvalFunc (codeMat 96 + codeMat 20)
  | ⟨13, _⟩ => kerEvalFunc (codeMat 258) ⊓ kerEvalFunc (codeMat 138 + codeMat 96) ⊓ kerEvalFunc (codeMat 20)
  | ⟨14, _⟩ => kerEvalFunc (codeMat 258 + codeMat 96) ⊓ kerEvalFunc (codeMat 138) ⊓ kerEvalFunc (codeMat 20)
def o237SourceLb : Fin 15 → ℕ
  | ⟨0, _⟩ => 15
  | ⟨1, _⟩ => 15
  | ⟨2, _⟩ => 15
  | ⟨3, _⟩ => 15
  | ⟨4, _⟩ => 15
  | ⟨5, _⟩ => 15
  | ⟨6, _⟩ => 14
  | ⟨7, _⟩ => 14
  | ⟨8, _⟩ => 14
  | ⟨9, _⟩ => 14
  | ⟨10, _⟩ => 14
  | ⟨11, _⟩ => 14
  | ⟨12, _⟩ => 14
  | ⟨13, _⟩ => 14
  | ⟨14, _⟩ => 14
def o237Lambda : Fin 15 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 1
  | ⟨5, _⟩ => 1
  | ⟨6, _⟩ => 1
  | ⟨7, _⟩ => 1
  | ⟨8, _⟩ => 1
  | ⟨9, _⟩ => 1
  | ⟨10, _⟩ => 1
  | ⟨11, _⟩ => 1
  | ⟨12, _⟩ => 1
  | ⟨13, _⟩ => 1
  | ⟨14, _⟩ => 1

def o237ScalarCoverB (i : Fin 15) (x0 x1 x2 x3 : F2) : Bool :=
  match i with
  | ⟨0, _⟩ => decide (((x1 = 0 ∧ x2 = 0) ∧ x3 = 0))
  | ⟨1, _⟩ => decide (((x0 = 0 ∧ x1 + x3 = 0) ∧ x2 = 0))
  | ⟨2, _⟩ => decide (((x0 + x2 = 0 ∧ x1 + x2 = 0) ∧ x3 = 0))
  | ⟨3, _⟩ => decide (((x0 + x3 = 0 ∧ x1 + x3 = 0) ∧ x2 + x3 = 0))
  | ⟨4, _⟩ => decide (((x0 = 0 ∧ x1 + x3 = 0) ∧ x2 + x3 = 0))
  | ⟨5, _⟩ => decide (((x0 + x3 = 0 ∧ x1 = 0) ∧ x2 + x3 = 0))
  | ⟨6, _⟩ => decide (((x0 + x1 = 0 ∧ x2 = 0) ∧ x3 = 0))
  | ⟨7, _⟩ => decide (((x0 = 0 ∧ x1 = 0) ∧ x2 = 0))
  | ⟨8, _⟩ => decide (((x0 + x3 = 0 ∧ x1 + x3 = 0) ∧ x2 = 0))
  | ⟨9, _⟩ => decide (((x0 = 0 ∧ x2 = 0) ∧ x3 = 0))
  | ⟨10, _⟩ => decide (((x0 + x3 = 0 ∧ x1 = 0) ∧ x2 = 0))
  | ⟨11, _⟩ => decide (((x0 = 0 ∧ x1 = 0) ∧ x3 = 0))
  | ⟨12, _⟩ => decide (((x0 = 0 ∧ x1 = 0) ∧ x2 + x3 = 0))
  | ⟨13, _⟩ => decide (((x0 = 0 ∧ x1 + x2 = 0) ∧ x3 = 0))
  | ⟨14, _⟩ => decide (((x0 + x2 = 0 ∧ x1 = 0) ∧ x3 = 0))

def o237Cover (i : Fin 15) (M : Mat3) : Prop :=
  o237ScalarCoverB i (evalFunc (o237Basis 0) M) (evalFunc (o237Basis 1) M) (evalFunc (o237Basis 2) M) (evalFunc (o237Basis 3) M) = true

theorem o237ScalarCoverage :
    ∀ (x0 x1 x2 x3 : F2), 1 ≤
    ∑ i : Fin 15, if o237ScalarCoverB i x0 x1 x2 x3 = true then o237Lambda i else 0 := by
  intro x0 x1 x2 x3
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;> decide

theorem o237MatCoverage (M : Mat3) :
    1 ≤ ∑ i : Fin 15, if o237Cover i M then o237Lambda i else 0 := by
  have h := o237ScalarCoverage
    (evalFunc (o237Basis 0) M) (evalFunc (o237Basis 1) M) (evalFunc (o237Basis 2) M) (evalFunc (o237Basis 3) M)
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o237ScalarCoverB i (evalFunc (o237Basis 0) M) (evalFunc (o237Basis 1) M) (evalFunc (o237Basis 2) M) (evalFunc (o237Basis 3) M) <;>
    simp [o237Cover, hb]

private lemma mem_kerEvalFunc_iff237 {L M : Mat3} :
    M ∈ kerEvalFunc L ↔ evalFunc L M = 0 := Iff.rfl

theorem o237W_le_source (i : Fin 15) : o237W ≤ o237SourceU i := by
  intro M hM
  fin_cases i <;> simp only [o237W, o237SourceU, o237Basis]
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 138) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 96) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 20) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 258) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 158) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 96) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 354) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 234) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 20) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 278) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 158) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 116) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 258) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 158) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 116) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 278) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 138) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 116) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 392) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 96) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 20) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 258) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 138) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 96) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 278) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 158) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 96) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 258) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 96) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 20) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 278) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 138) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 96) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 258) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 138) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 20) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 258) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 138) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 116) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 258) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 234) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 20) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 354) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 138) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 20) [266, 136, 96, 20, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩

theorem o237CoverSound (i : Fin 15) (M : Mat3) (h : o237Cover i M) : M ∈ o237SourceU i := by
  fin_cases i <;>
    simp only [o237Cover, o237ScalarCoverB, o237SourceU, o237Basis, Submodule.mem_inf,
               mem_kerEvalFunc_iff237, evalFunc_add_left] at h ⊢ <;>
    exact of_decide_eq_true h

private theorem o237Cert : ((∑ i : Fin 15, o237Lambda i) - 1) * 15 < ∑ i : Fin 15, o237Lambda i * o237SourceLb i := by
  simp only [o237Lambda, o237SourceLb]; decide
private theorem o237LambdaSum : 1 ≤ ∑ i : Fin 15, o237Lambda i := by
  simp only [o237Lambda]; decide

theorem o237Lb16
    (hSource : ∀ i : Fin 15, QuotientRankAtLeast (o237SourceU i) (o237SourceLb i)) :
    QuotientRankAtLeast o237W 16 :=
  quotientRankAtLeast_of_contradiction o237W 16 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o237SourceU o237SourceLb
      o237Lambda 1 15
      o237Cover o237W_le_source hSource
      o237LambdaSum o237CoverSound
      (fun M => o237MatCoverage M) (by omega) o237Cert D)

end QiushiMatmul
