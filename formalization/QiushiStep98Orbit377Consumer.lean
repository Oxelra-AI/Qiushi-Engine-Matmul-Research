import QiushiDirectCoverage
import QiushiFlattenSeeds
import QiushiOrbit29FP
import QiushiOrbit8Closed

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix Classical
namespace QiushiMatmul

def o377W : Submodule F2 Mat3 := spanCodes [161, 68, 19, 10]
def o377Basis : Fin 5 → Mat3
  | ⟨0, _⟩ => codeMat 256
  | ⟨1, _⟩ => codeMat 139
  | ⟨2, _⟩ => codeMat 68
  | ⟨3, _⟩ => codeMat 43
  | ⟨4, _⟩ => codeMat 26

def o377SourceU : Fin 14 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 256) ⊓ kerEvalFunc (codeMat 139 + codeMat 43) ⊓ kerEvalFunc (codeMat 68)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 256 + codeMat 68) ⊓ kerEvalFunc (codeMat 139) ⊓ kerEvalFunc (codeMat 43) ⊓ kerEvalFunc (codeMat 26)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 139 + codeMat 43) ⊓ kerEvalFunc (codeMat 68 + codeMat 43) ⊓ kerEvalFunc (codeMat 26)
  | ⟨3, _⟩ => kerEvalFunc (codeMat 256 + codeMat 43) ⊓ kerEvalFunc (codeMat 139 + codeMat 43) ⊓ kerEvalFunc (codeMat 26)
  | ⟨4, _⟩ => kerEvalFunc (codeMat 256 + codeMat 43) ⊓ kerEvalFunc (codeMat 139 + codeMat 43) ⊓ kerEvalFunc (codeMat 68 + codeMat 43 + codeMat 26)
  | ⟨5, _⟩ => kerEvalFunc (codeMat 256 + codeMat 43 + codeMat 26) ⊓ kerEvalFunc (codeMat 139 + codeMat 43) ⊓ kerEvalFunc (codeMat 68 + codeMat 43)
  | ⟨6, _⟩ => kerEvalFunc (codeMat 256 + codeMat 43) ⊓ kerEvalFunc (codeMat 139 + codeMat 26) ⊓ kerEvalFunc (codeMat 68 + codeMat 26)
  | ⟨7, _⟩ => kerEvalFunc (codeMat 256 + codeMat 139) ⊓ kerEvalFunc (codeMat 68 + codeMat 26) ⊓ kerEvalFunc (codeMat 43 + codeMat 26)
  | ⟨8, _⟩ => kerEvalFunc (codeMat 256 + codeMat 26) ⊓ kerEvalFunc (codeMat 139 + codeMat 26) ⊓ kerEvalFunc (codeMat 68 + codeMat 43)
  | ⟨9, _⟩ => kerEvalFunc (codeMat 256 + codeMat 26) ⊓ kerEvalFunc (codeMat 139 + codeMat 68) ⊓ kerEvalFunc (codeMat 43 + codeMat 26)
  | ⟨10, _⟩ => kerEvalFunc (codeMat 256 + codeMat 43 + codeMat 26) ⊓ kerEvalFunc (codeMat 139) ⊓ kerEvalFunc (codeMat 68 + codeMat 43 + codeMat 26)
  | ⟨11, _⟩ => kerEvalFunc (codeMat 256 + codeMat 68) ⊓ kerEvalFunc (codeMat 139 + codeMat 68 + codeMat 26) ⊓ kerEvalFunc (codeMat 43)
  | ⟨12, _⟩ => kerEvalFunc (codeMat 256 + codeMat 26) ⊓ kerEvalFunc (codeMat 68 + codeMat 26) ⊓ kerEvalFunc (codeMat 43)
  | ⟨13, _⟩ => kerEvalFunc (codeMat 256 + codeMat 26) ⊓ kerEvalFunc (codeMat 139) ⊓ kerEvalFunc (codeMat 68 + codeMat 26)
def o377SourceLb : Fin 14 → ℕ
  | ⟨0, _⟩ => 15
  | ⟨1, _⟩ => 15
  | ⟨2, _⟩ => 15
  | ⟨3, _⟩ => 15
  | ⟨4, _⟩ => 15
  | ⟨5, _⟩ => 15
  | ⟨6, _⟩ => 15
  | ⟨7, _⟩ => 15
  | ⟨8, _⟩ => 15
  | ⟨9, _⟩ => 15
  | ⟨10, _⟩ => 15
  | ⟨11, _⟩ => 15
  | ⟨12, _⟩ => 15
  | ⟨13, _⟩ => 15
def o377Lambda : Fin 14 → ℕ
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

def o377ScalarCoverB (i : Fin 14) (x0 x1 x2 x3 x4 : F2) : Bool :=
  match i with
  | ⟨0, _⟩ => decide (((x0 = 0 ∧ x1 + x3 = 0) ∧ x2 = 0))
  | ⟨1, _⟩ => decide ((((x0 + x2 = 0 ∧ x1 = 0) ∧ x3 = 0) ∧ x4 = 0))
  | ⟨2, _⟩ => decide (((x1 + x3 = 0 ∧ x2 + x3 = 0) ∧ x4 = 0))
  | ⟨3, _⟩ => decide (((x0 + x3 = 0 ∧ x1 + x3 = 0) ∧ x4 = 0))
  | ⟨4, _⟩ => decide (((x0 + x3 = 0 ∧ x1 + x3 = 0) ∧ x2 + x3 + x4 = 0))
  | ⟨5, _⟩ => decide (((x0 + x3 + x4 = 0 ∧ x1 + x3 = 0) ∧ x2 + x3 = 0))
  | ⟨6, _⟩ => decide (((x0 + x3 = 0 ∧ x1 + x4 = 0) ∧ x2 + x4 = 0))
  | ⟨7, _⟩ => decide (((x0 + x1 = 0 ∧ x2 + x4 = 0) ∧ x3 + x4 = 0))
  | ⟨8, _⟩ => decide (((x0 + x4 = 0 ∧ x1 + x4 = 0) ∧ x2 + x3 = 0))
  | ⟨9, _⟩ => decide (((x0 + x4 = 0 ∧ x1 + x2 = 0) ∧ x3 + x4 = 0))
  | ⟨10, _⟩ => decide (((x0 + x3 + x4 = 0 ∧ x1 = 0) ∧ x2 + x3 + x4 = 0))
  | ⟨11, _⟩ => decide (((x0 + x2 = 0 ∧ x1 + x2 + x4 = 0) ∧ x3 = 0))
  | ⟨12, _⟩ => decide (((x0 + x4 = 0 ∧ x2 + x4 = 0) ∧ x3 = 0))
  | ⟨13, _⟩ => decide (((x0 + x4 = 0 ∧ x1 = 0) ∧ x2 + x4 = 0))

def o377Cover (i : Fin 14) (M : Mat3) : Prop :=
  o377ScalarCoverB i (evalFunc (o377Basis 0) M) (evalFunc (o377Basis 1) M) (evalFunc (o377Basis 2) M) (evalFunc (o377Basis 3) M) (evalFunc (o377Basis 4) M) = true

theorem o377ScalarCoverage :
    ∀ (x0 x1 x2 x3 x4 : F2), 1 ≤
    ∑ i : Fin 14, if o377ScalarCoverB i x0 x1 x2 x3 x4 = true then o377Lambda i else 0 := by
  intro x0 x1 x2 x3 x4
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;> fin_cases x4 <;> decide

theorem o377MatCoverage (M : Mat3) :
    1 ≤ ∑ i : Fin 14, if o377Cover i M then o377Lambda i else 0 := by
  have h := o377ScalarCoverage
    (evalFunc (o377Basis 0) M) (evalFunc (o377Basis 1) M) (evalFunc (o377Basis 2) M) (evalFunc (o377Basis 3) M) (evalFunc (o377Basis 4) M)
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o377ScalarCoverB i (evalFunc (o377Basis 0) M) (evalFunc (o377Basis 1) M) (evalFunc (o377Basis 2) M) (evalFunc (o377Basis 3) M) (evalFunc (o377Basis 4) M) <;>
    simp [o377Cover, hb]

private lemma mem_kerEvalFunc_iff377 {L M : Mat3} :
    M ∈ kerEvalFunc L ↔ evalFunc L M = 0 := Iff.rfl

theorem o377W_le_source (i : Fin 14) : o377W ≤ o377SourceU i := by
  intro M hM
  fin_cases i <;> simp only [o377W, o377SourceU, o377Basis]
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 256) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 160) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 68) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 324) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 139) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 43) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 26) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 160) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 111) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 26) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 299) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 160) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 26) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 299) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 160) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 117) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 305) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 160) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 111) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 299) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 145) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 94) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 395) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 94) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 49) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 282) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 145) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 111) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 282) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 207) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 49) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 305) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 139) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 117) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 324) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 213) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 43) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 282) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 94) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 43) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 282) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 139) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 94) [161, 68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩

theorem o377CoverSound (i : Fin 14) (M : Mat3) (h : o377Cover i M) : M ∈ o377SourceU i := by
  fin_cases i <;>
    simp only [o377Cover, o377ScalarCoverB, o377SourceU, o377Basis, Submodule.mem_inf,
               mem_kerEvalFunc_iff377, evalFunc_add_left] at h ⊢ <;>
    exact of_decide_eq_true h

private theorem o377Cert : ((∑ i : Fin 14, o377Lambda i) - 1) * 16 < ∑ i : Fin 14, o377Lambda i * o377SourceLb i := by
  simp only [o377Lambda, o377SourceLb]; decide
private theorem o377LambdaSum : 1 ≤ ∑ i : Fin 14, o377Lambda i := by
  simp only [o377Lambda]; decide

theorem o377Lb17
    (hSource : ∀ i : Fin 14, QuotientRankAtLeast (o377SourceU i) (o377SourceLb i)) :
    QuotientRankAtLeast o377W 17 :=
  quotientRankAtLeast_of_contradiction o377W 17 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o377SourceU o377SourceLb
      o377Lambda 1 16
      o377Cover o377W_le_source hSource
      o377LambdaSum o377CoverSound
      (fun M => o377MatCoverage M) (by omega) o377Cert D)

end QiushiMatmul
