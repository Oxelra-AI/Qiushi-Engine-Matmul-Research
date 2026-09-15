import QiushiDirectCoverage
import QiushiFlattenSeeds
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiOrbit8Closed

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix Classical
namespace QiushiMatmul

def o217W : Submodule F2 Mat3 := spanCodes [308, 132, 96, 10, 1]
def o217Basis : Fin 4 → Mat3
  | ⟨0, _⟩ => codeMat 272
  | ⟨1, _⟩ => codeMat 148
  | ⟨2, _⟩ => codeMat 112
  | ⟨3, _⟩ => codeMat 10

def o217SourceU : Fin 12 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 272) ⊓ kerEvalFunc (codeMat 148 + codeMat 112) ⊓ kerEvalFunc (codeMat 10)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 272) ⊓ kerEvalFunc (codeMat 148 + codeMat 10) ⊓ kerEvalFunc (codeMat 112 + codeMat 10)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 272) ⊓ kerEvalFunc (codeMat 112) ⊓ kerEvalFunc (codeMat 10)
  | ⟨3, _⟩ => kerEvalFunc (codeMat 272 + codeMat 112) ⊓ kerEvalFunc (codeMat 148) ⊓ kerEvalFunc (codeMat 10)
  | ⟨4, _⟩ => kerEvalFunc (codeMat 272) ⊓ kerEvalFunc (codeMat 148) ⊓ kerEvalFunc (codeMat 10)
  | ⟨5, _⟩ => kerEvalFunc (codeMat 272 + codeMat 148) ⊓ kerEvalFunc (codeMat 112) ⊓ kerEvalFunc (codeMat 10)
  | ⟨6, _⟩ => kerEvalFunc (codeMat 272 + codeMat 112) ⊓ kerEvalFunc (codeMat 148 + codeMat 112)
  | ⟨7, _⟩ => kerEvalFunc (codeMat 272) ⊓ kerEvalFunc (codeMat 148 + codeMat 112 + codeMat 10)
  | ⟨8, _⟩ => kerEvalFunc (codeMat 148) ⊓ kerEvalFunc (codeMat 112 + codeMat 10)
  | ⟨9, _⟩ => kerEvalFunc (codeMat 148 + codeMat 10) ⊓ kerEvalFunc (codeMat 112)
  | ⟨10, _⟩ => kerEvalFunc (codeMat 272 + codeMat 10) ⊓ kerEvalFunc (codeMat 148)
  | ⟨11, _⟩ => kerEvalFunc (codeMat 272 + codeMat 10) ⊓ kerEvalFunc (codeMat 112)
def o217SourceLb : Fin 12 → ℕ
  | ⟨0, _⟩ => 15
  | ⟨1, _⟩ => 15
  | ⟨2, _⟩ => 14
  | ⟨3, _⟩ => 14
  | ⟨4, _⟩ => 14
  | ⟨5, _⟩ => 14
  | ⟨6, _⟩ => 12
  | ⟨7, _⟩ => 12
  | ⟨8, _⟩ => 12
  | ⟨9, _⟩ => 12
  | ⟨10, _⟩ => 12
  | ⟨11, _⟩ => 12
def o217Lambda : Fin 12 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 2
  | ⟨4, _⟩ => 1
  | ⟨5, _⟩ => 2
  | ⟨6, _⟩ => 2
  | ⟨7, _⟩ => 1
  | ⟨8, _⟩ => 1
  | ⟨9, _⟩ => 1
  | ⟨10, _⟩ => 1
  | ⟨11, _⟩ => 1

def o217ScalarCoverB (i : Fin 12) (x0 x1 x2 x3 : F2) : Bool :=
  match i with
  | ⟨0, _⟩ => decide (((x0 = 0 ∧ x1 + x2 = 0) ∧ x3 = 0))
  | ⟨1, _⟩ => decide (((x0 = 0 ∧ x1 + x3 = 0) ∧ x2 + x3 = 0))
  | ⟨2, _⟩ => decide (((x0 = 0 ∧ x2 = 0) ∧ x3 = 0))
  | ⟨3, _⟩ => decide (((x0 + x2 = 0 ∧ x1 = 0) ∧ x3 = 0))
  | ⟨4, _⟩ => decide (((x0 = 0 ∧ x1 = 0) ∧ x3 = 0))
  | ⟨5, _⟩ => decide (((x0 + x1 = 0 ∧ x2 = 0) ∧ x3 = 0))
  | ⟨6, _⟩ => decide ((x0 + x2 = 0 ∧ x1 + x2 = 0))
  | ⟨7, _⟩ => decide ((x0 = 0 ∧ x1 + x2 + x3 = 0))
  | ⟨8, _⟩ => decide ((x1 = 0 ∧ x2 + x3 = 0))
  | ⟨9, _⟩ => decide ((x1 + x3 = 0 ∧ x2 = 0))
  | ⟨10, _⟩ => decide ((x0 + x3 = 0 ∧ x1 = 0))
  | ⟨11, _⟩ => decide ((x0 + x3 = 0 ∧ x2 = 0))

def o217Cover (i : Fin 12) (M : Mat3) : Prop :=
  o217ScalarCoverB i (evalFunc (o217Basis 0) M) (evalFunc (o217Basis 1) M) (evalFunc (o217Basis 2) M) (evalFunc (o217Basis 3) M) = true

theorem o217ScalarCoverage :
    ∀ (x0 x1 x2 x3 : F2), 2 ≤
    ∑ i : Fin 12, if o217ScalarCoverB i x0 x1 x2 x3 = true then o217Lambda i else 0 := by
  intro x0 x1 x2 x3
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;> decide

theorem o217MatCoverage (M : Mat3) :
    2 ≤ ∑ i : Fin 12, if o217Cover i M then o217Lambda i else 0 := by
  have h := o217ScalarCoverage
    (evalFunc (o217Basis 0) M) (evalFunc (o217Basis 1) M) (evalFunc (o217Basis 2) M) (evalFunc (o217Basis 3) M)
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o217ScalarCoverB i (evalFunc (o217Basis 0) M) (evalFunc (o217Basis 1) M) (evalFunc (o217Basis 2) M) (evalFunc (o217Basis 3) M) <;>
    simp [o217Cover, hb]

private lemma mem_kerEvalFunc_iff217 {L M : Mat3} :
    M ∈ kerEvalFunc L ↔ evalFunc L M = 0 := Iff.rfl

theorem o217W_le_source (i : Fin 12) : o217W ≤ o217SourceU i := by
  intro M hM
  fin_cases i <;> simp only [o217W, o217SourceU, o217Basis]
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 272) [308, 132, 96, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 228) [308, 132, 96, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 10) [308, 132, 96, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 272) [308, 132, 96, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 158) [308, 132, 96, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 122) [308, 132, 96, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 272) [308, 132, 96, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 112) [308, 132, 96, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 10) [308, 132, 96, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 352) [308, 132, 96, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 148) [308, 132, 96, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 10) [308, 132, 96, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 272) [308, 132, 96, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 148) [308, 132, 96, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 10) [308, 132, 96, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 388) [308, 132, 96, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 112) [308, 132, 96, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 10) [308, 132, 96, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 352) [308, 132, 96, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 228) [308, 132, 96, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 272) [308, 132, 96, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 238) [308, 132, 96, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 148) [308, 132, 96, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 122) [308, 132, 96, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 158) [308, 132, 96, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 112) [308, 132, 96, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 282) [308, 132, 96, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 148) [308, 132, 96, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 282) [308, 132, 96, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 112) [308, 132, 96, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩

theorem o217CoverSound (i : Fin 12) (M : Mat3) (h : o217Cover i M) : M ∈ o217SourceU i := by
  fin_cases i <;>
    simp only [o217Cover, o217ScalarCoverB, o217SourceU, o217Basis, Submodule.mem_inf,
               mem_kerEvalFunc_iff217, evalFunc_add_left] at h ⊢ <;>
    exact of_decide_eq_true h

private theorem o217Cert : ((∑ i : Fin 12, o217Lambda i) - 2) * 15 < ∑ i : Fin 12, o217Lambda i * o217SourceLb i := by
  simp only [o217Lambda, o217SourceLb]; decide
private theorem o217LambdaSum : 2 ≤ ∑ i : Fin 12, o217Lambda i := by
  simp only [o217Lambda]; decide

theorem o217Lb16
    (hSource : ∀ i : Fin 12, QuotientRankAtLeast (o217SourceU i) (o217SourceLb i)) :
    QuotientRankAtLeast o217W 16 :=
  quotientRankAtLeast_of_contradiction o217W 16 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o217SourceU o217SourceLb
      o217Lambda 2 15
      o217Cover o217W_le_source hSource
      o217LambdaSum o217CoverSound
      (fun M => o217MatCoverage M) (by omega) o217Cert D)

end QiushiMatmul
