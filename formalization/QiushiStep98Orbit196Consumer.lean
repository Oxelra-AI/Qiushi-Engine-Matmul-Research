import QiushiDirectCoverage
import QiushiFlattenSeeds
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiOrbit8Closed

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix Classical
namespace QiushiMatmul

def o196W : Submodule F2 Mat3 := spanCodes [278, 132, 32, 10, 1]
def o196Basis : Fin 4 → Mat3
  | ⟨0, _⟩ => codeMat 266
  | ⟨1, _⟩ => codeMat 142
  | ⟨2, _⟩ => codeMat 64
  | ⟨3, _⟩ => codeMat 26

def o196SourceU : Fin 10 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 266) ⊓ kerEvalFunc (codeMat 142 + codeMat 64) ⊓ kerEvalFunc (codeMat 26)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 266 + codeMat 26) ⊓ kerEvalFunc (codeMat 142) ⊓ kerEvalFunc (codeMat 64 + codeMat 26)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 266 + codeMat 26) ⊓ kerEvalFunc (codeMat 142) ⊓ kerEvalFunc (codeMat 64)
  | ⟨3, _⟩ => kerEvalFunc (codeMat 142) ⊓ kerEvalFunc (codeMat 64) ⊓ kerEvalFunc (codeMat 26)
  | ⟨4, _⟩ => kerEvalFunc (codeMat 266) ⊓ kerEvalFunc (codeMat 142) ⊓ kerEvalFunc (codeMat 26)
  | ⟨5, _⟩ => kerEvalFunc (codeMat 266) ⊓ kerEvalFunc (codeMat 142 + codeMat 26) ⊓ kerEvalFunc (codeMat 64 + codeMat 26)
  | ⟨6, _⟩ => kerEvalFunc (codeMat 266 + codeMat 64) ⊓ kerEvalFunc (codeMat 142) ⊓ kerEvalFunc (codeMat 26)
  | ⟨7, _⟩ => kerEvalFunc (codeMat 266) ⊓ kerEvalFunc (codeMat 64)
  | ⟨8, _⟩ => kerEvalFunc (codeMat 266 + codeMat 142) ⊓ kerEvalFunc (codeMat 64 + codeMat 26)
  | ⟨9, _⟩ => kerEvalFunc (codeMat 266 + codeMat 64 + codeMat 26) ⊓ kerEvalFunc (codeMat 142 + codeMat 64 + codeMat 26)
def o196SourceLb : Fin 10 → ℕ
  | ⟨0, _⟩ => 15
  | ⟨1, _⟩ => 15
  | ⟨2, _⟩ => 14
  | ⟨3, _⟩ => 14
  | ⟨4, _⟩ => 14
  | ⟨5, _⟩ => 14
  | ⟨6, _⟩ => 14
  | ⟨7, _⟩ => 12
  | ⟨8, _⟩ => 12
  | ⟨9, _⟩ => 12
def o196Lambda : Fin 10 → ℕ
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

def o196ScalarCoverB (i : Fin 10) (x0 x1 x2 x3 : F2) : Bool :=
  match i with
  | ⟨0, _⟩ => decide (((x0 = 0 ∧ x1 + x2 = 0) ∧ x3 = 0))
  | ⟨1, _⟩ => decide (((x0 + x3 = 0 ∧ x1 = 0) ∧ x2 + x3 = 0))
  | ⟨2, _⟩ => decide (((x0 + x3 = 0 ∧ x1 = 0) ∧ x2 = 0))
  | ⟨3, _⟩ => decide (((x1 = 0 ∧ x2 = 0) ∧ x3 = 0))
  | ⟨4, _⟩ => decide (((x0 = 0 ∧ x1 = 0) ∧ x3 = 0))
  | ⟨5, _⟩ => decide (((x0 = 0 ∧ x1 + x3 = 0) ∧ x2 + x3 = 0))
  | ⟨6, _⟩ => decide (((x0 + x2 = 0 ∧ x1 = 0) ∧ x3 = 0))
  | ⟨7, _⟩ => decide ((x0 = 0 ∧ x2 = 0))
  | ⟨8, _⟩ => decide ((x0 + x1 = 0 ∧ x2 + x3 = 0))
  | ⟨9, _⟩ => decide ((x0 + x2 + x3 = 0 ∧ x1 + x2 + x3 = 0))

def o196Cover (i : Fin 10) (M : Mat3) : Prop :=
  o196ScalarCoverB i (evalFunc (o196Basis 0) M) (evalFunc (o196Basis 1) M) (evalFunc (o196Basis 2) M) (evalFunc (o196Basis 3) M) = true

theorem o196ScalarCoverage :
    ∀ (x0 x1 x2 x3 : F2), 1 ≤
    ∑ i : Fin 10, if o196ScalarCoverB i x0 x1 x2 x3 = true then o196Lambda i else 0 := by
  intro x0 x1 x2 x3
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;> decide

theorem o196MatCoverage (M : Mat3) :
    1 ≤ ∑ i : Fin 10, if o196Cover i M then o196Lambda i else 0 := by
  have h := o196ScalarCoverage
    (evalFunc (o196Basis 0) M) (evalFunc (o196Basis 1) M) (evalFunc (o196Basis 2) M) (evalFunc (o196Basis 3) M)
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o196ScalarCoverB i (evalFunc (o196Basis 0) M) (evalFunc (o196Basis 1) M) (evalFunc (o196Basis 2) M) (evalFunc (o196Basis 3) M) <;>
    simp [o196Cover, hb]

private lemma mem_kerEvalFunc_iff196 {L M : Mat3} :
    M ∈ kerEvalFunc L ↔ evalFunc L M = 0 := Iff.rfl

theorem o196W_le_source (i : Fin 10) : o196W ≤ o196SourceU i := by
  intro M hM
  fin_cases i <;> simp only [o196W, o196SourceU, o196Basis]
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 266) [278, 132, 32, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 206) [278, 132, 32, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 26) [278, 132, 32, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 272) [278, 132, 32, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 142) [278, 132, 32, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 90) [278, 132, 32, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 272) [278, 132, 32, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 142) [278, 132, 32, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 64) [278, 132, 32, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 142) [278, 132, 32, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 64) [278, 132, 32, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 26) [278, 132, 32, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 266) [278, 132, 32, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 142) [278, 132, 32, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 26) [278, 132, 32, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 266) [278, 132, 32, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 148) [278, 132, 32, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 90) [278, 132, 32, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 330) [278, 132, 32, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 142) [278, 132, 32, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 26) [278, 132, 32, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 266) [278, 132, 32, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 64) [278, 132, 32, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 388) [278, 132, 32, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 90) [278, 132, 32, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 336) [278, 132, 32, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 212) [278, 132, 32, 10, 1] (fun n hn => by fin_cases hn <;> decide) hM⟩

theorem o196CoverSound (i : Fin 10) (M : Mat3) (h : o196Cover i M) : M ∈ o196SourceU i := by
  fin_cases i <;>
    simp only [o196Cover, o196ScalarCoverB, o196SourceU, o196Basis, Submodule.mem_inf,
               mem_kerEvalFunc_iff196, evalFunc_add_left] at h ⊢ <;>
    exact of_decide_eq_true h

private theorem o196Cert : ((∑ i : Fin 10, o196Lambda i) - 1) * 15 < ∑ i : Fin 10, o196Lambda i * o196SourceLb i := by
  simp only [o196Lambda, o196SourceLb]; decide
private theorem o196LambdaSum : 1 ≤ ∑ i : Fin 10, o196Lambda i := by
  simp only [o196Lambda]; decide

theorem o196Lb16
    (hSource : ∀ i : Fin 10, QuotientRankAtLeast (o196SourceU i) (o196SourceLb i)) :
    QuotientRankAtLeast o196W 16 :=
  quotientRankAtLeast_of_contradiction o196W 16 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o196SourceU o196SourceLb
      o196Lambda 1 15
      o196Cover o196W_le_source hSource
      o196LambdaSum o196CoverSound
      (fun M => o196MatCoverage M) (by omega) o196Cert D)

end QiushiMatmul
