import QiushiDirectCoverage
import QiushiFlattenSeeds
import QiushiStep104Orbit279Split
import QiushiStep107Orbit373Extraction
import QiushiStep99Orbit377Dispatch

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

def o450W : Submodule F2 Mat3 := spanCodes [68, 19, 10]
def o450Basis : Fin 6 → Mat3
  | ⟨0, _⟩ => codeMat 32
  | ⟨1, _⟩ => codeMat 128
  | ⟨2, _⟩ => codeMat 256
  | ⟨3, _⟩ => codeMat 17
  | ⟨4, _⟩ => codeMat 68
  | ⟨5, _⟩ => codeMat 11

def o450SourceU : Fin 18 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 256) ⊓ kerEvalFunc (codeMat 68) ⊓ kerEvalFunc (codeMat 17 + codeMat 11)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 256) ⊓ kerEvalFunc (codeMat 68) ⊓ kerEvalFunc (codeMat 32 + codeMat 128) ⊓ kerEvalFunc (codeMat 17 + codeMat 11) ⊓ kerEvalFunc (codeMat 32 + codeMat 17)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 17) ⊓ kerEvalFunc (codeMat 68) ⊓ kerEvalFunc (codeMat 32 + codeMat 256) ⊓ kerEvalFunc (codeMat 11)
  | ⟨3, _⟩ => kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 68) ⊓ kerEvalFunc (codeMat 32 + codeMat 256) ⊓ kerEvalFunc (codeMat 11) ⊓ kerEvalFunc (codeMat 32 + codeMat 17)
  | ⟨4, _⟩ => kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 17) ⊓ kerEvalFunc (codeMat 32 + codeMat 256) ⊓ kerEvalFunc (codeMat 11) ⊓ kerEvalFunc (codeMat 32 + codeMat 68)
  | ⟨5, _⟩ => kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 17) ⊓ kerEvalFunc (codeMat 32 + codeMat 256) ⊓ kerEvalFunc (codeMat 32 + codeMat 68) ⊓ kerEvalFunc (codeMat 32 + codeMat 11)
  | ⟨6, _⟩ => kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 17) ⊓ kerEvalFunc (codeMat 68) ⊓ kerEvalFunc (codeMat 128 + codeMat 256) ⊓ kerEvalFunc (codeMat 11)
  | ⟨7, _⟩ => kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 68) ⊓ kerEvalFunc (codeMat 128 + codeMat 256) ⊓ kerEvalFunc (codeMat 11) ⊓ kerEvalFunc (codeMat 128 + codeMat 17)
  | ⟨8, _⟩ => kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 17) ⊓ kerEvalFunc (codeMat 128 + codeMat 256) ⊓ kerEvalFunc (codeMat 11) ⊓ kerEvalFunc (codeMat 128 + codeMat 68)
  | ⟨9, _⟩ => kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 17) ⊓ kerEvalFunc (codeMat 128 + codeMat 256) ⊓ kerEvalFunc (codeMat 128 + codeMat 68) ⊓ kerEvalFunc (codeMat 128 + codeMat 11)
  | ⟨10, _⟩ => kerEvalFunc (codeMat 32 + codeMat 128 + codeMat 17)
  | ⟨11, _⟩ => kerEvalFunc (codeMat 32 + codeMat 128 + codeMat 256 + codeMat 17 + codeMat 68)
  | ⟨12, _⟩ => kerEvalFunc (codeMat 256 + codeMat 11)
  | ⟨13, _⟩ => kerEvalFunc (codeMat 32 + codeMat 128 + codeMat 68 + codeMat 11)
  | ⟨14, _⟩ => kerEvalFunc (codeMat 256 + codeMat 68 + codeMat 11)
  | ⟨15, _⟩ => kerEvalFunc (codeMat 32 + codeMat 128 + codeMat 11)
  | ⟨16, _⟩ => kerEvalFunc (codeMat 17 + codeMat 68)
  | ⟨17, _⟩ => kerEvalFunc (codeMat 256 + codeMat 17)
  | ⟨n + 18, h⟩ => absurd h (by omega)

def o450SourceLb : Fin 18 → ℕ
  | ⟨n, _⟩ => [17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 9, 9, 9, 9, 9, 9, 9, 9].getD n 0

def o450Lambda : Fin 18 → ℕ
  | ⟨n, _⟩ => [4, 4, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1].getD n 0

def o450ScalarCoverB (i : Fin 18) (x0 x1 x2 x3 x4 x5 : F2) : Bool :=
  match i with
  | ⟨0, _⟩ => decide (((((x0 = 0 ∧ x1 = 0) ∧ x2 = 0) ∧ x4 = 0) ∧ x3 + x5 = 0))
  | ⟨1, _⟩ => decide (((((x2 = 0 ∧ x4 = 0) ∧ x0 + x1 = 0) ∧ x3 + x5 = 0) ∧ x0 + x3 = 0))
  | ⟨2, _⟩ => decide (((((x1 = 0 ∧ x3 = 0) ∧ x4 = 0) ∧ x0 + x2 = 0) ∧ x5 = 0))
  | ⟨3, _⟩ => decide (((((x1 = 0 ∧ x4 = 0) ∧ x0 + x2 = 0) ∧ x5 = 0) ∧ x0 + x3 = 0))
  | ⟨4, _⟩ => decide (((((x1 = 0 ∧ x3 = 0) ∧ x0 + x2 = 0) ∧ x5 = 0) ∧ x0 + x4 = 0))
  | ⟨5, _⟩ => decide (((((x1 = 0 ∧ x3 = 0) ∧ x0 + x2 = 0) ∧ x0 + x4 = 0) ∧ x0 + x5 = 0))
  | ⟨6, _⟩ => decide (((((x0 = 0 ∧ x3 = 0) ∧ x4 = 0) ∧ x1 + x2 = 0) ∧ x5 = 0))
  | ⟨7, _⟩ => decide (((((x0 = 0 ∧ x4 = 0) ∧ x1 + x2 = 0) ∧ x5 = 0) ∧ x1 + x3 = 0))
  | ⟨8, _⟩ => decide (((((x0 = 0 ∧ x3 = 0) ∧ x1 + x2 = 0) ∧ x5 = 0) ∧ x1 + x4 = 0))
  | ⟨9, _⟩ => decide (((((x0 = 0 ∧ x3 = 0) ∧ x1 + x2 = 0) ∧ x1 + x4 = 0) ∧ x1 + x5 = 0))
  | ⟨10, _⟩ => decide (x0 + x1 + x3 = 0)
  | ⟨11, _⟩ => decide (x0 + x1 + x2 + x3 + x4 = 0)
  | ⟨12, _⟩ => decide (x2 + x5 = 0)
  | ⟨13, _⟩ => decide (x0 + x1 + x4 + x5 = 0)
  | ⟨14, _⟩ => decide (x2 + x4 + x5 = 0)
  | ⟨15, _⟩ => decide (x0 + x1 + x5 = 0)
  | ⟨16, _⟩ => decide (x3 + x4 = 0)
  | ⟨17, _⟩ => decide (x2 + x3 = 0)
  | ⟨n + 18, h⟩ => absurd h (by omega)

def o450Cover (i : Fin 18) (M : Mat3) : Prop :=
  o450ScalarCoverB i (evalFunc (o450Basis 0) M) (evalFunc (o450Basis 1) M) (evalFunc (o450Basis 2) M) (evalFunc (o450Basis 3) M) (evalFunc (o450Basis 4) M) (evalFunc (o450Basis 5) M) = true

theorem o450ScalarCoverage :
    ∀ (x0 x1 x2 x3 x4 x5 : F2), 4 ≤
    ∑ i : Fin 18, if o450ScalarCoverB i x0 x1 x2 x3 x4 x5 = true then o450Lambda i else 0 := by
  intro x0 x1 x2 x3 x4 x5
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;> fin_cases x4 <;> fin_cases x5 <;> decide

theorem o450MatCoverage (M : Mat3) :
    4 ≤ ∑ i : Fin 18, if o450Cover i M then o450Lambda i else 0 := by
  have h := o450ScalarCoverage
    (evalFunc (o450Basis 0) M) (evalFunc (o450Basis 1) M) (evalFunc (o450Basis 2) M) (evalFunc (o450Basis 3) M) (evalFunc (o450Basis 4) M) (evalFunc (o450Basis 5) M)
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o450ScalarCoverB i (evalFunc (o450Basis 0) M) (evalFunc (o450Basis 1) M) (evalFunc (o450Basis 2) M) (evalFunc (o450Basis 3) M) (evalFunc (o450Basis 4) M) (evalFunc (o450Basis 5) M) <;>
    simp [o450Cover, hb]

private lemma mem_kerEvalFunc_iff450 {L M : Mat3} :
    M ∈ kerEvalFunc L ↔ evalFunc L M = 0 := Iff.rfl

theorem o450W_le_source (i : Fin 18) : o450W ≤ o450SourceU i := by
  intro M hM
  fin_cases i <;> simp only [o450SourceU]
  · exact ⟨⟨⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 32) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 128) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 256) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 68) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 17 + codeMat 11) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 256) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 68) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 32 + codeMat 128) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 17 + codeMat 11) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 32 + codeMat 17) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 128) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 17) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 68) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 32 + codeMat 256) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 11) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 128) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 68) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 32 + codeMat 256) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 11) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 32 + codeMat 17) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 128) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 17) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 32 + codeMat 256) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 11) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 32 + codeMat 68) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 128) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 17) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 32 + codeMat 256) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 32 + codeMat 68) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 32 + codeMat 11) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 32) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 17) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 68) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 128 + codeMat 256) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 11) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 32) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 68) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 128 + codeMat 256) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 11) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 128 + codeMat 17) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 32) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 17) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 128 + codeMat 256) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 11) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 128 + codeMat 68) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact ⟨⟨⟨⟨spanCodes_le_kerEvalFunc_of_gens' (codeMat 32) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM, spanCodes_le_kerEvalFunc_of_gens' (codeMat 17) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 128 + codeMat 256) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 128 + codeMat 68) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩, spanCodes_le_kerEvalFunc_of_gens' (codeMat 128 + codeMat 11) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM⟩
  · exact spanCodes_le_kerEvalFunc_of_gens' (codeMat 32 + codeMat 128 + codeMat 17) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM
  · exact spanCodes_le_kerEvalFunc_of_gens' (codeMat 32 + codeMat 128 + codeMat 256 + codeMat 17 + codeMat 68) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM
  · exact spanCodes_le_kerEvalFunc_of_gens' (codeMat 256 + codeMat 11) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM
  · exact spanCodes_le_kerEvalFunc_of_gens' (codeMat 32 + codeMat 128 + codeMat 68 + codeMat 11) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM
  · exact spanCodes_le_kerEvalFunc_of_gens' (codeMat 256 + codeMat 68 + codeMat 11) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM
  · exact spanCodes_le_kerEvalFunc_of_gens' (codeMat 32 + codeMat 128 + codeMat 11) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM
  · exact spanCodes_le_kerEvalFunc_of_gens' (codeMat 17 + codeMat 68) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM
  · exact spanCodes_le_kerEvalFunc_of_gens' (codeMat 256 + codeMat 17) [68, 19, 10] (fun n hn => by fin_cases hn <;> decide) hM

theorem o450CoverSound (i : Fin 18) (M : Mat3) (h : o450Cover i M) : M ∈ o450SourceU i := by
  fin_cases i <;>
    simp only [o450Cover, o450ScalarCoverB, o450SourceU, o450Basis, Submodule.mem_inf,
               mem_kerEvalFunc_iff450, evalFunc_add_left] at h ⊢ <;>
    exact of_decide_eq_true h

private theorem o450Cert : (32 - 4) * 17 < ∑ i : Fin 18, o450Lambda i * o450SourceLb i := by
  simp only [o450Lambda, o450SourceLb]; decide
private theorem o450LambdaSum : 4 ≤ ∑ i : Fin 18, o450Lambda i := by
  simp only [o450Lambda]; decide

theorem o450Lb18
    (hSource : ∀ i : Fin 18, QuotientRankAtLeast (o450SourceU i) (o450SourceLb i)) :
    QuotientRankAtLeast o450W 18 :=
  quotientRankAtLeast_of_contradiction o450W 18 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o450SourceU o450SourceLb
      o450Lambda 4 17
      o450Cover o450W_le_source hSource
      o450LambdaSum o450CoverSound
      (fun M => o450MatCoverage M) (by omega) o450Cert D)

end QiushiMatmul
