import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiOrbitTransport
import QiushiStep98Orbit196Consumer
import QiushiStep99Orbit55Dispatch
import QiushiStep99Orbit56Dispatch
import QiushiStep99Orbit68Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiStep99Orbit76Dispatch
import QiushiStep99Orbit82Dispatch
import QiushiTransposeTransport

set_option maxHeartbeats 800000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem step99o196_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step99o196MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step99o196_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step99o196MatrixCodeNat M) = M := by decide

lemma step99o196_codeMat_matrixCode (M : Mat3) :
    codeMat (step99o196MatrixCodeNat M) = M :=
  step99o196_codeMat_matrixCode_all M

private theorem step99o196_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step99o196_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

private theorem step99o196_codeMat_mem_transposeW_of_witness
    {V : Submodule F2 Mat3} {pre tpre : Nat}
    (h_mem : codeMat tpre ∈ V)
    (h_trans : (codeMat tpre : Mat3).transpose = codeMat pre) :
    codeMat pre ∈ transposeW V := by
  change ∃ X, X ∈ V ∧ transposeLinearMap X = codeMat pre
  exact ⟨codeMat tpre, h_mem, h_trans⟩

-- Source 0 (row 0): orbit 76, lb 15
def step99o196ActualSource0 : Submodule F2 Mat3 := spanCodes [278, 132, 68, 32, 10, 1]

private theorem step99o196s0_sourceU_le :
    (o196SourceU ⟨0, by omega⟩) ≤ step99o196ActualSource0 := by
  intro M hM
  have hbool : spanContainsCodeCore [278, 132, 68, 32, 10, 1] (step99o196MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 266) ⊓ kerEvalFunc (codeMat 142 + codeMat 64)) ⊓ kerEvalFunc (codeMat 26)) at hM
    change ((evalFunc (codeMat 266) M = 0 ∧ evalFunc (codeMat 142 + codeMat 64) M = 0) ∧ evalFunc (codeMat 26) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [278, 132, 68, 32, 10, 1] (step99o196MatrixCodeNat M) hbool
  rwa [step99o196_codeMat_matrixCode] at hspan

private theorem step99o196s0_QtInv :
    (codeMat 403 : Mat3).transpose⁻¹ = (codeMat 403 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 403 : Mat3).transpose * (codeMat 403 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o196s0_targetSpan_le_action :
    step99o196ActualSource0 ≤ actionW (codeMat 305) (codeMat 403) o76W := by
  apply step99o196_spanCodes_le_of_gens [278, 132, 68, 32, 10, 1]
    (actionW (codeMat 305) (codeMat 403) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 251 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 251 (by decide)
    have hact : actionA (codeMat 305) (codeMat 403) (codeMat 251) = codeMat 278 := by
      unfold actionA
      rw [step99o196s0_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 251 * (codeMat 403 : Mat3).transpose = codeMat 278
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 452 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 452 (by decide)
    have hact : actionA (codeMat 305) (codeMat 403) (codeMat 452) = codeMat 132 := by
      unfold actionA
      rw [step99o196s0_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 452 * (codeMat 403 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 305) (codeMat 403) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step99o196s0_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 68 * (codeMat 403 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 288 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 305) (codeMat 403) (codeMat 288) = codeMat 32 := by
      unfold actionA
      rw [step99o196s0_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 288 * (codeMat 403 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 79 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 79 (by decide)
    have hact : actionA (codeMat 305) (codeMat 403) (codeMat 79) = codeMat 10 := by
      unfold actionA
      rw [step99o196s0_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 79 * (codeMat 403 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 305) (codeMat 403) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step99o196s0_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 1 * (codeMat 403 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact

theorem step99o196s0Dispatch :
    QuotientRankAtLeast (o196SourceU ⟨0, by omega⟩) 15 := by
  have hP : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 403 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 305) (codeMat 403) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 305) (codeMat 403) hP hQ o76W 15 step99_orbit76_lb15_unconditional
  have hMono : QuotientRankAtLeast step99o196ActualSource0 15 :=
    quotientRankAtLeast_mono step99o196s0_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o196s0_sourceU_le hMono

-- Source 1 (row 1): orbit 69, lb 15
def step99o196ActualSource1 : Submodule F2 Mat3 := spanCodes [278, 132, 70, 32, 10, 1]

private theorem step99o196s1_sourceU_le :
    (o196SourceU ⟨1, by omega⟩) ≤ step99o196ActualSource1 := by
  intro M hM
  have hbool : spanContainsCodeCore [278, 132, 70, 32, 10, 1] (step99o196MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 266 + codeMat 26) ⊓ kerEvalFunc (codeMat 142)) ⊓ kerEvalFunc (codeMat 64 + codeMat 26)) at hM
    change ((evalFunc (codeMat 266 + codeMat 26) M = 0 ∧ evalFunc (codeMat 142) M = 0) ∧ evalFunc (codeMat 64 + codeMat 26) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [278, 132, 70, 32, 10, 1] (step99o196MatrixCodeNat M) hbool
  rwa [step99o196_codeMat_matrixCode] at hspan

private theorem step99o196s1_QtInv :
    (codeMat 226 : Mat3).transpose⁻¹ = (codeMat 141 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 226 : Mat3).transpose * (codeMat 141 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o196s1_targetSpan_le_action :
    step99o196ActualSource1 ≤ actionW (codeMat 85) (codeMat 226) o69W := by
  apply step99o196_spanCodes_le_of_gens [278, 132, 70, 32, 10, 1]
    (actionW (codeMat 85) (codeMat 226) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 362 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 362 (by decide)
    have hact : actionA (codeMat 85) (codeMat 226) (codeMat 362) = codeMat 278 := by
      unfold actionA
      rw [step99o196s1_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 362 * (codeMat 141 : Mat3).transpose = codeMat 278
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 453 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 453 (by decide)
    have hact : actionA (codeMat 85) (codeMat 226) (codeMat 453) = codeMat 132 := by
      unfold actionA
      rw [step99o196s1_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 453 * (codeMat 141 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 196 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 196 (by decide)
    have hact : actionA (codeMat 85) (codeMat 226) (codeMat 196) = codeMat 70 := by
      unfold actionA
      rw [step99o196s1_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 196 * (codeMat 141 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 85) (codeMat 226) (codeMat 16) = codeMat 32 := by
      unfold actionA
      rw [step99o196s1_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 16 * (codeMat 141 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 352 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 352 (by decide)
    have hact : actionA (codeMat 85) (codeMat 226) (codeMat 352) = codeMat 10 := by
      unfold actionA
      rw [step99o196s1_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 352 * (codeMat 141 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 256 (by decide)
    have hact : actionA (codeMat 85) (codeMat 226) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step99o196s1_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 256 * (codeMat 141 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact

theorem step99o196s1Dispatch :
    QuotientRankAtLeast (o196SourceU ⟨1, by omega⟩) 15 := by
  have hP : Invertible (codeMat 85 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 226 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 85) (codeMat 226) o69W) 15 :=
    @quotientRankAtLeast_action (codeMat 85) (codeMat 226) hP hQ o69W 15 step99_orbit69_lb15_unconditional
  have hMono : QuotientRankAtLeast step99o196ActualSource1 15 :=
    quotientRankAtLeast_mono step99o196s1_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o196s1_sourceU_le hMono

-- Source 2 (row 3): orbit 55, lb 14
def step99o196ActualSource2 : Submodule F2 Mat3 := spanCodes [272, 130, 32, 10, 6, 1]

private theorem step99o196s2_sourceU_le :
    (o196SourceU ⟨2, by omega⟩) ≤ step99o196ActualSource2 := by
  intro M hM
  have hbool : spanContainsCodeCore [272, 130, 32, 10, 6, 1] (step99o196MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 266 + codeMat 26) ⊓ kerEvalFunc (codeMat 142)) ⊓ kerEvalFunc (codeMat 64)) at hM
    change ((evalFunc (codeMat 266 + codeMat 26) M = 0 ∧ evalFunc (codeMat 142) M = 0) ∧ evalFunc (codeMat 64) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 130, 32, 10, 6, 1] (step99o196MatrixCodeNat M) hbool
  rwa [step99o196_codeMat_matrixCode] at hspan

private theorem step99o196s2_QtInv :
    (codeMat 401 : Mat3).transpose⁻¹ = (codeMat 401 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 401 : Mat3).transpose * (codeMat 401 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o196s2_targetSpan_le_action :
    step99o196ActualSource2 ≤ actionW (codeMat 401) (codeMat 401) o55W := by
  apply step99o196_spanCodes_le_of_gens [272, 130, 32, 10, 6, 1]
    (actionW (codeMat 401) (codeMat 401) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 272 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 272 (by decide)
    have hact : actionA (codeMat 401) (codeMat 401) (codeMat 272) = codeMat 272 := by
      unfold actionA
      rw [step99o196s2_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 272 * (codeMat 401 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 438 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 438 (by decide)
    have hact : actionA (codeMat 401) (codeMat 401) (codeMat 438) = codeMat 130 := by
      unfold actionA
      rw [step99o196s2_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 438 * (codeMat 401 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 401) (codeMat 401) (codeMat 32) = codeMat 32 := by
      unfold actionA
      rw [step99o196s2_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 32 * (codeMat 401 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 14 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 14 (by decide)
    have hact : actionA (codeMat 401) (codeMat 401) (codeMat 14) = codeMat 10 := by
      unfold actionA
      rw [step99o196s2_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 14 * (codeMat 401 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 401) (codeMat 401) (codeMat 2) = codeMat 6 := by
      unfold actionA
      rw [step99o196s2_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 2 * (codeMat 401 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 401) (codeMat 401) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step99o196s2_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 1 * (codeMat 401 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact

theorem step99o196s2Dispatch :
    QuotientRankAtLeast (o196SourceU ⟨2, by omega⟩) 14 := by
  have hP : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 401) (codeMat 401) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 401) (codeMat 401) hP hQ o55W 14 step99_orbit55_lb14_unconditional
  have hMono : QuotientRankAtLeast step99o196ActualSource2 14 :=
    quotientRankAtLeast_mono step99o196s2_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o196s2_sourceU_le hMono

-- Source 3 (row 6): orbit 55, lb 14
def step99o196ActualSource3 : Submodule F2 Mat3 := spanCodes [256, 132, 32, 22, 10, 1]

private theorem step99o196s3_sourceU_le :
    (o196SourceU ⟨3, by omega⟩) ≤ step99o196ActualSource3 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 132, 32, 22, 10, 1] (step99o196MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 142) ⊓ kerEvalFunc (codeMat 64)) ⊓ kerEvalFunc (codeMat 26)) at hM
    change ((evalFunc (codeMat 142) M = 0 ∧ evalFunc (codeMat 64) M = 0) ∧ evalFunc (codeMat 26) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 132, 32, 22, 10, 1] (step99o196MatrixCodeNat M) hbool
  rwa [step99o196_codeMat_matrixCode] at hspan

private theorem step99o196s3_QtInv :
    (codeMat 92 : Mat3).transpose⁻¹ = (codeMat 116 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 92 : Mat3).transpose * (codeMat 116 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o196s3_targetSpan_le_transposeAction :
    step99o196ActualSource3 ≤ transposeW (actionW (codeMat 244) (codeMat 92) o55W) := by
  apply step99o196_spanCodes_le_of_gens [256, 132, 32, 22, 10, 1]
    (transposeW (actionW (codeMat 244) (codeMat 92) o55W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    -- g=256, g^T=256; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 1 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 244) (codeMat 92) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step99o196s3_QtInv]
      show (codeMat 244 : Mat3).transpose * codeMat 1 * (codeMat 116 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 256 ∈ actionW (codeMat 244) (codeMat 92) o55W :=
      step99o196_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 256 : Mat3).transpose = codeMat 256 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h1
    -- g=132, g^T=96; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 15 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 15 (by decide)
    have hact : actionA (codeMat 244) (codeMat 92) (codeMat 15) = codeMat 96 := by
      unfold actionA
      rw [step99o196s3_QtInv]
      show (codeMat 244 : Mat3).transpose * codeMat 15 * (codeMat 116 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 96 ∈ actionW (codeMat 244) (codeMat 92) o55W :=
      step99o196_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 96 : Mat3).transpose = codeMat 132 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h2
    -- g=32, g^T=128; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 2 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 244) (codeMat 92) (codeMat 2) = codeMat 128 := by
      unfold actionA
      rw [step99o196s3_QtInv]
      show (codeMat 244 : Mat3).transpose * codeMat 2 * (codeMat 116 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 128 ∈ actionW (codeMat 244) (codeMat 92) o55W :=
      step99o196_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 128 : Mat3).transpose = codeMat 32 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h3
    -- g=22, g^T=88; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 34 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 34 (by decide)
    have hact : actionA (codeMat 244) (codeMat 92) (codeMat 34) = codeMat 88 := by
      unfold actionA
      rw [step99o196s3_QtInv]
      show (codeMat 244 : Mat3).transpose * codeMat 34 * (codeMat 116 : Mat3).transpose = codeMat 88
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 88 ∈ actionW (codeMat 244) (codeMat 92) o55W :=
      step99o196_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 88 : Mat3).transpose = codeMat 22 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h4
    -- g=10, g^T=10; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 164 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 164 (by decide)
    have hact : actionA (codeMat 244) (codeMat 92) (codeMat 164) = codeMat 10 := by
      unfold actionA
      rw [step99o196s3_QtInv]
      show (codeMat 244 : Mat3).transpose * codeMat 164 * (codeMat 116 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 10 ∈ actionW (codeMat 244) (codeMat 92) o55W :=
      step99o196_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 10 : Mat3).transpose = codeMat 10 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h5
    -- g=1, g^T=1; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 438 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 438 (by decide)
    have hact : actionA (codeMat 244) (codeMat 92) (codeMat 438) = codeMat 1 := by
      unfold actionA
      rw [step99o196s3_QtInv]
      show (codeMat 244 : Mat3).transpose * codeMat 438 * (codeMat 116 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 1 ∈ actionW (codeMat 244) (codeMat 92) o55W :=
      step99o196_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 1 : Mat3).transpose = codeMat 1 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_transposeW_of_witness hmemAction htrans

theorem step99o196s3Dispatch :
    QuotientRankAtLeast (o196SourceU ⟨3, by omega⟩) 14 := by
  have hP : Invertible (codeMat 244 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 92 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 244) (codeMat 92) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 244) (codeMat 92) hP hQ o55W 14 step99_orbit55_lb14_unconditional
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 244) (codeMat 92) o55W)) 14 :=
    quotientRankAtLeast_transpose hAct
  have hMono : QuotientRankAtLeast step99o196ActualSource3 14 :=
    quotientRankAtLeast_mono step99o196s3_targetSpan_le_transposeAction hT
  exact quotientRankAtLeast_mono step99o196s3_sourceU_le hMono

-- Source 4 (row 7): orbit 56, lb 14
def step99o196ActualSource4 : Submodule F2 Mat3 := spanCodes [278, 132, 64, 32, 10, 1]

private theorem step99o196s4_sourceU_le :
    (o196SourceU ⟨4, by omega⟩) ≤ step99o196ActualSource4 := by
  intro M hM
  have hbool : spanContainsCodeCore [278, 132, 64, 32, 10, 1] (step99o196MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 266) ⊓ kerEvalFunc (codeMat 142)) ⊓ kerEvalFunc (codeMat 26)) at hM
    change ((evalFunc (codeMat 266) M = 0 ∧ evalFunc (codeMat 142) M = 0) ∧ evalFunc (codeMat 26) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [278, 132, 64, 32, 10, 1] (step99o196MatrixCodeNat M) hbool
  rwa [step99o196_codeMat_matrixCode] at hspan

private theorem step99o196s4_QtInv :
    (codeMat 183 : Mat3).transpose⁻¹ = (codeMat 419 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 183 : Mat3).transpose * (codeMat 419 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o196s4_targetSpan_le_transposeAction :
    step99o196ActualSource4 ≤ transposeW (actionW (codeMat 465) (codeMat 183) o56W) := by
  apply step99o196_spanCodes_le_of_gens [278, 132, 64, 32, 10, 1]
    (transposeW (actionW (codeMat 465) (codeMat 183) o56W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    -- g=278, g^T=344; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 162 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 162 (by decide)
    have hact : actionA (codeMat 465) (codeMat 183) (codeMat 162) = codeMat 344 := by
      unfold actionA
      rw [step99o196s4_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 162 * (codeMat 419 : Mat3).transpose = codeMat 344
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 344 ∈ actionW (codeMat 465) (codeMat 183) o56W :=
      step99o196_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 344 : Mat3).transpose = codeMat 278 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h1
    -- g=132, g^T=96; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 81 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 81 (by decide)
    have hact : actionA (codeMat 465) (codeMat 183) (codeMat 81) = codeMat 96 := by
      unfold actionA
      rw [step99o196s4_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 81 * (codeMat 419 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 96 ∈ actionW (codeMat 465) (codeMat 183) o56W :=
      step99o196_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 96 : Mat3).transpose = codeMat 132 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h2
    -- g=64, g^T=4; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 3 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 465) (codeMat 183) (codeMat 3) = codeMat 4 := by
      unfold actionA
      rw [step99o196s4_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 3 * (codeMat 419 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 4 ∈ actionW (codeMat 465) (codeMat 183) o56W :=
      step99o196_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 4 : Mat3).transpose = codeMat 64 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h3
    -- g=32, g^T=128; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 511 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 511 (by decide)
    have hact : actionA (codeMat 465) (codeMat 183) (codeMat 511) = codeMat 128 := by
      unfold actionA
      rw [step99o196s4_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 511 * (codeMat 419 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 128 ∈ actionW (codeMat 465) (codeMat 183) o56W :=
      step99o196_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 128 : Mat3).transpose = codeMat 32 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h4
    -- g=10, g^T=10; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 15 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 15 (by decide)
    have hact : actionA (codeMat 465) (codeMat 183) (codeMat 15) = codeMat 10 := by
      unfold actionA
      rw [step99o196s4_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 15 * (codeMat 419 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 10 ∈ actionW (codeMat 465) (codeMat 183) o56W :=
      step99o196_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 10 : Mat3).transpose = codeMat 10 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h5
    -- g=1, g^T=1; show g^T ∈ actionW then g ∈ transposeW(actionW)
    have hw : codeMat 1 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 465) (codeMat 183) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step99o196s4_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 1 * (codeMat 419 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 1 ∈ actionW (codeMat 465) (codeMat 183) o56W :=
      step99o196_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 1 : Mat3).transpose = codeMat 1 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_transposeW_of_witness hmemAction htrans

theorem step99o196s4Dispatch :
    QuotientRankAtLeast (o196SourceU ⟨4, by omega⟩) 14 := by
  have hP : Invertible (codeMat 465 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 183 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 465) (codeMat 183) o56W) 14 :=
    @quotientRankAtLeast_action (codeMat 465) (codeMat 183) hP hQ o56W 14 step99_orbit56_lb14_unconditional
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 465) (codeMat 183) o56W)) 14 :=
    quotientRankAtLeast_transpose hAct
  have hMono : QuotientRankAtLeast step99o196ActualSource4 14 :=
    quotientRankAtLeast_mono step99o196s4_targetSpan_le_transposeAction hT
  exact quotientRankAtLeast_mono step99o196s4_sourceU_le hMono

-- Source 5 (row 11): orbit 68, lb 14
def step99o196ActualSource5 : Submodule F2 Mat3 := spanCodes [278, 132, 84, 32, 10, 1]

private theorem step99o196s5_sourceU_le :
    (o196SourceU ⟨5, by omega⟩) ≤ step99o196ActualSource5 := by
  intro M hM
  have hbool : spanContainsCodeCore [278, 132, 84, 32, 10, 1] (step99o196MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 266) ⊓ kerEvalFunc (codeMat 142 + codeMat 26)) ⊓ kerEvalFunc (codeMat 64 + codeMat 26)) at hM
    change ((evalFunc (codeMat 266) M = 0 ∧ evalFunc (codeMat 142 + codeMat 26) M = 0) ∧ evalFunc (codeMat 64 + codeMat 26) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [278, 132, 84, 32, 10, 1] (step99o196MatrixCodeNat M) hbool
  rwa [step99o196_codeMat_matrixCode] at hspan

private theorem step99o196s5_QtInv :
    (codeMat 239 : Mat3).transpose⁻¹ = (codeMat 351 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 239 : Mat3).transpose * (codeMat 351 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o196s5_targetSpan_le_action :
    step99o196ActualSource5 ≤ actionW (codeMat 125) (codeMat 239) o68W := by
  apply step99o196_spanCodes_le_of_gens [278, 132, 84, 32, 10, 1]
    (actionW (codeMat 125) (codeMat 239) o68W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 366 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 366 (by decide)
    have hact : actionA (codeMat 125) (codeMat 239) (codeMat 366) = codeMat 278 := by
      unfold actionA
      rw [step99o196s5_QtInv]
      show (codeMat 125 : Mat3).transpose * codeMat 366 * (codeMat 351 : Mat3).transpose = codeMat 278
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 389 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 389 (by decide)
    have hact : actionA (codeMat 125) (codeMat 239) (codeMat 389) = codeMat 132 := by
      unfold actionA
      rw [step99o196s5_QtInv]
      show (codeMat 125 : Mat3).transpose * codeMat 389 * (codeMat 351 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 298 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 298 (by decide)
    have hact : actionA (codeMat 125) (codeMat 239) (codeMat 298) = codeMat 84 := by
      unfold actionA
      rw [step99o196s5_QtInv]
      show (codeMat 125 : Mat3).transpose * codeMat 298 * (codeMat 351 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 27 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 125) (codeMat 239) (codeMat 27) = codeMat 32 := by
      unfold actionA
      rw [step99o196s5_QtInv]
      show (codeMat 125 : Mat3).transpose * codeMat 27 * (codeMat 351 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 383 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 383 (by decide)
    have hact : actionA (codeMat 125) (codeMat 239) (codeMat 383) = codeMat 10 := by
      unfold actionA
      rw [step99o196s5_QtInv]
      show (codeMat 125 : Mat3).transpose * codeMat 383 * (codeMat 351 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 448 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 448 (by decide)
    have hact : actionA (codeMat 125) (codeMat 239) (codeMat 448) = codeMat 1 := by
      unfold actionA
      rw [step99o196s5_QtInv]
      show (codeMat 125 : Mat3).transpose * codeMat 448 * (codeMat 351 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact

theorem step99o196s5Dispatch :
    QuotientRankAtLeast (o196SourceU ⟨5, by omega⟩) 14 := by
  have hP : Invertible (codeMat 125 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 239 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 125) (codeMat 239) o68W) 14 :=
    @quotientRankAtLeast_action (codeMat 125) (codeMat 239) hP hQ o68W 14 step99_orbit68_lb14_unconditional
  have hMono : QuotientRankAtLeast step99o196ActualSource5 14 :=
    quotientRankAtLeast_mono step99o196s5_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o196s5_sourceU_le hMono

-- Source 6 (row 12): orbit 82, lb 14
def step99o196ActualSource6 : Submodule F2 Mat3 := spanCodes [278, 132, 86, 32, 10, 1]

private theorem step99o196s6_sourceU_le :
    (o196SourceU ⟨6, by omega⟩) ≤ step99o196ActualSource6 := by
  intro M hM
  have hbool : spanContainsCodeCore [278, 132, 86, 32, 10, 1] (step99o196MatrixCodeNat M) = true := by
    change M ∈ ((kerEvalFunc (codeMat 266 + codeMat 64) ⊓ kerEvalFunc (codeMat 142)) ⊓ kerEvalFunc (codeMat 26)) at hM
    change ((evalFunc (codeMat 266 + codeMat 64) M = 0 ∧ evalFunc (codeMat 142) M = 0) ∧ evalFunc (codeMat 26) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [278, 132, 86, 32, 10, 1] (step99o196MatrixCodeNat M) hbool
  rwa [step99o196_codeMat_matrixCode] at hspan

private theorem step99o196s6_QtInv :
    (codeMat 214 : Mat3).transpose⁻¹ = (codeMat 214 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 214 : Mat3).transpose * (codeMat 214 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o196s6_targetSpan_le_action :
    step99o196ActualSource6 ≤ actionW (codeMat 426) (codeMat 214) o82W := by
  apply step99o196_spanCodes_le_of_gens [278, 132, 86, 32, 10, 1]
    (actionW (codeMat 426) (codeMat 214) o82W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 496 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 496 (by decide)
    have hact : actionA (codeMat 426) (codeMat 214) (codeMat 496) = codeMat 278 := by
      unfold actionA
      rw [step99o196s6_QtInv]
      show (codeMat 426 : Mat3).transpose * codeMat 496 * (codeMat 214 : Mat3).transpose = codeMat 278
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 398 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 398 (by decide)
    have hact : actionA (codeMat 426) (codeMat 214) (codeMat 398) = codeMat 132 := by
      unfold actionA
      rw [step99o196s6_QtInv]
      show (codeMat 426 : Mat3).transpose * codeMat 398 * (codeMat 214 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 181 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 181 (by decide)
    have hact : actionA (codeMat 426) (codeMat 214) (codeMat 181) = codeMat 86 := by
      unfold actionA
      rw [step99o196s6_QtInv]
      show (codeMat 426 : Mat3).transpose * codeMat 181 * (codeMat 214 : Mat3).transpose = codeMat 86
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 426) (codeMat 214) (codeMat 1) = codeMat 32 := by
      unfold actionA
      rw [step99o196s6_QtInv]
      show (codeMat 426 : Mat3).transpose * codeMat 1 * (codeMat 214 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 507 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 507 (by decide)
    have hact : actionA (codeMat 426) (codeMat 214) (codeMat 507) = codeMat 10 := by
      unfold actionA
      rw [step99o196s6_QtInv]
      show (codeMat 426 : Mat3).transpose * codeMat 507 * (codeMat 214 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 292 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 292 (by decide)
    have hact : actionA (codeMat 426) (codeMat 214) (codeMat 292) = codeMat 1 := by
      unfold actionA
      rw [step99o196s6_QtInv]
      show (codeMat 426 : Mat3).transpose * codeMat 292 * (codeMat 214 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact

theorem step99o196s6Dispatch :
    QuotientRankAtLeast (o196SourceU ⟨6, by omega⟩) 14 := by
  have hP : Invertible (codeMat 426 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 214 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 426) (codeMat 214) o82W) 14 :=
    @quotientRankAtLeast_action (codeMat 426) (codeMat 214) hP hQ o82W 14 step99_orbit82_lb14_unconditional
  have hMono : QuotientRankAtLeast step99o196ActualSource6 14 :=
    quotientRankAtLeast_mono step99o196s6_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o196s6_sourceU_le hMono

-- Source 7 (row 16): orbit 11, lb 12
def step99o196ActualSource7 : Submodule F2 Mat3 := spanCodes [258, 128, 32, 16, 10, 4, 1]

private theorem step99o196s7_sourceU_le :
    (o196SourceU ⟨7, by omega⟩) ≤ step99o196ActualSource7 := by
  intro M hM
  have hbool : spanContainsCodeCore [258, 128, 32, 16, 10, 4, 1] (step99o196MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 266) ⊓ kerEvalFunc (codeMat 64)) at hM
    change (evalFunc (codeMat 266) M = 0 ∧ evalFunc (codeMat 64) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 128, 32, 16, 10, 4, 1] (step99o196MatrixCodeNat M) hbool
  rwa [step99o196_codeMat_matrixCode] at hspan

private theorem step99o196s7_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o196s7_targetSpan_le_action :
    step99o196ActualSource7 ≤ actionW (codeMat 266) (codeMat 84) orbit11W := by
  apply step99o196_spanCodes_le_of_gens [258, 128, 32, 16, 10, 4, 1]
    (actionW (codeMat 266) (codeMat 84) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 80 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 80 (by decide)
    have hact : actionA (codeMat 266) (codeMat 84) (codeMat 80) = codeMat 258 := by
      unfold actionA
      rw [step99o196s7_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 80 * (codeMat 84 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 266) (codeMat 84) (codeMat 128) = codeMat 128 := by
      unfold actionA
      rw [step99o196s7_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 128 * (codeMat 84 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 84) (codeMat 1) = codeMat 32 := by
      unfold actionA
      rw [step99o196s7_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 84) (codeMat 2) = codeMat 16 := by
      unfold actionA
      rw [step99o196s7_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 20 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 20 (by decide)
    have hact : actionA (codeMat 266) (codeMat 84) (codeMat 20) = codeMat 10 := by
      unfold actionA
      rw [step99o196s7_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 20 * (codeMat 84 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 84) (codeMat 8) = codeMat 4 := by
      unfold actionA
      rw [step99o196s7_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 84 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 84) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step99o196s7_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact

theorem step99o196s7Dispatch :
    QuotientRankAtLeast (o196SourceU ⟨7, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 84) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 84) hP hQ orbit11W 12 orbit11_lb12
  have hMono : QuotientRankAtLeast step99o196ActualSource7 12 :=
    quotientRankAtLeast_mono step99o196s7_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o196s7_sourceU_le hMono

-- Source 8 (row 24): orbit 14, lb 12
def step99o196ActualSource8 : Submodule F2 Mat3 := spanCodes [260, 132, 66, 32, 18, 10, 1]

private theorem step99o196s8_sourceU_le :
    (o196SourceU ⟨8, by omega⟩) ≤ step99o196ActualSource8 := by
  intro M hM
  have hbool : spanContainsCodeCore [260, 132, 66, 32, 18, 10, 1] (step99o196MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 266 + codeMat 142) ⊓ kerEvalFunc (codeMat 64 + codeMat 26)) at hM
    change (evalFunc (codeMat 266 + codeMat 142) M = 0 ∧ evalFunc (codeMat 64 + codeMat 26) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 132, 66, 32, 18, 10, 1] (step99o196MatrixCodeNat M) hbool
  rwa [step99o196_codeMat_matrixCode] at hspan

private theorem step99o196s8_QtInv :
    (codeMat 179 : Mat3).transpose⁻¹ = (codeMat 421 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 179 : Mat3).transpose * (codeMat 421 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o196s8_targetSpan_le_action :
    step99o196ActualSource8 ≤ actionW (codeMat 183) (codeMat 179) orbit14W := by
  apply step99o196_spanCodes_le_of_gens [260, 132, 66, 32, 18, 10, 1]
    (actionW (codeMat 183) (codeMat 179) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 130 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 130 (by decide)
    have hact : actionA (codeMat 183) (codeMat 179) (codeMat 130) = codeMat 260 := by
      unfold actionA
      rw [step99o196s8_QtInv]
      show (codeMat 183 : Mat3).transpose * codeMat 130 * (codeMat 421 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 490 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 490 (by decide)
    have hact : actionA (codeMat 183) (codeMat 179) (codeMat 490) = codeMat 132 := by
      unfold actionA
      rw [step99o196s8_QtInv]
      show (codeMat 183 : Mat3).transpose * codeMat 490 * (codeMat 421 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 119 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 119 (by decide)
    have hact : actionA (codeMat 183) (codeMat 179) (codeMat 119) = codeMat 66 := by
      unfold actionA
      rw [step99o196s8_QtInv]
      show (codeMat 183 : Mat3).transpose * codeMat 119 * (codeMat 421 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 183) (codeMat 179) (codeMat 128) = codeMat 32 := by
      unfold actionA
      rw [step99o196s8_QtInv]
      show (codeMat 183 : Mat3).transpose * codeMat 128 * (codeMat 421 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 511 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 511 (by decide)
    have hact : actionA (codeMat 183) (codeMat 179) (codeMat 511) = codeMat 18 := by
      unfold actionA
      rw [step99o196s8_QtInv]
      show (codeMat 183 : Mat3).transpose * codeMat 511 * (codeMat 421 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 127 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 127 (by decide)
    have hact : actionA (codeMat 183) (codeMat 179) (codeMat 127) = codeMat 10 := by
      unfold actionA
      rw [step99o196s8_QtInv]
      show (codeMat 183 : Mat3).transpose * codeMat 127 * (codeMat 421 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 9 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 9 (by decide)
    have hact : actionA (codeMat 183) (codeMat 179) (codeMat 9) = codeMat 1 := by
      unfold actionA
      rw [step99o196s8_QtInv]
      show (codeMat 183 : Mat3).transpose * codeMat 9 * (codeMat 421 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact

theorem step99o196s8Dispatch :
    QuotientRankAtLeast (o196SourceU ⟨8, by omega⟩) 12 := by
  have hP : Invertible (codeMat 183 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 179 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 183) (codeMat 179) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 183) (codeMat 179) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o196ActualSource8 12 :=
    quotientRankAtLeast_mono step99o196s8_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o196s8_sourceU_le hMono

-- Source 9 (row 29): orbit 14, lb 12
def step99o196ActualSource9 : Submodule F2 Mat3 := spanCodes [276, 132, 80, 32, 8, 2, 1]

private theorem step99o196s9_sourceU_le :
    (o196SourceU ⟨9, by omega⟩) ≤ step99o196ActualSource9 := by
  intro M hM
  have hbool : spanContainsCodeCore [276, 132, 80, 32, 8, 2, 1] (step99o196MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 266 + codeMat 64 + codeMat 26) ⊓ kerEvalFunc (codeMat 142 + codeMat 64 + codeMat 26)) at hM
    change (evalFunc (codeMat 266 + codeMat 64 + codeMat 26) M = 0 ∧ evalFunc (codeMat 142 + codeMat 64 + codeMat 26) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [276, 132, 80, 32, 8, 2, 1] (step99o196MatrixCodeNat M) hbool
  rwa [step99o196_codeMat_matrixCode] at hspan

private theorem step99o196s9_QtInv :
    (codeMat 172 : Mat3).transpose⁻¹ = (codeMat 99 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 172 : Mat3).transpose * (codeMat 99 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o196s9_targetSpan_le_action :
    step99o196ActualSource9 ≤ actionW (codeMat 106) (codeMat 172) orbit14W := by
  apply step99o196_spanCodes_le_of_gens [276, 132, 80, 32, 8, 2, 1]
    (actionW (codeMat 106) (codeMat 172) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 28 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 28 (by decide)
    have hact : actionA (codeMat 106) (codeMat 172) (codeMat 28) = codeMat 276 := by
      unfold actionA
      rw [step99o196s9_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 28 * (codeMat 99 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 480 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 480 (by decide)
    have hact : actionA (codeMat 106) (codeMat 172) (codeMat 480) = codeMat 132 := by
      unfold actionA
      rw [step99o196s9_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 480 * (codeMat 99 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 148 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 148 (by decide)
    have hact : actionA (codeMat 106) (codeMat 172) (codeMat 148) = codeMat 80 := by
      unfold actionA
      rw [step99o196s9_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 148 * (codeMat 99 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 106) (codeMat 172) (codeMat 3) = codeMat 32 := by
      unfold actionA
      rw [step99o196s9_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 3 * (codeMat 99 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 106) (codeMat 172) (codeMat 2) = codeMat 8 := by
      unfold actionA
      rw [step99o196s9_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 2 * (codeMat 99 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 106) (codeMat 172) (codeMat 256) = codeMat 2 := by
      unfold actionA
      rw [step99o196s9_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 256 * (codeMat 99 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 106) (codeMat 172) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step99o196s9_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 128 * (codeMat 99 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o196_codeMat_mem_actionW_of_witness hw hact

theorem step99o196s9Dispatch :
    QuotientRankAtLeast (o196SourceU ⟨9, by omega⟩) 12 := by
  have hP : Invertible (codeMat 106 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 172 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 106) (codeMat 172) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 106) (codeMat 172) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o196ActualSource9 12 :=
    quotientRankAtLeast_mono step99o196s9_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o196s9_sourceU_le hMono

theorem step99o196_all_dispatch (i : Fin 10) :
    QuotientRankAtLeast (o196SourceU i) (o196SourceLb i) := by
  fin_cases i
  · exact step99o196s0Dispatch
  · exact step99o196s1Dispatch
  · exact step99o196s2Dispatch
  · exact step99o196s3Dispatch
  · exact step99o196s4Dispatch
  · exact step99o196s5Dispatch
  · exact step99o196s6Dispatch
  · exact step99o196s7Dispatch
  · exact step99o196s8Dispatch
  · exact step99o196s9Dispatch

theorem step99_orbit196_lb16_unconditional :
    QuotientRankAtLeast o196W 16 :=
  o196Lb16 step99o196_all_dispatch

end QiushiMatmul
