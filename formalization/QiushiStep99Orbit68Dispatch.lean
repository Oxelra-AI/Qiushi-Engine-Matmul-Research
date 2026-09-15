import QiushiCodeSpanCore
import QiushiFlattenSeeds
import QiushiMonotonicity
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiOrbitTransport
import QiushiStep81Qdim2Generated
import QiushiStep98Orbit68Consumer
import QiushiTransposeTransport

set_option maxHeartbeats 800000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem step99o68_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step99o68MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step99o68_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step99o68MatrixCodeNat M) = M := by decide

lemma step99o68_codeMat_matrixCode (M : Mat3) :
    codeMat (step99o68MatrixCodeNat M) = M :=
  step99o68_codeMat_matrixCode_all M

private theorem step99o68_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step99o68_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

private theorem step99o68_codeMat_mem_transposeW_of_witness
    {V : Submodule F2 Mat3} {pre tpre : Nat}
    (h_mem : codeMat tpre ∈ V)
    (h_trans : (codeMat tpre : Mat3).transpose = codeMat pre) :
    codeMat pre ∈ transposeW V := by
  change ∃ X, X ∈ V ∧ transposeLinearMap X = codeMat pre
  exact ⟨codeMat tpre, h_mem, h_trans⟩

-- Source 0 (row 0): orbit 10, lb 12
def step99o68ActualSource0 : Submodule F2 Mat3 := spanCodes [288, 164, 68, 16, 8, 2, 1]

private theorem step99o68s0_sourceU_le :
    (o68SourceU ⟨0, by omega⟩) ≤ step99o68ActualSource0 := by
  intro M hM
  have hbool : spanContainsCodeCore [288, 164, 68, 16, 8, 2, 1] (step99o68MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 356) ⊓ kerEvalFunc (codeMat 196)) at hM
    change (evalFunc (codeMat 356) M = 0 ∧ evalFunc (codeMat 196) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 8, 2, 1] (step99o68MatrixCodeNat M) hbool
  rwa [step99o68_codeMat_matrixCode] at hspan

private theorem step99o68s0_QtInv :
    (codeMat 286 : Mat3).transpose⁻¹ = (codeMat 303 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 286 : Mat3).transpose * (codeMat 303 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o68s0_targetSpan_le_action :
    step99o68ActualSource0 ≤ actionW (codeMat 266) (codeMat 286) orbit10W := by
  apply step99o68_spanCodes_le_of_gens [288, 164, 68, 16, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 286) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 325 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 325 (by decide)
    have hact : actionA (codeMat 266) (codeMat 286) (codeMat 325) = codeMat 288 := by
      unfold actionA
      rw [step99o68s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 325 * (codeMat 303 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 237 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 237 (by decide)
    have hact : actionA (codeMat 266) (codeMat 286) (codeMat 237) = codeMat 164 := by
      unfold actionA
      rw [step99o68s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 237 * (codeMat 303 : Mat3).transpose = codeMat 164
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 168 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 168 (by decide)
    have hact : actionA (codeMat 266) (codeMat 286) (codeMat 168) = codeMat 68 := by
      unfold actionA
      rw [step99o68s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 168 * (codeMat 303 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 3 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 266) (codeMat 286) (codeMat 3) = codeMat 16 := by
      unfold actionA
      rw [step99o68s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 3 * (codeMat 303 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 286) (codeMat 2) = codeMat 8 := by
      unfold actionA
      rw [step99o68s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 303 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 266) (codeMat 286) (codeMat 24) = codeMat 2 := by
      unfold actionA
      rw [step99o68s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 24 * (codeMat 303 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 286) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step99o68s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 303 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact

theorem step99o68s0Dispatch :
    QuotientRankAtLeast (o68SourceU ⟨0, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 286 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 286) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 286) hP hQ orbit10W 12 orbit10_lb12
  have hMono : QuotientRankAtLeast step99o68ActualSource0 12 :=
    quotientRankAtLeast_mono step99o68s0_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o68s0_sourceU_le hMono

-- Source 1 (row 1): orbit 14, lb 12
def step99o68ActualSource1 : Submodule F2 Mat3 := spanCodes [288, 160, 64, 16, 10, 4, 1]

private theorem step99o68s1_sourceU_le :
    (o68SourceU ⟨1, by omega⟩) ≤ step99o68ActualSource1 := by
  intro M hM
  have hbool : spanContainsCodeCore [288, 160, 64, 16, 10, 4, 1] (step99o68MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 356 + codeMat 196) ⊓ kerEvalFunc (codeMat 10)) at hM
    change (evalFunc (codeMat 356 + codeMat 196) M = 0 ∧ evalFunc (codeMat 10) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 160, 64, 16, 10, 4, 1] (step99o68MatrixCodeNat M) hbool
  rwa [step99o68_codeMat_matrixCode] at hspan

private theorem step99o68s1_QtInv :
    (codeMat 142 : Mat3).transpose⁻¹ = (codeMat 354 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 142 : Mat3).transpose * (codeMat 354 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o68s1_targetSpan_le_action :
    step99o68ActualSource1 ≤ actionW (codeMat 305) (codeMat 142) orbit14W := by
  apply step99o68_spanCodes_le_of_gens [288, 160, 64, 16, 10, 4, 1]
    (actionW (codeMat 305) (codeMat 142) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 305) (codeMat 142) (codeMat 8) = codeMat 288 := by
      unfold actionA
      rw [step99o68s1_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 8 * (codeMat 354 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 264 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 264 (by decide)
    have hact : actionA (codeMat 305) (codeMat 142) (codeMat 264) = codeMat 160 := by
      unfold actionA
      rw [step99o68s1_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 264 * (codeMat 354 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 305) (codeMat 142) (codeMat 128) = codeMat 64 := by
      unfold actionA
      rw [step99o68s1_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 128 * (codeMat 354 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 305) (codeMat 142) (codeMat 360) = codeMat 16 := by
      unfold actionA
      rw [step99o68s1_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 360 * (codeMat 354 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 149 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 149 (by decide)
    have hact : actionA (codeMat 305) (codeMat 142) (codeMat 149) = codeMat 10 := by
      unfold actionA
      rw [step99o68s1_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 149 * (codeMat 354 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 305) (codeMat 142) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step99o68s1_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 1 * (codeMat 354 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 305) (codeMat 142) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step99o68s1_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 2 * (codeMat 354 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact

theorem step99o68s1Dispatch :
    QuotientRankAtLeast (o68SourceU ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 305) (codeMat 142) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 305) (codeMat 142) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o68ActualSource1 12 :=
    quotientRankAtLeast_mono step99o68s1_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o68s1_sourceU_le hMono

-- Source 2 (row 2): orbit 14, lb 12
def step99o68ActualSource2 : Submodule F2 Mat3 := spanCodes [288, 162, 66, 16, 10, 6, 1]

private theorem step99o68s2_sourceU_le :
    (o68SourceU ⟨2, by omega⟩) ≤ step99o68ActualSource2 := by
  intro M hM
  have hbool : spanContainsCodeCore [288, 162, 66, 16, 10, 6, 1] (step99o68MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 356 + codeMat 10) ⊓ kerEvalFunc (codeMat 196 + codeMat 10)) at hM
    change (evalFunc (codeMat 356 + codeMat 10) M = 0 ∧ evalFunc (codeMat 196 + codeMat 10) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 162, 66, 16, 10, 6, 1] (step99o68MatrixCodeNat M) hbool
  rwa [step99o68_codeMat_matrixCode] at hspan

private theorem step99o68s2_QtInv :
    (codeMat 426 : Mat3).transpose⁻¹ = (codeMat 335 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 426 : Mat3).transpose * (codeMat 335 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o68s2_targetSpan_le_action :
    step99o68ActualSource2 ≤ actionW (codeMat 417) (codeMat 426) orbit14W := by
  apply step99o68_spanCodes_le_of_gens [288, 162, 66, 16, 10, 6, 1]
    (actionW (codeMat 417) (codeMat 426) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 417) (codeMat 426) (codeMat 384) = codeMat 288 := by
      unfold actionA
      rw [step99o68s2_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 384 * (codeMat 335 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 413 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 413 (by decide)
    have hact : actionA (codeMat 417) (codeMat 426) (codeMat 413) = codeMat 162 := by
      unfold actionA
      rw [step99o68s2_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 413 * (codeMat 335 : Mat3).transpose = codeMat 162
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 21 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 21 (by decide)
    have hact : actionA (codeMat 417) (codeMat 426) (codeMat 21) = codeMat 66 := by
      unfold actionA
      rw [step99o68s2_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 21 * (codeMat 335 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 417) (codeMat 426) (codeMat 360) = codeMat 16 := by
      unfold actionA
      rw [step99o68s2_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 360 * (codeMat 335 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 149 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 149 (by decide)
    have hact : actionA (codeMat 417) (codeMat 426) (codeMat 149) = codeMat 10 := by
      unfold actionA
      rw [step99o68s2_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 149 * (codeMat 335 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 417) (codeMat 426) (codeMat 3) = codeMat 6 := by
      unfold actionA
      rw [step99o68s2_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 3 * (codeMat 335 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 417) (codeMat 426) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step99o68s2_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 2 * (codeMat 335 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact

theorem step99o68s2Dispatch :
    QuotientRankAtLeast (o68SourceU ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 426 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 417) (codeMat 426) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 417) (codeMat 426) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o68ActualSource2 12 :=
    quotientRankAtLeast_mono step99o68s2_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o68s2_sourceU_le hMono

-- Source 3 (row 3): orbit 14, lb 12
def step99o68ActualSource3 : Submodule F2 Mat3 := spanCodes [256, 132, 68, 32, 16, 10, 1]

private theorem step99o68s3_sourceU_le :
    (o68SourceU ⟨3, by omega⟩) ≤ step99o68ActualSource3 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 132, 68, 32, 16, 10, 1] (step99o68MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 196) ⊓ kerEvalFunc (codeMat 10)) at hM
    change (evalFunc (codeMat 196) M = 0 ∧ evalFunc (codeMat 10) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 132, 68, 32, 16, 10, 1] (step99o68MatrixCodeNat M) hbool
  rwa [step99o68_codeMat_matrixCode] at hspan

private theorem step99o68s3_QtInv :
    (codeMat 225 : Mat3).transpose⁻¹ = (codeMat 169 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 225 : Mat3).transpose * (codeMat 169 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o68s3_targetSpan_le_action :
    step99o68ActualSource3 ≤ actionW (codeMat 156) (codeMat 225) orbit14W := by
  apply step99o68_spanCodes_le_of_gens [256, 132, 68, 32, 16, 10, 1]
    (actionW (codeMat 156) (codeMat 225) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 156) (codeMat 225) (codeMat 2) = codeMat 256 := by
      unfold actionA
      rw [step99o68s3_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 2 * (codeMat 169 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 148 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 148 (by decide)
    have hact : actionA (codeMat 156) (codeMat 225) (codeMat 148) = codeMat 132 := by
      unfold actionA
      rw [step99o68s3_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 148 * (codeMat 169 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 149 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 149 (by decide)
    have hact : actionA (codeMat 156) (codeMat 225) (codeMat 149) = codeMat 68 := by
      unfold actionA
      rw [step99o68s3_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 149 * (codeMat 169 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 156) (codeMat 225) (codeMat 128) = codeMat 32 := by
      unfold actionA
      rw [step99o68s3_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 128 * (codeMat 169 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 156) (codeMat 225) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step99o68s3_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 256 * (codeMat 169 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 156) (codeMat 225) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step99o68s3_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 96 * (codeMat 169 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 156) (codeMat 225) (codeMat 360) = codeMat 1 := by
      unfold actionA
      rw [step99o68s3_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 360 * (codeMat 169 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact

theorem step99o68s3Dispatch :
    QuotientRankAtLeast (o68SourceU ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 156 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 156) (codeMat 225) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 156) (codeMat 225) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o68ActualSource3 12 :=
    quotientRankAtLeast_mono step99o68s3_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o68s3_sourceU_le hMono

-- Source 4 (row 4): orbit 14, lb 12
def step99o68ActualSource4 : Submodule F2 Mat3 := spanCodes [258, 134, 68, 34, 16, 10, 1]

private theorem step99o68s4_sourceU_le :
    (o68SourceU ⟨4, by omega⟩) ≤ step99o68ActualSource4 := by
  intro M hM
  have hbool : spanContainsCodeCore [258, 134, 68, 34, 16, 10, 1] (step99o68MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 356 + codeMat 10) ⊓ kerEvalFunc (codeMat 196)) at hM
    change (evalFunc (codeMat 356 + codeMat 10) M = 0 ∧ evalFunc (codeMat 196) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 134, 68, 34, 16, 10, 1] (step99o68MatrixCodeNat M) hbool
  rwa [step99o68_codeMat_matrixCode] at hspan

private theorem step99o68s4_QtInv :
    (codeMat 229 : Mat3).transpose⁻¹ = (codeMat 187 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 229 : Mat3).transpose * (codeMat 187 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o68s4_targetSpan_le_action :
    step99o68ActualSource4 ≤ actionW (codeMat 158) (codeMat 229) orbit14W := by
  apply step99o68_spanCodes_le_of_gens [258, 134, 68, 34, 16, 10, 1]
    (actionW (codeMat 158) (codeMat 229) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 483 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 483 (by decide)
    have hact : actionA (codeMat 158) (codeMat 229) (codeMat 483) = codeMat 258 := by
      unfold actionA
      rw [step99o68s4_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 483 * (codeMat 187 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 252 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 252 (by decide)
    have hact : actionA (codeMat 158) (codeMat 229) (codeMat 252) = codeMat 134 := by
      unfold actionA
      rw [step99o68s4_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 252 * (codeMat 187 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 413 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 413 (by decide)
    have hact : actionA (codeMat 158) (codeMat 229) (codeMat 413) = codeMat 68 := by
      unfold actionA
      rw [step99o68s4_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 413 * (codeMat 187 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 480 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 480 (by decide)
    have hact : actionA (codeMat 158) (codeMat 229) (codeMat 480) = codeMat 34 := by
      unfold actionA
      rw [step99o68s4_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 480 * (codeMat 187 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 158) (codeMat 229) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step99o68s4_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 256 * (codeMat 187 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 158) (codeMat 229) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step99o68s4_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 96 * (codeMat 187 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 158) (codeMat 229) (codeMat 360) = codeMat 1 := by
      unfold actionA
      rw [step99o68s4_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 360 * (codeMat 187 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact

theorem step99o68s4Dispatch :
    QuotientRankAtLeast (o68SourceU ⟨4, by omega⟩) 12 := by
  have hP : Invertible (codeMat 158 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 229 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 158) (codeMat 229) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 158) (codeMat 229) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o68ActualSource4 12 :=
    quotientRankAtLeast_mono step99o68s4_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o68s4_sourceU_le hMono

-- Source 5 (row 5): orbit 16, lb 12
def step99o68ActualSource5 : Submodule F2 Mat3 := spanCodes [262, 130, 68, 38, 16, 10, 1]

private theorem step99o68s5_sourceU_le :
    (o68SourceU ⟨5, by omega⟩) ≤ step99o68ActualSource5 := by
  intro M hM
  have hbool : spanContainsCodeCore [262, 130, 68, 38, 16, 10, 1] (step99o68MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 356) ⊓ kerEvalFunc (codeMat 196 + codeMat 10)) at hM
    change (evalFunc (codeMat 356) M = 0 ∧ evalFunc (codeMat 196 + codeMat 10) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 130, 68, 38, 16, 10, 1] (step99o68MatrixCodeNat M) hbool
  rwa [step99o68_codeMat_matrixCode] at hspan

private theorem step99o68s5_QtInv :
    (codeMat 489 : Mat3).transpose⁻¹ = (codeMat 241 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 489 : Mat3).transpose * (codeMat 241 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o68s5_targetSpan_le_action :
    step99o68ActualSource5 ≤ actionW (codeMat 187) (codeMat 489) step81o16s2Wspan := by
  apply step99o68_spanCodes_le_of_gens [262, 130, 68, 38, 16, 10, 1]
    (actionW (codeMat 187) (codeMat 489) step81o16s2Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 180 ∈ step81o16s2Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 180 (by decide)
    have hact : actionA (codeMat 187) (codeMat 489) (codeMat 180) = codeMat 262 := by
      unfold actionA
      rw [step99o68s5_QtInv]
      show (codeMat 187 : Mat3).transpose * codeMat 180 * (codeMat 241 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 288 ∈ step81o16s2Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 288 (by decide)
    have hact : actionA (codeMat 187) (codeMat 489) (codeMat 288) = codeMat 130 := by
      unfold actionA
      rw [step99o68s5_QtInv]
      show (codeMat 187 : Mat3).transpose * codeMat 288 * (codeMat 241 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 441 ∈ step81o16s2Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 441 (by decide)
    have hact : actionA (codeMat 187) (codeMat 489) (codeMat 441) = codeMat 68 := by
      unfold actionA
      rw [step99o68s5_QtInv]
      show (codeMat 187 : Mat3).transpose * codeMat 441 * (codeMat 241 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 258 ∈ step81o16s2Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 258 (by decide)
    have hact : actionA (codeMat 187) (codeMat 489) (codeMat 258) = codeMat 38 := by
      unfold actionA
      rw [step99o68s5_QtInv]
      show (codeMat 187 : Mat3).transpose * codeMat 258 * (codeMat 241 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ step81o16s2Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 187) (codeMat 489) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step99o68s5_QtInv]
      show (codeMat 187 : Mat3).transpose * codeMat 256 * (codeMat 241 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 196 ∈ step81o16s2Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 196 (by decide)
    have hact : actionA (codeMat 187) (codeMat 489) (codeMat 196) = codeMat 10 := by
      unfold actionA
      rw [step99o68s5_QtInv]
      show (codeMat 187 : Mat3).transpose * codeMat 196 * (codeMat 241 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 455 ∈ step81o16s2Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 455 (by decide)
    have hact : actionA (codeMat 187) (codeMat 489) (codeMat 455) = codeMat 1 := by
      unfold actionA
      rw [step99o68s5_QtInv]
      show (codeMat 187 : Mat3).transpose * codeMat 455 * (codeMat 241 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact

theorem step99o68s5Dispatch :
    QuotientRankAtLeast (o68SourceU ⟨5, by omega⟩) 12 := by
  have hP : Invertible (codeMat 187 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 489 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 187) (codeMat 489) step81o16s2Wspan) 12 :=
    @quotientRankAtLeast_action (codeMat 187) (codeMat 489) hP hQ step81o16s2Wspan 12 step81o16s2Span_lb
  have hMono : QuotientRankAtLeast step99o68ActualSource5 12 :=
    quotientRankAtLeast_mono step99o68s5_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o68s5_sourceU_le hMono

-- Source 6 (row 6): orbit 15, lb 9
def step99o68ActualSource6 : Submodule F2 Mat3 := spanCodes [260, 128, 68, 36, 16, 10, 1]

private theorem step99o68s6_sourceU_le :
    (o68SourceU ⟨6, by omega⟩) ≤ step99o68ActualSource6 := by
  intro M hM
  have hbool : spanContainsCodeCore [260, 128, 68, 36, 16, 10, 1] (step99o68MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 356) ⊓ kerEvalFunc (codeMat 10)) at hM
    change (evalFunc (codeMat 356) M = 0 ∧ evalFunc (codeMat 10) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 128, 68, 36, 16, 10, 1] (step99o68MatrixCodeNat M) hbool
  rwa [step99o68_codeMat_matrixCode] at hspan

private theorem step99o68s6_QtInv :
    (codeMat 331 : Mat3).transpose⁻¹ = (codeMat 410 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 331 : Mat3).transpose * (codeMat 410 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o68s6_targetSpan_le_action :
    step99o68ActualSource6 ≤ actionW (codeMat 244) (codeMat 331) flatW_15 := by
  apply step99o68_spanCodes_le_of_gens [260, 128, 68, 36, 16, 10, 1]
    (actionW (codeMat 244) (codeMat 331) flatW_15)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 288 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 288 (by decide)
    have hact : actionA (codeMat 244) (codeMat 331) (codeMat 288) = codeMat 260 := by
      unfold actionA
      rw [step99o68s6_QtInv]
      show (codeMat 244 : Mat3).transpose * codeMat 288 * (codeMat 410 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 244) (codeMat 331) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step99o68s6_QtInv]
      show (codeMat 244 : Mat3).transpose * codeMat 1 * (codeMat 410 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 291 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 291 (by decide)
    have hact : actionA (codeMat 244) (codeMat 331) (codeMat 291) = codeMat 68 := by
      unfold actionA
      rw [step99o68s6_QtInv]
      show (codeMat 244 : Mat3).transpose * codeMat 291 * (codeMat 410 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 244) (codeMat 331) (codeMat 256) = codeMat 36 := by
      unfold actionA
      rw [step99o68s6_QtInv]
      show (codeMat 244 : Mat3).transpose * codeMat 256 * (codeMat 410 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 9 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 9 (by decide)
    have hact : actionA (codeMat 244) (codeMat 331) (codeMat 9) = codeMat 16 := by
      unfold actionA
      rw [step99o68s6_QtInv]
      show (codeMat 244 : Mat3).transpose * codeMat 9 * (codeMat 410 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 118 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 118 (by decide)
    have hact : actionA (codeMat 244) (codeMat 331) (codeMat 118) = codeMat 10 := by
      unfold actionA
      rw [step99o68s6_QtInv]
      show (codeMat 244 : Mat3).transpose * codeMat 118 * (codeMat 410 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 511 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 511 (by decide)
    have hact : actionA (codeMat 244) (codeMat 331) (codeMat 511) = codeMat 1 := by
      unfold actionA
      rw [step99o68s6_QtInv]
      show (codeMat 244 : Mat3).transpose * codeMat 511 * (codeMat 410 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o68_codeMat_mem_actionW_of_witness hw hact

theorem step99o68s6Dispatch :
    QuotientRankAtLeast (o68SourceU ⟨6, by omega⟩) 9 := by
  have hP : Invertible (codeMat 244 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 331 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 244) (codeMat 331) flatW_15) 9 :=
    @quotientRankAtLeast_action (codeMat 244) (codeMat 331) hP hQ flatW_15 9 flatSeed_15
  have hMono : QuotientRankAtLeast step99o68ActualSource6 9 :=
    quotientRankAtLeast_mono step99o68s6_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o68s6_sourceU_le hMono

theorem step99o68_all_dispatch (i : Fin 7) :
    QuotientRankAtLeast (o68SourceU i) (o68SourceLb i) := by
  fin_cases i
  · exact step99o68s0Dispatch
  · exact step99o68s1Dispatch
  · exact step99o68s2Dispatch
  · exact step99o68s3Dispatch
  · exact step99o68s4Dispatch
  · exact step99o68s5Dispatch
  · exact step99o68s6Dispatch

theorem step99_orbit68_lb14_unconditional :
    QuotientRankAtLeast o68W 14 :=
  o68Lb14 step99o68_all_dispatch

end QiushiMatmul
