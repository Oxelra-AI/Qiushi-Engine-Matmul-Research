import QiushiCodeSpanCore
import QiushiFlattenSeeds
import QiushiMonotonicity
import QiushiOrbit14FP
import QiushiOrbitTransport
import QiushiStep81Qdim2Generated
import QiushiStep98Orbit76Consumer
import QiushiTransposeTransport

set_option maxHeartbeats 800000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem step99o76_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step99o76MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step99o76_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step99o76MatrixCodeNat M) = M := by decide

lemma step99o76_codeMat_matrixCode (M : Mat3) :
    codeMat (step99o76MatrixCodeNat M) = M :=
  step99o76_codeMat_matrixCode_all M

private theorem step99o76_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step99o76_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

private theorem step99o76_codeMat_mem_transposeW_of_witness
    {V : Submodule F2 Mat3} {pre tpre : Nat}
    (h_mem : codeMat tpre ∈ V)
    (h_trans : (codeMat tpre : Mat3).transpose = codeMat pre) :
    codeMat pre ∈ transposeW V := by
  change ∃ X, X ∈ V ∧ transposeLinearMap X = codeMat pre
  exact ⟨codeMat tpre, h_mem, h_trans⟩

-- Source 0 (row 0): orbit 17, lb 14
def step99o76ActualSource0 : Submodule F2 Mat3 := spanCodes [262, 134, 68, 38, 20, 10, 1]

private theorem step99o76s0_sourceU_le :
    (o76SourceU ⟨0, by omega⟩) ≤ step99o76ActualSource0 := by
  intro M hM
  have hbool : spanContainsCodeCore [262, 134, 68, 38, 20, 10, 1] (step99o76MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 416 + codeMat 10) ⊓ kerEvalFunc (codeMat 84 + codeMat 10)) at hM
    change (evalFunc (codeMat 416 + codeMat 10) M = 0 ∧ evalFunc (codeMat 84 + codeMat 10) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 134, 68, 38, 20, 10, 1] (step99o76MatrixCodeNat M) hbool
  rwa [step99o76_codeMat_matrixCode] at hspan

private theorem step99o76s0_QtInv :
    (codeMat 501 : Mat3).transpose⁻¹ = (codeMat 494 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 501 : Mat3).transpose * (codeMat 494 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o76s0_targetSpan_le_action :
    step99o76ActualSource0 ≤ actionW (codeMat 212) (codeMat 501) step81o17s4Wspan := by
  apply step99o76_spanCodes_le_of_gens [262, 134, 68, 38, 20, 10, 1]
    (actionW (codeMat 212) (codeMat 501) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 79 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 79 (by decide)
    have hact : actionA (codeMat 212) (codeMat 501) (codeMat 79) = codeMat 262 := by
      unfold actionA
      rw [step99o76s0_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 79 * (codeMat 494 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o76_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 78 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 212) (codeMat 501) (codeMat 78) = codeMat 134 := by
      unfold actionA
      rw [step99o76s0_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 78 * (codeMat 494 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o76_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 509 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 509 (by decide)
    have hact : actionA (codeMat 212) (codeMat 501) (codeMat 509) = codeMat 68 := by
      unfold actionA
      rw [step99o76s0_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 509 * (codeMat 494 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o76_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 112 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 112 (by decide)
    have hact : actionA (codeMat 212) (codeMat 501) (codeMat 112) = codeMat 38 := by
      unfold actionA
      rw [step99o76s0_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 112 * (codeMat 494 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o76_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 456 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 456 (by decide)
    have hact : actionA (codeMat 212) (codeMat 501) (codeMat 456) = codeMat 20 := by
      unfold actionA
      rw [step99o76s0_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 456 * (codeMat 494 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o76_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 408 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 408 (by decide)
    have hact : actionA (codeMat 212) (codeMat 501) (codeMat 408) = codeMat 10 := by
      unfold actionA
      rw [step99o76s0_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 408 * (codeMat 494 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o76_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 360 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 360 (by decide)
    have hact : actionA (codeMat 212) (codeMat 501) (codeMat 360) = codeMat 1 := by
      unfold actionA
      rw [step99o76s0_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 360 * (codeMat 494 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o76_codeMat_mem_actionW_of_witness hw hact

theorem step99o76s0Dispatch :
    QuotientRankAtLeast (o76SourceU ⟨0, by omega⟩) 14 := by
  have hP : Invertible (codeMat 212 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 501 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 212) (codeMat 501) step81o17s4Wspan) 14 :=
    @quotientRankAtLeast_action (codeMat 212) (codeMat 501) hP hQ step81o17s4Wspan 14 step81o17s4Span_lb
  have hMono : QuotientRankAtLeast step99o76ActualSource0 14 :=
    quotientRankAtLeast_mono step99o76s0_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o76s0_sourceU_le hMono

-- Source 1 (row 2): orbit 14, lb 12
def step99o76ActualSource1 : Submodule F2 Mat3 := spanCodes [288, 160, 64, 16, 10, 4, 1]

private theorem step99o76s1_sourceU_le :
    (o76SourceU ⟨1, by omega⟩) ≤ step99o76ActualSource1 := by
  intro M hM
  have hbool : spanContainsCodeCore [288, 160, 64, 16, 10, 4, 1] (step99o76MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 416) ⊓ kerEvalFunc (codeMat 10)) at hM
    change (evalFunc (codeMat 416) M = 0 ∧ evalFunc (codeMat 10) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 160, 64, 16, 10, 4, 1] (step99o76MatrixCodeNat M) hbool
  rwa [step99o76_codeMat_matrixCode] at hspan

private theorem step99o76s1_QtInv :
    (codeMat 142 : Mat3).transpose⁻¹ = (codeMat 354 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 142 : Mat3).transpose * (codeMat 354 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o76s1_targetSpan_le_action :
    step99o76ActualSource1 ≤ actionW (codeMat 305) (codeMat 142) orbit14W := by
  apply step99o76_spanCodes_le_of_gens [288, 160, 64, 16, 10, 4, 1]
    (actionW (codeMat 305) (codeMat 142) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 305) (codeMat 142) (codeMat 8) = codeMat 288 := by
      unfold actionA
      rw [step99o76s1_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 8 * (codeMat 354 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o76_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 264 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 264 (by decide)
    have hact : actionA (codeMat 305) (codeMat 142) (codeMat 264) = codeMat 160 := by
      unfold actionA
      rw [step99o76s1_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 264 * (codeMat 354 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o76_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 305) (codeMat 142) (codeMat 128) = codeMat 64 := by
      unfold actionA
      rw [step99o76s1_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 128 * (codeMat 354 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o76_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 305) (codeMat 142) (codeMat 360) = codeMat 16 := by
      unfold actionA
      rw [step99o76s1_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 360 * (codeMat 354 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o76_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 149 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 149 (by decide)
    have hact : actionA (codeMat 305) (codeMat 142) (codeMat 149) = codeMat 10 := by
      unfold actionA
      rw [step99o76s1_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 149 * (codeMat 354 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o76_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 305) (codeMat 142) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step99o76s1_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 1 * (codeMat 354 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o76_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 305) (codeMat 142) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step99o76s1_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 2 * (codeMat 354 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o76_codeMat_mem_actionW_of_witness hw hact

theorem step99o76s1Dispatch :
    QuotientRankAtLeast (o76SourceU ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 305) (codeMat 142) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 305) (codeMat 142) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o76ActualSource1 12 :=
    quotientRankAtLeast_mono step99o76s1_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o76s1_sourceU_le hMono

-- Source 2 (row 3): orbit 14, lb 12
def step99o76ActualSource2 : Submodule F2 Mat3 := spanCodes [288, 160, 66, 18, 10, 6, 1]

private theorem step99o76s2_sourceU_le :
    (o76SourceU ⟨2, by omega⟩) ≤ step99o76ActualSource2 := by
  intro M hM
  have hbool : spanContainsCodeCore [288, 160, 66, 18, 10, 6, 1] (step99o76MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 416) ⊓ kerEvalFunc (codeMat 84 + codeMat 10)) at hM
    change (evalFunc (codeMat 416) M = 0 ∧ evalFunc (codeMat 84 + codeMat 10) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 160, 66, 18, 10, 6, 1] (step99o76MatrixCodeNat M) hbool
  rwa [step99o76_codeMat_matrixCode] at hspan

private theorem step99o76s2_QtInv :
    (codeMat 442 : Mat3).transpose⁻¹ = (codeMat 334 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 442 : Mat3).transpose * (codeMat 334 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o76s2_targetSpan_le_action :
    step99o76ActualSource2 ≤ actionW (codeMat 417) (codeMat 442) orbit14W := by
  apply step99o76_spanCodes_le_of_gens [288, 160, 66, 18, 10, 6, 1]
    (actionW (codeMat 417) (codeMat 442) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 417) (codeMat 442) (codeMat 384) = codeMat 288 := by
      unfold actionA
      rw [step99o76s2_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 384 * (codeMat 334 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o76_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 392 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 392 (by decide)
    have hact : actionA (codeMat 417) (codeMat 442) (codeMat 392) = codeMat 160 := by
      unfold actionA
      rw [step99o76s2_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 392 * (codeMat 334 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o76_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 23 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 23 (by decide)
    have hact : actionA (codeMat 417) (codeMat 442) (codeMat 23) = codeMat 66 := by
      unfold actionA
      rw [step99o76s2_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 23 * (codeMat 334 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o76_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 511 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 511 (by decide)
    have hact : actionA (codeMat 417) (codeMat 442) (codeMat 511) = codeMat 18 := by
      unfold actionA
      rw [step99o76s2_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 511 * (codeMat 334 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o76_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 151 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 151 (by decide)
    have hact : actionA (codeMat 417) (codeMat 442) (codeMat 151) = codeMat 10 := by
      unfold actionA
      rw [step99o76s2_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 151 * (codeMat 334 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o76_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 417) (codeMat 442) (codeMat 1) = codeMat 6 := by
      unfold actionA
      rw [step99o76s2_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 1 * (codeMat 334 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o76_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 417) (codeMat 442) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step99o76s2_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 2 * (codeMat 334 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o76_codeMat_mem_actionW_of_witness hw hact

theorem step99o76s2Dispatch :
    QuotientRankAtLeast (o76SourceU ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 442 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 417) (codeMat 442) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 417) (codeMat 442) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o76ActualSource2 12 :=
    quotientRankAtLeast_mono step99o76s2_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o76s2_sourceU_le hMono

-- Source 3 (row 6): orbit 14, lb 12
def step99o76ActualSource3 : Submodule F2 Mat3 := spanCodes [260, 132, 68, 36, 20, 10, 1]

private theorem step99o76s3_sourceU_le :
    (o76SourceU ⟨3, by omega⟩) ≤ step99o76ActualSource3 := by
  intro M hM
  have hbool : spanContainsCodeCore [260, 132, 68, 36, 20, 10, 1] (step99o76MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 416 + codeMat 84) ⊓ kerEvalFunc (codeMat 10)) at hM
    change (evalFunc (codeMat 416 + codeMat 84) M = 0 ∧ evalFunc (codeMat 10) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 132, 68, 36, 20, 10, 1] (step99o76MatrixCodeNat M) hbool
  rwa [step99o76_codeMat_matrixCode] at hspan

private theorem step99o76s3_QtInv :
    (codeMat 87 : Mat3).transpose⁻¹ = (codeMat 468 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 87 : Mat3).transpose * (codeMat 468 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o76s3_targetSpan_le_action :
    step99o76ActualSource3 ≤ actionW (codeMat 302) (codeMat 87) orbit14W := by
  apply step99o76_spanCodes_le_of_gens [260, 132, 68, 36, 20, 10, 1]
    (actionW (codeMat 302) (codeMat 87) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 302) (codeMat 87) (codeMat 8) = codeMat 260 := by
      unfold actionA
      rw [step99o76s3_QtInv]
      show (codeMat 302 : Mat3).transpose * codeMat 8 * (codeMat 468 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o76_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 136 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 136 (by decide)
    have hact : actionA (codeMat 302) (codeMat 87) (codeMat 136) = codeMat 132 := by
      unfold actionA
      rw [step99o76s3_QtInv]
      show (codeMat 302 : Mat3).transpose * codeMat 136 * (codeMat 468 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o76_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 264 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 264 (by decide)
    have hact : actionA (codeMat 302) (codeMat 87) (codeMat 264) = codeMat 68 := by
      unfold actionA
      rw [step99o76s3_QtInv]
      show (codeMat 302 : Mat3).transpose * codeMat 264 * (codeMat 468 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o76_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 9 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 9 (by decide)
    have hact : actionA (codeMat 302) (codeMat 87) (codeMat 9) = codeMat 36 := by
      unfold actionA
      rw [step99o76s3_QtInv]
      show (codeMat 302 : Mat3).transpose * codeMat 9 * (codeMat 468 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o76_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 139 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 139 (by decide)
    have hact : actionA (codeMat 302) (codeMat 87) (codeMat 139) = codeMat 20 := by
      unfold actionA
      rw [step99o76s3_QtInv]
      show (codeMat 302 : Mat3).transpose * codeMat 139 * (codeMat 468 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o76_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 413 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 413 (by decide)
    have hact : actionA (codeMat 302) (codeMat 87) (codeMat 413) = codeMat 10 := by
      unfold actionA
      rw [step99o76s3_QtInv]
      show (codeMat 302 : Mat3).transpose * codeMat 413 * (codeMat 468 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o76_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 302) (codeMat 87) (codeMat 360) = codeMat 1 := by
      unfold actionA
      rw [step99o76s3_QtInv]
      show (codeMat 302 : Mat3).transpose * codeMat 360 * (codeMat 468 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o76_codeMat_mem_actionW_of_witness hw hact

theorem step99o76s3Dispatch :
    QuotientRankAtLeast (o76SourceU ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 302 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 87 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 302) (codeMat 87) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 302) (codeMat 87) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o76ActualSource3 12 :=
    quotientRankAtLeast_mono step99o76s3_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o76s3_sourceU_le hMono

-- Source 4 (row 7): orbit 3, lb 9
def step99o76ActualSource4 : Submodule F2 Mat3 := spanCodes [256, 128, 68, 32, 20, 8, 2, 1]

private theorem step99o76s4_sourceU_le :
    (o76SourceU ⟨4, by omega⟩) ≤ step99o76ActualSource4 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 128, 68, 32, 20, 8, 2, 1] (step99o76MatrixCodeNat M) = true := by
    change M ∈ kerEvalFunc (codeMat 84) at hM
    change evalFunc (codeMat 84) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] (step99o76MatrixCodeNat M) hbool
  rwa [step99o76_codeMat_matrixCode] at hspan

private theorem step99o76s4_contain :
    step99o76ActualSource4 ≤ flatW_3 := by
  apply step99o76_spanCodes_le_of_gens [256, 128, 68, 32, 20, 8, 2, 1] flatW_3
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 68 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 32 (by decide)
  · subst h4
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 20 (by decide)
  · subst h5
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
  · subst h6
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide)
  · subst h7
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)

theorem step99o76s4Dispatch :
    QuotientRankAtLeast (o76SourceU ⟨4, by omega⟩) 9 :=
  quotientRankAtLeast_mono (le_trans step99o76s4_sourceU_le step99o76s4_contain) flatSeed_3

theorem step99o76_all_dispatch (i : Fin 5) :
    QuotientRankAtLeast (o76SourceU i) (o76SourceLb i) := by
  fin_cases i
  · exact step99o76s0Dispatch
  · exact step99o76s1Dispatch
  · exact step99o76s2Dispatch
  · exact step99o76s3Dispatch
  · exact step99o76s4Dispatch

theorem step99_orbit76_lb15_unconditional :
    QuotientRankAtLeast o76W 15 :=
  o76Lb15 step99o76_all_dispatch

end QiushiMatmul
