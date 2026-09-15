import QiushiCodeSpanCore
import QiushiFlattenSeeds
import QiushiMonotonicity
import QiushiOrbit13FP
import QiushiOrbit14FP
import QiushiOrbitTransport
import QiushiStep81Qdim2Generated
import QiushiStep98Orbit82Consumer
import QiushiTransposeTransport

set_option maxHeartbeats 800000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem step99o82_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step99o82MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step99o82_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step99o82MatrixCodeNat M) = M := by decide

lemma step99o82_codeMat_matrixCode (M : Mat3) :
    codeMat (step99o82MatrixCodeNat M) = M :=
  step99o82_codeMat_matrixCode_all M

private theorem step99o82_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step99o82_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

private theorem step99o82_codeMat_mem_transposeW_of_witness
    {V : Submodule F2 Mat3} {pre tpre : Nat}
    (h_mem : codeMat tpre ∈ V)
    (h_trans : (codeMat tpre : Mat3).transpose = codeMat pre) :
    codeMat pre ∈ transposeW V := by
  change ∃ X, X ∈ V ∧ transposeLinearMap X = codeMat pre
  exact ⟨codeMat tpre, h_mem, h_trans⟩

-- Source 0 (row 0): orbit 14, lb 12
def step99o82ActualSource0 : Submodule F2 Mat3 := spanCodes [292, 160, 96, 20, 8, 2, 1]

private theorem step99o82s0_sourceU_le :
    (o82SourceU ⟨0, by omega⟩) ≤ step99o82ActualSource0 := by
  intro M hM
  have hbool : spanContainsCodeCore [292, 160, 96, 20, 8, 2, 1] (step99o82MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 276) ⊓ kerEvalFunc (codeMat 244)) at hM
    change (evalFunc (codeMat 276) M = 0 ∧ evalFunc (codeMat 244) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 8, 2, 1] (step99o82MatrixCodeNat M) hbool
  rwa [step99o82_codeMat_matrixCode] at hspan

private theorem step99o82s0_QtInv :
    (codeMat 279 : Mat3).transpose⁻¹ = (codeMat 279 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 279 : Mat3).transpose * (codeMat 279 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o82s0_targetSpan_le_action :
    step99o82ActualSource0 ≤ actionW (codeMat 337) (codeMat 279) orbit14W := by
  apply step99o82_spanCodes_le_of_gens [292, 160, 96, 20, 8, 2, 1]
    (actionW (codeMat 337) (codeMat 279) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 337) (codeMat 279) (codeMat 360) = codeMat 292 := by
      unfold actionA
      rw [step99o82s0_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 360 * (codeMat 279 : Mat3).transpose = codeMat 292
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 235 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 235 (by decide)
    have hact : actionA (codeMat 337) (codeMat 279) (codeMat 235) = codeMat 160 := by
      unfold actionA
      rw [step99o82s0_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 235 * (codeMat 279 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 105 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 105 (by decide)
    have hact : actionA (codeMat 337) (codeMat 279) (codeMat 105) = codeMat 96 := by
      unfold actionA
      rw [step99o82s0_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 105 * (codeMat 279 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 29 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 29 (by decide)
    have hact : actionA (codeMat 337) (codeMat 279) (codeMat 29) = codeMat 20 := by
      unfold actionA
      rw [step99o82s0_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 29 * (codeMat 279 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 337) (codeMat 279) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step99o82s0_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 8 * (codeMat 279 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 337) (codeMat 279) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step99o82s0_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 3 * (codeMat 279 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 337) (codeMat 279) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step99o82s0_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 1 * (codeMat 279 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact

theorem step99o82s0Dispatch :
    QuotientRankAtLeast (o82SourceU ⟨0, by omega⟩) 12 := by
  have hP : Invertible (codeMat 337 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 279 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 337) (codeMat 279) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 337) (codeMat 279) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o82ActualSource0 12 :=
    quotientRankAtLeast_mono step99o82s0_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o82s0_sourceU_le hMono

-- Source 1 (row 1): orbit 16, lb 12
def step99o82ActualSource1 : Submodule F2 Mat3 := spanCodes [290, 160, 96, 18, 10, 6, 1]

private theorem step99o82s1_sourceU_le :
    (o82SourceU ⟨1, by omega⟩) ≤ step99o82ActualSource1 := by
  intro M hM
  have hbool : spanContainsCodeCore [290, 160, 96, 18, 10, 6, 1] (step99o82MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 276 + codeMat 10) ⊓ kerEvalFunc (codeMat 244 + codeMat 10)) at hM
    change (evalFunc (codeMat 276 + codeMat 10) M = 0 ∧ evalFunc (codeMat 244 + codeMat 10) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 18, 10, 6, 1] (step99o82MatrixCodeNat M) hbool
  rwa [step99o82_codeMat_matrixCode] at hspan

private theorem step99o82s1_QtInv :
    (codeMat 443 : Mat3).transpose⁻¹ = (codeMat 254 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 443 : Mat3).transpose * (codeMat 254 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o82s1_targetSpan_le_action :
    step99o82ActualSource1 ≤ actionW (codeMat 161) (codeMat 443) step81o16s2Wspan := by
  apply step99o82_spanCodes_le_of_gens [290, 160, 96, 18, 10, 6, 1]
    (actionW (codeMat 161) (codeMat 443) step81o16s2Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 439 ∈ step81o16s2Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 439 (by decide)
    have hact : actionA (codeMat 161) (codeMat 443) (codeMat 439) = codeMat 290 := by
      unfold actionA
      rw [step99o82s1_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 439 * (codeMat 254 : Mat3).transpose = codeMat 290
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 440 ∈ step81o16s2Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 440 (by decide)
    have hact : actionA (codeMat 161) (codeMat 443) (codeMat 440) = codeMat 160 := by
      unfold actionA
      rw [step99o82s1_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 440 * (codeMat 254 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 408 ∈ step81o16s2Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 408 (by decide)
    have hact : actionA (codeMat 161) (codeMat 443) (codeMat 408) = codeMat 96 := by
      unfold actionA
      rw [step99o82s1_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 408 * (codeMat 254 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 455 ∈ step81o16s2Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 455 (by decide)
    have hact : actionA (codeMat 161) (codeMat 443) (codeMat 455) = codeMat 18 := by
      unfold actionA
      rw [step99o82s1_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 455 * (codeMat 254 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 199 ∈ step81o16s2Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 199 (by decide)
    have hact : actionA (codeMat 161) (codeMat 443) (codeMat 199) = codeMat 10 := by
      unfold actionA
      rw [step99o82s1_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 199 * (codeMat 254 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ step81o16s2Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 443) (codeMat 1) = codeMat 6 := by
      unfold actionA
      rw [step99o82s1_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 254 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ step81o16s2Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 161) (codeMat 443) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step99o82s1_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 3 * (codeMat 254 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact

theorem step99o82s1Dispatch :
    QuotientRankAtLeast (o82SourceU ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 443 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 443) step81o16s2Wspan) 12 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 443) hP hQ step81o16s2Wspan 12 step81o16s2Span_lb
  have hMono : QuotientRankAtLeast step99o82ActualSource1 12 :=
    quotientRankAtLeast_mono step99o82s1_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o82s1_sourceU_le hMono

-- Source 2 (row 2): orbit 14, lb 12
def step99o82ActualSource2 : Submodule F2 Mat3 := spanCodes [260, 128, 64, 32, 20, 10, 1]

private theorem step99o82s2_sourceU_le :
    (o82SourceU ⟨2, by omega⟩) ≤ step99o82ActualSource2 := by
  intro M hM
  have hbool : spanContainsCodeCore [260, 128, 64, 32, 20, 10, 1] (step99o82MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 276) ⊓ kerEvalFunc (codeMat 10)) at hM
    change (evalFunc (codeMat 276) M = 0 ∧ evalFunc (codeMat 10) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 128, 64, 32, 20, 10, 1] (step99o82MatrixCodeNat M) hbool
  rwa [step99o82_codeMat_matrixCode] at hspan

private theorem step99o82s2_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o82s2_targetSpan_le_action :
    step99o82ActualSource2 ≤ actionW (codeMat 277) (codeMat 140) orbit14W := by
  apply step99o82_spanCodes_le_of_gens [260, 128, 64, 32, 20, 10, 1]
    (actionW (codeMat 277) (codeMat 140) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 277) (codeMat 140) (codeMat 1) = codeMat 260 := by
      unfold actionA
      rw [step99o82s2_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 277) (codeMat 140) (codeMat 256) = codeMat 128 := by
      unfold actionA
      rw [step99o82s2_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 256 * (codeMat 98 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 277) (codeMat 140) (codeMat 128) = codeMat 64 := by
      unfold actionA
      rw [step99o82s2_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 128 * (codeMat 98 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 277) (codeMat 140) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step99o82s2_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 97 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 97 (by decide)
    have hact : actionA (codeMat 277) (codeMat 140) (codeMat 97) = codeMat 20 := by
      unfold actionA
      rw [step99o82s2_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 97 * (codeMat 98 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 276 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 276 (by decide)
    have hact : actionA (codeMat 277) (codeMat 140) (codeMat 276) = codeMat 10 := by
      unfold actionA
      rw [step99o82s2_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 276 * (codeMat 98 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 130 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 130 (by decide)
    have hact : actionA (codeMat 277) (codeMat 140) (codeMat 130) = codeMat 1 := by
      unfold actionA
      rw [step99o82s2_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 130 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact

theorem step99o82s2Dispatch :
    QuotientRankAtLeast (o82SourceU ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 277 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 277) (codeMat 140) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 277) (codeMat 140) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o82ActualSource2 12 :=
    quotientRankAtLeast_mono step99o82s2_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o82s2_sourceU_le hMono

-- Source 3 (row 3): orbit 14, lb 12
def step99o82ActualSource3 : Submodule F2 Mat3 := spanCodes [262, 130, 66, 34, 20, 10, 1]

private theorem step99o82s3_sourceU_le :
    (o82SourceU ⟨3, by omega⟩) ≤ step99o82ActualSource3 := by
  intro M hM
  have hbool : spanContainsCodeCore [262, 130, 66, 34, 20, 10, 1] (step99o82MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 276) ⊓ kerEvalFunc (codeMat 244 + codeMat 10)) at hM
    change (evalFunc (codeMat 276) M = 0 ∧ evalFunc (codeMat 244 + codeMat 10) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 130, 66, 34, 20, 10, 1] (step99o82MatrixCodeNat M) hbool
  rwa [step99o82_codeMat_matrixCode] at hspan

private theorem step99o82s3_QtInv :
    (codeMat 165 : Mat3).transpose⁻¹ = (codeMat 163 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 165 : Mat3).transpose * (codeMat 163 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o82s3_targetSpan_le_action :
    step99o82ActualSource3 ≤ actionW (codeMat 335) (codeMat 165) orbit14W := by
  apply step99o82_spanCodes_le_of_gens [262, 130, 66, 34, 20, 10, 1]
    (actionW (codeMat 335) (codeMat 165) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 224 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 224 (by decide)
    have hact : actionA (codeMat 335) (codeMat 165) (codeMat 224) = codeMat 262 := by
      unfold actionA
      rw [step99o82s3_QtInv]
      show (codeMat 335 : Mat3).transpose * codeMat 224 * (codeMat 163 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 335) (codeMat 165) (codeMat 256) = codeMat 130 := by
      unfold actionA
      rw [step99o82s3_QtInv]
      show (codeMat 335 : Mat3).transpose * codeMat 256 * (codeMat 163 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 104 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 104 (by decide)
    have hact : actionA (codeMat 335) (codeMat 165) (codeMat 104) = codeMat 66 := by
      unfold actionA
      rw [step99o82s3_QtInv]
      show (codeMat 335 : Mat3).transpose * codeMat 104 * (codeMat 163 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 227 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 227 (by decide)
    have hact : actionA (codeMat 335) (codeMat 165) (codeMat 227) = codeMat 34 := by
      unfold actionA
      rw [step99o82s3_QtInv]
      show (codeMat 335 : Mat3).transpose * codeMat 227 * (codeMat 163 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 284 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 284 (by decide)
    have hact : actionA (codeMat 335) (codeMat 165) (codeMat 284) = codeMat 20 := by
      unfold actionA
      rw [step99o82s3_QtInv]
      show (codeMat 335 : Mat3).transpose * codeMat 284 * (codeMat 163 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 97 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 97 (by decide)
    have hact : actionA (codeMat 335) (codeMat 165) (codeMat 97) = codeMat 10 := by
      unfold actionA
      rw [step99o82s3_QtInv]
      show (codeMat 335 : Mat3).transpose * codeMat 97 * (codeMat 163 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 335) (codeMat 165) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step99o82s3_QtInv]
      show (codeMat 335 : Mat3).transpose * codeMat 8 * (codeMat 163 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact

theorem step99o82s3Dispatch :
    QuotientRankAtLeast (o82SourceU ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 335 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 165 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 335) (codeMat 165) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 335) (codeMat 165) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o82ActualSource3 12 :=
    quotientRankAtLeast_mono step99o82s3_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o82s3_sourceU_le hMono

-- Source 4 (row 4): orbit 13, lb 12
def step99o82ActualSource4 : Submodule F2 Mat3 := spanCodes [256, 132, 68, 36, 20, 10, 1]

private theorem step99o82s4_sourceU_le :
    (o82SourceU ⟨4, by omega⟩) ≤ step99o82ActualSource4 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 132, 68, 36, 20, 10, 1] (step99o82MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 244) ⊓ kerEvalFunc (codeMat 10)) at hM
    change (evalFunc (codeMat 244) M = 0 ∧ evalFunc (codeMat 10) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 132, 68, 36, 20, 10, 1] (step99o82MatrixCodeNat M) hbool
  rwa [step99o82_codeMat_matrixCode] at hspan

private theorem step99o82s4_QtInv :
    (codeMat 207 : Mat3).transpose⁻¹ = (codeMat 370 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 207 : Mat3).transpose * (codeMat 370 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o82s4_targetSpan_le_action :
    step99o82ActualSource4 ≤ actionW (codeMat 156) (codeMat 207) orbit13W := by
  apply step99o82_spanCodes_le_of_gens [256, 132, 68, 36, 20, 10, 1]
    (actionW (codeMat 156) (codeMat 207) orbit13W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 156) (codeMat 207) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step99o82s4_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 1 * (codeMat 370 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 77 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 77 (by decide)
    have hact : actionA (codeMat 156) (codeMat 207) (codeMat 77) = codeMat 132 := by
      unfold actionA
      rw [step99o82s4_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 77 * (codeMat 370 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 79 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 79 (by decide)
    have hact : actionA (codeMat 156) (codeMat 207) (codeMat 79) = codeMat 68 := by
      unfold actionA
      rw [step99o82s4_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 79 * (codeMat 370 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 156) (codeMat 207) (codeMat 8) = codeMat 36 := by
      unfold actionA
      rw [step99o82s4_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 8 * (codeMat 370 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 264 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 264 (by decide)
    have hact : actionA (codeMat 156) (codeMat 207) (codeMat 264) = codeMat 20 := by
      unfold actionA
      rw [step99o82s4_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 264 * (codeMat 370 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 168 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 168 (by decide)
    have hact : actionA (codeMat 156) (codeMat 207) (codeMat 168) = codeMat 10 := by
      unfold actionA
      rw [step99o82s4_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 168 * (codeMat 370 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 504 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 504 (by decide)
    have hact : actionA (codeMat 156) (codeMat 207) (codeMat 504) = codeMat 1 := by
      unfold actionA
      rw [step99o82s4_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 504 * (codeMat 370 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact

theorem step99o82s4Dispatch :
    QuotientRankAtLeast (o82SourceU ⟨4, by omega⟩) 12 := by
  have hP : Invertible (codeMat 156 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 207 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 156) (codeMat 207) orbit13W) 12 :=
    @quotientRankAtLeast_action (codeMat 156) (codeMat 207) hP hQ orbit13W 12 orbit13_lb12
  have hMono : QuotientRankAtLeast step99o82ActualSource4 12 :=
    quotientRankAtLeast_mono step99o82s4_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o82s4_sourceU_le hMono

-- Source 5 (row 5): orbit 16, lb 12
def step99o82ActualSource5 : Submodule F2 Mat3 := spanCodes [258, 134, 70, 38, 20, 10, 1]

private theorem step99o82s5_sourceU_le :
    (o82SourceU ⟨5, by omega⟩) ≤ step99o82ActualSource5 := by
  intro M hM
  have hbool : spanContainsCodeCore [258, 134, 70, 38, 20, 10, 1] (step99o82MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 276 + codeMat 10) ⊓ kerEvalFunc (codeMat 244)) at hM
    change (evalFunc (codeMat 276 + codeMat 10) M = 0 ∧ evalFunc (codeMat 244) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 134, 70, 38, 20, 10, 1] (step99o82MatrixCodeNat M) hbool
  rwa [step99o82_codeMat_matrixCode] at hspan

private theorem step99o82s5_QtInv :
    (codeMat 122 : Mat3).transpose⁻¹ = (codeMat 460 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 122 : Mat3).transpose * (codeMat 460 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o82s5_targetSpan_le_action :
    step99o82ActualSource5 ≤ actionW (codeMat 351) (codeMat 122) step81o16s2Wspan := by
  apply step99o82_spanCodes_le_of_gens [258, 134, 70, 38, 20, 10, 1]
    (actionW (codeMat 351) (codeMat 122) step81o16s2Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 201 ∈ step81o16s2Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 201 (by decide)
    have hact : actionA (codeMat 351) (codeMat 122) (codeMat 201) = codeMat 258 := by
      unfold actionA
      rw [step99o82s5_QtInv]
      show (codeMat 351 : Mat3).transpose * codeMat 201 * (codeMat 460 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 82 ∈ step81o16s2Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 82 (by decide)
    have hact : actionA (codeMat 351) (codeMat 122) (codeMat 82) = codeMat 134 := by
      unfold actionA
      rw [step99o82s5_QtInv]
      show (codeMat 351 : Mat3).transpose * codeMat 82 * (codeMat 460 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 127 ∈ step81o16s2Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 127 (by decide)
    have hact : actionA (codeMat 351) (codeMat 122) (codeMat 127) = codeMat 70 := by
      unfold actionA
      rw [step99o82s5_QtInv]
      show (codeMat 351 : Mat3).transpose * codeMat 127 * (codeMat 460 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 203 ∈ step81o16s2Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 203 (by decide)
    have hact : actionA (codeMat 351) (codeMat 122) (codeMat 203) = codeMat 38 := by
      unfold actionA
      rw [step99o82s5_QtInv]
      show (codeMat 351 : Mat3).transpose * codeMat 203 * (codeMat 460 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 81 ∈ step81o16s2Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 81 (by decide)
    have hact : actionA (codeMat 351) (codeMat 122) (codeMat 81) = codeMat 20 := by
      unfold actionA
      rw [step99o82s5_QtInv]
      show (codeMat 351 : Mat3).transpose * codeMat 81 * (codeMat 460 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 349 ∈ step81o16s2Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 349 (by decide)
    have hact : actionA (codeMat 351) (codeMat 122) (codeMat 349) = codeMat 10 := by
      unfold actionA
      rw [step99o82s5_QtInv]
      show (codeMat 351 : Mat3).transpose * codeMat 349 * (codeMat 460 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 438 ∈ step81o16s2Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 438 (by decide)
    have hact : actionA (codeMat 351) (codeMat 122) (codeMat 438) = codeMat 1 := by
      unfold actionA
      rw [step99o82s5_QtInv]
      show (codeMat 351 : Mat3).transpose * codeMat 438 * (codeMat 460 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact

theorem step99o82s5Dispatch :
    QuotientRankAtLeast (o82SourceU ⟨5, by omega⟩) 12 := by
  have hP : Invertible (codeMat 351 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 122 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 351) (codeMat 122) step81o16s2Wspan) 12 :=
    @quotientRankAtLeast_action (codeMat 351) (codeMat 122) hP hQ step81o16s2Wspan 12 step81o16s2Span_lb
  have hMono : QuotientRankAtLeast step99o82ActualSource5 12 :=
    quotientRankAtLeast_mono step99o82s5_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o82s5_sourceU_le hMono

-- Source 6 (row 6): orbit 15, lb 9
def step99o82ActualSource6 : Submodule F2 Mat3 := spanCodes [288, 160, 96, 16, 10, 4, 1]

private theorem step99o82s6_sourceU_le :
    (o82SourceU ⟨6, by omega⟩) ≤ step99o82ActualSource6 := by
  intro M hM
  have hbool : spanContainsCodeCore [288, 160, 96, 16, 10, 4, 1] (step99o82MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 276 + codeMat 244) ⊓ kerEvalFunc (codeMat 10)) at hM
    change (evalFunc (codeMat 276 + codeMat 244) M = 0 ∧ evalFunc (codeMat 10) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 160, 96, 16, 10, 4, 1] (step99o82MatrixCodeNat M) hbool
  rwa [step99o82_codeMat_matrixCode] at hspan

private theorem step99o82s6_QtInv :
    (codeMat 467 : Mat3).transpose⁻¹ = (codeMat 339 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 467 : Mat3).transpose * (codeMat 339 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o82s6_targetSpan_le_action :
    step99o82ActualSource6 ≤ actionW (codeMat 460) (codeMat 467) flatW_15 := by
  apply step99o82_spanCodes_le_of_gens [288, 160, 96, 16, 10, 4, 1]
    (actionW (codeMat 460) (codeMat 467) flatW_15)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 288 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 288 (by decide)
    have hact : actionA (codeMat 460) (codeMat 467) (codeMat 288) = codeMat 288 := by
      unfold actionA
      rw [step99o82s6_QtInv]
      show (codeMat 460 : Mat3).transpose * codeMat 288 * (codeMat 339 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 291 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 291 (by decide)
    have hact : actionA (codeMat 460) (codeMat 467) (codeMat 291) = codeMat 160 := by
      unfold actionA
      rw [step99o82s6_QtInv]
      show (codeMat 460 : Mat3).transpose * codeMat 291 * (codeMat 339 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 289 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 289 (by decide)
    have hact : actionA (codeMat 460) (codeMat 467) (codeMat 289) = codeMat 96 := by
      unfold actionA
      rw [step99o82s6_QtInv]
      show (codeMat 460 : Mat3).transpose * codeMat 289 * (codeMat 339 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 511 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 511 (by decide)
    have hact : actionA (codeMat 460) (codeMat 467) (codeMat 511) = codeMat 16 := by
      unfold actionA
      rw [step99o82s6_QtInv]
      show (codeMat 460 : Mat3).transpose * codeMat 511 * (codeMat 339 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 341 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 341 (by decide)
    have hact : actionA (codeMat 460) (codeMat 467) (codeMat 341) = codeMat 10 := by
      unfold actionA
      rw [step99o82s6_QtInv]
      show (codeMat 460 : Mat3).transpose * codeMat 341 * (codeMat 339 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 460) (codeMat 467) (codeMat 32) = codeMat 4 := by
      unfold actionA
      rw [step99o82s6_QtInv]
      show (codeMat 460 : Mat3).transpose * codeMat 32 * (codeMat 339 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 40 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 460) (codeMat 467) (codeMat 40) = codeMat 1 := by
      unfold actionA
      rw [step99o82s6_QtInv]
      show (codeMat 460 : Mat3).transpose * codeMat 40 * (codeMat 339 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o82_codeMat_mem_actionW_of_witness hw hact

theorem step99o82s6Dispatch :
    QuotientRankAtLeast (o82SourceU ⟨6, by omega⟩) 9 := by
  have hP : Invertible (codeMat 460 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 467 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 460) (codeMat 467) flatW_15) 9 :=
    @quotientRankAtLeast_action (codeMat 460) (codeMat 467) hP hQ flatW_15 9 flatSeed_15
  have hMono : QuotientRankAtLeast step99o82ActualSource6 9 :=
    quotientRankAtLeast_mono step99o82s6_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o82s6_sourceU_le hMono

theorem step99o82_all_dispatch (i : Fin 7) :
    QuotientRankAtLeast (o82SourceU i) (o82SourceLb i) := by
  fin_cases i
  · exact step99o82s0Dispatch
  · exact step99o82s1Dispatch
  · exact step99o82s2Dispatch
  · exact step99o82s3Dispatch
  · exact step99o82s4Dispatch
  · exact step99o82s5Dispatch
  · exact step99o82s6Dispatch

theorem step99_orbit82_lb14_unconditional :
    QuotientRankAtLeast o82W 14 :=
  o82Lb14 step99o82_all_dispatch

end QiushiMatmul
