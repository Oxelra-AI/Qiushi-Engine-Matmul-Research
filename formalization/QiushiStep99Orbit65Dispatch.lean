import QiushiCodeSpanCore
import QiushiFlattenSeeds
import QiushiMonotonicity
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiOrbitTransport
import QiushiStep98Orbit65Consumer

set_option maxHeartbeats 800000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem step99o65_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step99o65MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step99o65_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step99o65MatrixCodeNat M) = M := by decide

lemma step99o65_codeMat_matrixCode (M : Mat3) :
    codeMat (step99o65MatrixCodeNat M) = M :=
  step99o65_codeMat_matrixCode_all M

private theorem step99o65_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step99o65_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

-- Source 0 (row 0): orbit 10, lb 12
def step99o65ActualSource0 : Submodule F2 Mat3 := spanCodes [260, 160, 68, 16, 8, 2, 1]

private theorem step99o65s0_sourceU_le :
    (o65SourceU ⟨0, by omega⟩) ≤ step99o65ActualSource0 := by
  intro M hM
  have hbool : spanContainsCodeCore [260, 160, 68, 16, 8, 2, 1] (step99o65MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 324) ⊓ kerEvalFunc (codeMat 160)) at hM
    change (evalFunc (codeMat 324) M = 0 ∧ evalFunc (codeMat 160) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 8, 2, 1] (step99o65MatrixCodeNat M) hbool
  rwa [step99o65_codeMat_matrixCode] at hspan

private theorem step99o65s0_QtInv :
    (codeMat 298 : Mat3).transpose⁻¹ = (codeMat 270 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 298 : Mat3).transpose * (codeMat 270 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o65s0_targetSpan_le_action :
    step99o65ActualSource0 ≤ actionW (codeMat 266) (codeMat 298) orbit10W := by
  apply step99o65_spanCodes_le_of_gens [260, 160, 68, 16, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 298) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 432 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide)
    have hact : actionA (codeMat 266) (codeMat 298) (codeMat 432) = codeMat 260 := by
      unfold actionA
      rw [step99o65s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 432 * (codeMat 270 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 70 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 70 (by decide)
    have hact : actionA (codeMat 266) (codeMat 298) (codeMat 70) = codeMat 160 := by
      unfold actionA
      rw [step99o65s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 70 * (codeMat 270 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 176 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 176 (by decide)
    have hact : actionA (codeMat 266) (codeMat 298) (codeMat 176) = codeMat 68 := by
      unfold actionA
      rw [step99o65s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 176 * (codeMat 270 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 298) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step99o65s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 270 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 298) (codeMat 2) = codeMat 8 := by
      unfold actionA
      rw [step99o65s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 270 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 298) (codeMat 8) = codeMat 2 := by
      unfold actionA
      rw [step99o65s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 270 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 298) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step99o65s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 270 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact

theorem step99o65s0Dispatch :
    QuotientRankAtLeast (o65SourceU ⟨0, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 298 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 298) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 298) hP hQ orbit10W 12 orbit10_lb12
  have hMono : QuotientRankAtLeast step99o65ActualSource0 12 :=
    quotientRankAtLeast_mono step99o65s0_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o65s0_sourceU_le hMono

-- Source 1 (row 1): orbit 10, lb 12
def step99o65ActualSource1 : Submodule F2 Mat3 := spanCodes [256, 160, 64, 16, 10, 4, 1]

private theorem step99o65s1_sourceU_le :
    (o65SourceU ⟨1, by omega⟩) ≤ step99o65ActualSource1 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 160, 64, 16, 10, 4, 1] (step99o65MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 160) ⊓ kerEvalFunc (codeMat 10)) at hM
    change (evalFunc (codeMat 160) M = 0 ∧ evalFunc (codeMat 10) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 10, 4, 1] (step99o65MatrixCodeNat M) hbool
  rwa [step99o65_codeMat_matrixCode] at hspan

private theorem step99o65s1_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o65s1_targetSpan_le_action :
    step99o65ActualSource1 ≤ actionW (codeMat 140) (codeMat 140) orbit10W := by
  apply step99o65_spanCodes_le_of_gens [256, 160, 64, 16, 10, 4, 1]
    (actionW (codeMat 140) (codeMat 140) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step99o65s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 68) = codeMat 160 := by
      unfold actionA
      rw [step99o65s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 68 * (codeMat 98 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 2) = codeMat 64 := by
      unfold actionA
      rw [step99o65s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step99o65s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 256 * (codeMat 98 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step99o65s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 160 * (codeMat 98 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 8) = codeMat 4 := by
      unfold actionA
      rw [step99o65s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step99o65s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 16 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact

theorem step99o65s1Dispatch :
    QuotientRankAtLeast (o65SourceU ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 140) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 140) hP hQ orbit10W 12 orbit10_lb12
  have hMono : QuotientRankAtLeast step99o65ActualSource1 12 :=
    quotientRankAtLeast_mono step99o65s1_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o65s1_sourceU_le hMono

-- Source 2 (row 3): orbit 14, lb 12
def step99o65ActualSource2 : Submodule F2 Mat3 := spanCodes [260, 128, 68, 32, 16, 10, 1]

private theorem step99o65s2_sourceU_le :
    (o65SourceU ⟨2, by omega⟩) ≤ step99o65ActualSource2 := by
  intro M hM
  have hbool : spanContainsCodeCore [260, 128, 68, 32, 16, 10, 1] (step99o65MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 324) ⊓ kerEvalFunc (codeMat 10)) at hM
    change (evalFunc (codeMat 324) M = 0 ∧ evalFunc (codeMat 10) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 128, 68, 32, 16, 10, 1] (step99o65MatrixCodeNat M) hbool
  rwa [step99o65_codeMat_matrixCode] at hspan

private theorem step99o65s2_QtInv :
    (codeMat 85 : Mat3).transpose⁻¹ = (codeMat 340 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 85 : Mat3).transpose * (codeMat 340 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o65s2_targetSpan_le_action :
    step99o65ActualSource2 ≤ actionW (codeMat 298) (codeMat 85) orbit14W := by
  apply step99o65_spanCodes_le_of_gens [260, 128, 68, 32, 16, 10, 1]
    (actionW (codeMat 298) (codeMat 85) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 298) (codeMat 85) (codeMat 8) = codeMat 260 := by
      unfold actionA
      rw [step99o65s2_QtInv]
      show (codeMat 298 : Mat3).transpose * codeMat 8 * (codeMat 340 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 298) (codeMat 85) (codeMat 128) = codeMat 128 := by
      unfold actionA
      rw [step99o65s2_QtInv]
      show (codeMat 298 : Mat3).transpose * codeMat 128 * (codeMat 340 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 264 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 264 (by decide)
    have hact : actionA (codeMat 298) (codeMat 85) (codeMat 264) = codeMat 68 := by
      unfold actionA
      rw [step99o65s2_QtInv]
      show (codeMat 298 : Mat3).transpose * codeMat 264 * (codeMat 340 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 298) (codeMat 85) (codeMat 1) = codeMat 32 := by
      unfold actionA
      rw [step99o65s2_QtInv]
      show (codeMat 298 : Mat3).transpose * codeMat 1 * (codeMat 340 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 298) (codeMat 85) (codeMat 2) = codeMat 16 := by
      unfold actionA
      rw [step99o65s2_QtInv]
      show (codeMat 298 : Mat3).transpose * codeMat 2 * (codeMat 340 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 149 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 149 (by decide)
    have hact : actionA (codeMat 298) (codeMat 85) (codeMat 149) = codeMat 10 := by
      unfold actionA
      rw [step99o65s2_QtInv]
      show (codeMat 298 : Mat3).transpose * codeMat 149 * (codeMat 340 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 298) (codeMat 85) (codeMat 360) = codeMat 1 := by
      unfold actionA
      rw [step99o65s2_QtInv]
      show (codeMat 298 : Mat3).transpose * codeMat 360 * (codeMat 340 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact

theorem step99o65s2Dispatch :
    QuotientRankAtLeast (o65SourceU ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 298 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 85 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 298) (codeMat 85) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 298) (codeMat 85) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o65ActualSource2 12 :=
    quotientRankAtLeast_mono step99o65s2_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o65s2_sourceU_le hMono

-- Source 3 (row 6): orbit 14, lb 12
def step99o65ActualSource3 : Submodule F2 Mat3 := spanCodes [260, 134, 68, 38, 16, 10, 1]

private theorem step99o65s3_sourceU_le :
    (o65SourceU ⟨3, by omega⟩) ≤ step99o65ActualSource3 := by
  intro M hM
  have hbool : spanContainsCodeCore [260, 134, 68, 38, 16, 10, 1] (step99o65MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 324 + codeMat 10) ⊓ kerEvalFunc (codeMat 160 + codeMat 10)) at hM
    change (evalFunc (codeMat 324 + codeMat 10) M = 0 ∧ evalFunc (codeMat 160 + codeMat 10) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 134, 68, 38, 16, 10, 1] (step99o65MatrixCodeNat M) hbool
  rwa [step99o65_codeMat_matrixCode] at hspan

private theorem step99o65s3_QtInv :
    (codeMat 467 : Mat3).transpose⁻¹ = (codeMat 339 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 467 : Mat3).transpose * (codeMat 339 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o65s3_targetSpan_le_action :
    step99o65ActualSource3 ≤ actionW (codeMat 355) (codeMat 467) orbit14W := by
  apply step99o65_spanCodes_le_of_gens [260, 134, 68, 38, 16, 10, 1]
    (actionW (codeMat 355) (codeMat 467) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 355) (codeMat 467) (codeMat 256) = codeMat 260 := by
      unfold actionA
      rw [step99o65s3_QtInv]
      show (codeMat 355 : Mat3).transpose * codeMat 256 * (codeMat 339 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 224 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 224 (by decide)
    have hact : actionA (codeMat 355) (codeMat 467) (codeMat 224) = codeMat 134 := by
      unfold actionA
      rw [step99o65s3_QtInv]
      show (codeMat 355 : Mat3).transpose * codeMat 224 * (codeMat 339 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 264 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 264 (by decide)
    have hact : actionA (codeMat 355) (codeMat 467) (codeMat 264) = codeMat 68 := by
      unfold actionA
      rw [step99o65s3_QtInv]
      show (codeMat 355 : Mat3).transpose * codeMat 264 * (codeMat 339 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 508 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 508 (by decide)
    have hact : actionA (codeMat 355) (codeMat 467) (codeMat 508) = codeMat 38 := by
      unfold actionA
      rw [step99o65s3_QtInv]
      show (codeMat 355 : Mat3).transpose * codeMat 508 * (codeMat 339 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 511 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 511 (by decide)
    have hact : actionA (codeMat 355) (codeMat 467) (codeMat 511) = codeMat 16 := by
      unfold actionA
      rw [step99o65s3_QtInv]
      show (codeMat 355 : Mat3).transpose * codeMat 511 * (codeMat 339 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 149 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 149 (by decide)
    have hact : actionA (codeMat 355) (codeMat 467) (codeMat 149) = codeMat 10 := by
      unfold actionA
      rw [step99o65s3_QtInv]
      show (codeMat 355 : Mat3).transpose * codeMat 149 * (codeMat 339 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 355) (codeMat 467) (codeMat 360) = codeMat 1 := by
      unfold actionA
      rw [step99o65s3_QtInv]
      show (codeMat 355 : Mat3).transpose * codeMat 360 * (codeMat 339 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact

theorem step99o65s3Dispatch :
    QuotientRankAtLeast (o65SourceU ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 355 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 467 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 355) (codeMat 467) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 355) (codeMat 467) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o65ActualSource3 12 :=
    quotientRankAtLeast_mono step99o65s3_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o65s3_sourceU_le hMono

-- Source 4 (row 7): orbit 3, lb 9
def step99o65ActualSource4 : Submodule F2 Mat3 := spanCodes [258, 130, 66, 34, 16, 10, 6, 1]

private theorem step99o65s4_sourceU_le :
    (o65SourceU ⟨4, by omega⟩) ≤ step99o65ActualSource4 := by
  intro M hM
  have hbool : spanContainsCodeCore [258, 130, 66, 34, 16, 10, 6, 1] (step99o65MatrixCodeNat M) = true := by
    change M ∈ kerEvalFunc (codeMat 324 + codeMat 160 + codeMat 10) at hM
    change evalFunc (codeMat 324 + codeMat 160 + codeMat 10) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 130, 66, 34, 16, 10, 6, 1] (step99o65MatrixCodeNat M) hbool
  rwa [step99o65_codeMat_matrixCode] at hspan

private theorem step99o65s4_QtInv :
    (codeMat 494 : Mat3).transpose⁻¹ = (codeMat 501 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 494 : Mat3).transpose * (codeMat 501 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o65s4_targetSpan_le_action :
    step99o65ActualSource4 ≤ actionW (codeMat 84) (codeMat 494) flatW_3 := by
  apply step99o65_spanCodes_le_of_gens [258, 130, 66, 34, 16, 10, 6, 1]
    (actionW (codeMat 84) (codeMat 494) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 327 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 327 (by decide)
    have hact : actionA (codeMat 84) (codeMat 494) (codeMat 327) = codeMat 258 := by
      unfold actionA
      rw [step99o65s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 327 * (codeMat 501 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 325 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 325 (by decide)
    have hact : actionA (codeMat 84) (codeMat 494) (codeMat 325) = codeMat 130 := by
      unfold actionA
      rw [step99o65s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 325 * (codeMat 501 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 326 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 326 (by decide)
    have hact : actionA (codeMat 84) (codeMat 494) (codeMat 326) = codeMat 66 := by
      unfold actionA
      rw [step99o65s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 326 * (codeMat 501 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 376 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 376 (by decide)
    have hact : actionA (codeMat 84) (codeMat 494) (codeMat 376) = codeMat 34 := by
      unfold actionA
      rw [step99o65s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 376 * (codeMat 501 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 40 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 84) (codeMat 494) (codeMat 40) = codeMat 16 := by
      unfold actionA
      rw [step99o65s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 501 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 368 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 368 (by decide)
    have hact : actionA (codeMat 84) (codeMat 494) (codeMat 368) = codeMat 10 := by
      unfold actionA
      rw [step99o65s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 368 * (codeMat 501 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 494) (codeMat 128) = codeMat 6 := by
      unfold actionA
      rw [step99o65s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 501 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 494) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step99o65s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 501 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o65_codeMat_mem_actionW_of_witness hw hact

theorem step99o65s4Dispatch :
    QuotientRankAtLeast (o65SourceU ⟨4, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 494 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 494) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 494) hP hQ flatW_3 9 flatSeed_3
  have hMono : QuotientRankAtLeast step99o65ActualSource4 9 :=
    quotientRankAtLeast_mono step99o65s4_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o65s4_sourceU_le hMono

theorem step99o65_all_dispatch (i : Fin 5) :
    QuotientRankAtLeast (o65SourceU i) (o65SourceLb i) := by
  fin_cases i
  · exact step99o65s0Dispatch
  · exact step99o65s1Dispatch
  · exact step99o65s2Dispatch
  · exact step99o65s3Dispatch
  · exact step99o65s4Dispatch

theorem step99_orbit65_lb15_unconditional :
    QuotientRankAtLeast o65W 15 :=
  o65Lb15 step99o65_all_dispatch

end QiushiMatmul
