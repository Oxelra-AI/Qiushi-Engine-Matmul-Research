import QiushiCodeSpanCore
import QiushiFlattenSeeds
import QiushiMonotonicity
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiOrbitTransport
import QiushiStep98Orbit69Consumer
import QiushiTransposeTransport

set_option maxHeartbeats 800000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem step99o69_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step99o69MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step99o69_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step99o69MatrixCodeNat M) = M := by decide

lemma step99o69_codeMat_matrixCode (M : Mat3) :
    codeMat (step99o69MatrixCodeNat M) = M :=
  step99o69_codeMat_matrixCode_all M

private theorem step99o69_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step99o69_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

private theorem step99o69_codeMat_mem_transposeW_of_witness
    {V : Submodule F2 Mat3} {pre tpre : Nat}
    (h_mem : codeMat tpre ∈ V)
    (h_trans : (codeMat tpre : Mat3).transpose = codeMat pre) :
    codeMat pre ∈ transposeW V := by
  change ∃ X, X ∈ V ∧ transposeLinearMap X = codeMat pre
  exact ⟨codeMat tpre, h_mem, h_trans⟩

-- Source 0 (row 0): orbit 10, lb 12
def step99o69ActualSource0 : Submodule F2 Mat3 := spanCodes [256, 164, 96, 16, 8, 2, 1]

private theorem step99o69s0_sourceU_le :
    (o69SourceU ⟨0, by omega⟩) ≤ step99o69ActualSource0 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 164, 96, 16, 8, 2, 1] (step99o69MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 132) ⊓ kerEvalFunc (codeMat 100)) at hM
    change (evalFunc (codeMat 132) M = 0 ∧ evalFunc (codeMat 100) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 8, 2, 1] (step99o69MatrixCodeNat M) hbool
  rwa [step99o69_codeMat_matrixCode] at hspan

private theorem step99o69s0_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = (codeMat 275 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * (codeMat 275 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o69s0_targetSpan_le_action :
    step99o69ActualSource0 ≤ actionW (codeMat 266) (codeMat 275) orbit10W := by
  apply step99o69_spanCodes_le_of_gens [256, 164, 96, 16, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 275) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 266) (codeMat 275) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step99o69s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 256 * (codeMat 275 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 228 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 228 (by decide)
    have hact : actionA (codeMat 266) (codeMat 275) (codeMat 228) = codeMat 164 := by
      unfold actionA
      rw [step99o69s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 228 * (codeMat 275 : Mat3).transpose = codeMat 164
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 266) (codeMat 275) (codeMat 68) = codeMat 96 := by
      unfold actionA
      rw [step99o69s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 68 * (codeMat 275 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 3 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 266) (codeMat 275) (codeMat 3) = codeMat 16 := by
      unfold actionA
      rw [step99o69s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 3 * (codeMat 275 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 275) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step99o69s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 275 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 266) (codeMat 275) (codeMat 24) = codeMat 2 := by
      unfold actionA
      rw [step99o69s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 24 * (codeMat 275 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 275) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step99o69s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 275 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact

theorem step99o69s0Dispatch :
    QuotientRankAtLeast (o69SourceU ⟨0, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 275) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 275) hP hQ orbit10W 12 orbit10_lb12
  have hMono : QuotientRankAtLeast step99o69ActualSource0 12 :=
    quotientRankAtLeast_mono step99o69s0_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o69s0_sourceU_le hMono

-- Source 1 (row 1): orbit 14, lb 12
def step99o69ActualSource1 : Submodule F2 Mat3 := spanCodes [256, 160, 96, 16, 10, 4, 1]

private theorem step99o69s1_sourceU_le :
    (o69SourceU ⟨1, by omega⟩) ≤ step99o69ActualSource1 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 160, 96, 16, 10, 4, 1] (step99o69MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 132 + codeMat 100) ⊓ kerEvalFunc (codeMat 10)) at hM
    change (evalFunc (codeMat 132 + codeMat 100) M = 0 ∧ evalFunc (codeMat 10) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 160, 96, 16, 10, 4, 1] (step99o69MatrixCodeNat M) hbool
  rwa [step99o69_codeMat_matrixCode] at hspan

private theorem step99o69s1_QtInv :
    (codeMat 226 : Mat3).transpose⁻¹ = (codeMat 141 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 226 : Mat3).transpose * (codeMat 141 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o69s1_targetSpan_le_action :
    step99o69ActualSource1 ≤ actionW (codeMat 92) (codeMat 226) orbit14W := by
  apply step99o69_spanCodes_le_of_gens [256, 160, 96, 16, 10, 4, 1]
    (actionW (codeMat 92) (codeMat 226) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 92) (codeMat 226) (codeMat 2) = codeMat 256 := by
      unfold actionA
      rw [step99o69s1_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 2 * (codeMat 141 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 149 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 149 (by decide)
    have hact : actionA (codeMat 92) (codeMat 226) (codeMat 149) = codeMat 160 := by
      unfold actionA
      rw [step99o69s1_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 149 * (codeMat 141 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 148 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 148 (by decide)
    have hact : actionA (codeMat 92) (codeMat 226) (codeMat 148) = codeMat 96 := by
      unfold actionA
      rw [step99o69s1_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 148 * (codeMat 141 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 92) (codeMat 226) (codeMat 360) = codeMat 16 := by
      unfold actionA
      rw [step99o69s1_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 360 * (codeMat 141 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 92) (codeMat 226) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step99o69s1_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 96 * (codeMat 141 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 92) (codeMat 226) (codeMat 128) = codeMat 4 := by
      unfold actionA
      rw [step99o69s1_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 128 * (codeMat 141 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 92) (codeMat 226) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step99o69s1_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 256 * (codeMat 141 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact

theorem step99o69s1Dispatch :
    QuotientRankAtLeast (o69SourceU ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 92 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 226 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 92) (codeMat 226) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 92) (codeMat 226) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o69ActualSource1 12 :=
    quotientRankAtLeast_mono step99o69s1_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o69s1_sourceU_le hMono

-- Source 2 (row 3): orbit 14, lb 12
def step99o69ActualSource2 : Submodule F2 Mat3 := spanCodes [256, 132, 64, 32, 16, 10, 1]

private theorem step99o69s2_sourceU_le :
    (o69SourceU ⟨2, by omega⟩) ≤ step99o69ActualSource2 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 132, 64, 32, 16, 10, 1] (step99o69MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 132) ⊓ kerEvalFunc (codeMat 10)) at hM
    change (evalFunc (codeMat 132) M = 0 ∧ evalFunc (codeMat 10) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 32, 16, 10, 1] (step99o69MatrixCodeNat M) hbool
  rwa [step99o69_codeMat_matrixCode] at hspan

private theorem step99o69s2_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o69s2_targetSpan_le_action :
    step99o69ActualSource2 ≤ actionW (codeMat 140) (codeMat 161) orbit14W := by
  apply step99o69_spanCodes_le_of_gens [256, 132, 64, 32, 16, 10, 1]
    (actionW (codeMat 140) (codeMat 161) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 2) = codeMat 256 := by
      unfold actionA
      rw [step99o69s2_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 20 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 20 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 20) = codeMat 132 := by
      unfold actionA
      rw [step99o69s2_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 20 * (codeMat 161 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 1) = codeMat 64 := by
      unfold actionA
      rw [step99o69s2_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 128) = codeMat 32 := by
      unfold actionA
      rw [step99o69s2_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 128 * (codeMat 161 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step99o69s2_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 256 * (codeMat 161 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step99o69s2_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 96 * (codeMat 161 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step99o69s2_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact

theorem step99o69s2Dispatch :
    QuotientRankAtLeast (o69SourceU ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 161) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 161) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o69ActualSource2 12 :=
    quotientRankAtLeast_mono step99o69s2_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o69s2_sourceU_le hMono

-- Source 3 (row 5): orbit 14, lb 12
def step99o69ActualSource3 : Submodule F2 Mat3 := spanCodes [256, 128, 68, 36, 16, 10, 1]

private theorem step99o69s3_sourceU_le :
    (o69SourceU ⟨3, by omega⟩) ≤ step99o69ActualSource3 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 128, 68, 36, 16, 10, 1] (step99o69MatrixCodeNat M) = true := by
    change M ∈ (kerEvalFunc (codeMat 100) ⊓ kerEvalFunc (codeMat 10)) at hM
    change (evalFunc (codeMat 100) M = 0 ∧ evalFunc (codeMat 10) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 36, 16, 10, 1] (step99o69MatrixCodeNat M) hbool
  rwa [step99o69_codeMat_matrixCode] at hspan

private theorem step99o69s3_QtInv :
    (codeMat 99 : Mat3).transpose⁻¹ = (codeMat 172 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 99 : Mat3).transpose * (codeMat 172 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o69s3_targetSpan_le_action :
    step99o69ActualSource3 ≤ actionW (codeMat 212) (codeMat 99) orbit14W := by
  apply step99o69_spanCodes_le_of_gens [256, 128, 68, 36, 16, 10, 1]
    (actionW (codeMat 212) (codeMat 99) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 212) (codeMat 99) (codeMat 2) = codeMat 256 := by
      unfold actionA
      rw [step99o69s3_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 2 * (codeMat 172 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 212) (codeMat 99) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step99o69s3_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 1 * (codeMat 172 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 149 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 149 (by decide)
    have hact : actionA (codeMat 212) (codeMat 99) (codeMat 149) = codeMat 68 := by
      unfold actionA
      rw [step99o69s3_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 149 * (codeMat 172 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 212) (codeMat 99) (codeMat 128) = codeMat 36 := by
      unfold actionA
      rw [step99o69s3_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 128 * (codeMat 172 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 212) (codeMat 99) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step99o69s3_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 8 * (codeMat 172 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 212) (codeMat 99) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step99o69s3_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 96 * (codeMat 172 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 212) (codeMat 99) (codeMat 360) = codeMat 1 := by
      unfold actionA
      rw [step99o69s3_QtInv]
      show (codeMat 212 : Mat3).transpose * codeMat 360 * (codeMat 172 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact

theorem step99o69s3Dispatch :
    QuotientRankAtLeast (o69SourceU ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 212 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 99 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 212) (codeMat 99) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 212) (codeMat 99) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step99o69ActualSource3 12 :=
    quotientRankAtLeast_mono step99o69s3_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o69s3_sourceU_le hMono

-- Source 4 (row 7): orbit 3, lb 9
def step99o69ActualSource4 : Submodule F2 Mat3 := spanCodes [256, 128, 66, 34, 16, 10, 6, 1]

private theorem step99o69s4_sourceU_le :
    (o69SourceU ⟨4, by omega⟩) ≤ step99o69ActualSource4 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 128, 66, 34, 16, 10, 6, 1] (step99o69MatrixCodeNat M) = true := by
    change M ∈ kerEvalFunc (codeMat 100 + codeMat 10) at hM
    change evalFunc (codeMat 100 + codeMat 10) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 128, 66, 34, 16, 10, 6, 1] (step99o69MatrixCodeNat M) hbool
  rwa [step99o69_codeMat_matrixCode] at hspan

private theorem step99o69s4_QtInv :
    (codeMat 110 : Mat3).transpose⁻¹ = (codeMat 444 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 110 : Mat3).transpose * (codeMat 444 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o69s4_targetSpan_le_action :
    step99o69ActualSource4 ≤ actionW (codeMat 84) (codeMat 110) flatW_3 := by
  apply step99o69_spanCodes_le_of_gens [256, 128, 66, 34, 16, 10, 6, 1]
    (actionW (codeMat 84) (codeMat 110) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 3 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 84) (codeMat 110) (codeMat 3) = codeMat 256 := by
      unfold actionA
      rw [step99o69s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 3 * (codeMat 444 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 110) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step99o69s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 444 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 70 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 70 (by decide)
    have hact : actionA (codeMat 84) (codeMat 110) (codeMat 70) = codeMat 66 := by
      unfold actionA
      rw [step99o69s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 70 * (codeMat 444 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 88 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 88 (by decide)
    have hact : actionA (codeMat 84) (codeMat 110) (codeMat 88) = codeMat 34 := by
      unfold actionA
      rw [step99o69s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 88 * (codeMat 444 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 110) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step99o69s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 444 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 112 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 112 (by decide)
    have hact : actionA (codeMat 84) (codeMat 110) (codeMat 112) = codeMat 10 := by
      unfold actionA
      rw [step99o69s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 112 * (codeMat 444 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 110) (codeMat 128) = codeMat 6 := by
      unfold actionA
      rw [step99o69s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 444 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 110) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step99o69s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 444 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact

theorem step99o69s4Dispatch :
    QuotientRankAtLeast (o69SourceU ⟨4, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 110 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 110) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 110) hP hQ flatW_3 9 flatSeed_3
  have hMono : QuotientRankAtLeast step99o69ActualSource4 9 :=
    quotientRankAtLeast_mono step99o69s4_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o69s4_sourceU_le hMono

-- Source 5 (row 8): orbit 3, lb 9
def step99o69ActualSource5 : Submodule F2 Mat3 := spanCodes [256, 130, 64, 32, 16, 10, 6, 1]

private theorem step99o69s5_sourceU_le :
    (o69SourceU ⟨5, by omega⟩) ≤ step99o69ActualSource5 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 130, 64, 32, 16, 10, 6, 1] (step99o69MatrixCodeNat M) = true := by
    change M ∈ kerEvalFunc (codeMat 132 + codeMat 10) at hM
    change evalFunc (codeMat 132 + codeMat 10) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 130, 64, 32, 16, 10, 6, 1] (step99o69MatrixCodeNat M) hbool
  rwa [step99o69_codeMat_matrixCode] at hspan

private theorem step99o69s5_QtInv :
    (codeMat 142 : Mat3).transpose⁻¹ = (codeMat 354 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 142 : Mat3).transpose * (codeMat 354 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o69s5_targetSpan_le_action :
    step99o69ActualSource5 ≤ actionW (codeMat 84) (codeMat 142) flatW_3 := by
  apply step99o69_spanCodes_le_of_gens [256, 130, 64, 32, 16, 10, 6, 1]
    (actionW (codeMat 84) (codeMat 142) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 142) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step99o69s5_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 354 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 325 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 325 (by decide)
    have hact : actionA (codeMat 84) (codeMat 142) (codeMat 325) = codeMat 130 := by
      unfold actionA
      rw [step99o69s5_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 325 * (codeMat 354 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 142) (codeMat 2) = codeMat 64 := by
      unfold actionA
      rw [step99o69s5_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 354 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 142) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step99o69s5_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 354 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 40 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 84) (codeMat 142) (codeMat 40) = codeMat 16 := by
      unfold actionA
      rw [step99o69s5_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 354 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 336 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 336 (by decide)
    have hact : actionA (codeMat 84) (codeMat 142) (codeMat 336) = codeMat 10 := by
      unfold actionA
      rw [step99o69s5_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 336 * (codeMat 354 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 142) (codeMat 256) = codeMat 6 := by
      unfold actionA
      rw [step99o69s5_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 354 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 142) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step99o69s5_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 354 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact

theorem step99o69s5Dispatch :
    QuotientRankAtLeast (o69SourceU ⟨5, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 142) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 142) hP hQ flatW_3 9 flatSeed_3
  have hMono : QuotientRankAtLeast step99o69ActualSource5 9 :=
    quotientRankAtLeast_mono step99o69s5_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o69s5_sourceU_le hMono

-- Source 6 (row 9): orbit 3, lb 9
def step99o69ActualSource6 : Submodule F2 Mat3 := spanCodes [256, 130, 66, 34, 16, 10, 4, 1]

private theorem step99o69s6_sourceU_le :
    (o69SourceU ⟨6, by omega⟩) ≤ step99o69ActualSource6 := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 130, 66, 34, 16, 10, 4, 1] (step99o69MatrixCodeNat M) = true := by
    change M ∈ kerEvalFunc (codeMat 132 + codeMat 100 + codeMat 10) at hM
    change evalFunc (codeMat 132 + codeMat 100 + codeMat 10) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 130, 66, 34, 16, 10, 4, 1] (step99o69MatrixCodeNat M) hbool
  rwa [step99o69_codeMat_matrixCode] at hspan

private theorem step99o69s6_QtInv :
    (codeMat 234 : Mat3).transpose⁻¹ = (codeMat 461 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 234 : Mat3).transpose * (codeMat 461 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step99o69s6_targetSpan_le_action :
    step99o69ActualSource6 ≤ actionW (codeMat 84) (codeMat 234) flatW_3 := by
  apply step99o69_spanCodes_le_of_gens [256, 130, 66, 34, 16, 10, 4, 1]
    (actionW (codeMat 84) (codeMat 234) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 2 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 234) (codeMat 2) = codeMat 256 := by
      unfold actionA
      rw [step99o69s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 461 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 325 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 325 (by decide)
    have hact : actionA (codeMat 84) (codeMat 234) (codeMat 325) = codeMat 130 := by
      unfold actionA
      rw [step99o69s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 325 * (codeMat 461 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 326 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 326 (by decide)
    have hact : actionA (codeMat 84) (codeMat 234) (codeMat 326) = codeMat 66 := by
      unfold actionA
      rw [step99o69s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 326 * (codeMat 461 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 336 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 336 (by decide)
    have hact : actionA (codeMat 84) (codeMat 234) (codeMat 336) = codeMat 34 := by
      unfold actionA
      rw [step99o69s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 336 * (codeMat 461 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 40 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 84) (codeMat 234) (codeMat 40) = codeMat 16 := by
      unfold actionA
      rw [step99o69s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 461 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 368 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 368 (by decide)
    have hact : actionA (codeMat 84) (codeMat 234) (codeMat 368) = codeMat 10 := by
      unfold actionA
      rw [step99o69s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 368 * (codeMat 461 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 234) (codeMat 128) = codeMat 4 := by
      unfold actionA
      rw [step99o69s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 461 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 234) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step99o69s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 461 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step99o69_codeMat_mem_actionW_of_witness hw hact

theorem step99o69s6Dispatch :
    QuotientRankAtLeast (o69SourceU ⟨6, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 234 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 234) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 234) hP hQ flatW_3 9 flatSeed_3
  have hMono : QuotientRankAtLeast step99o69ActualSource6 9 :=
    quotientRankAtLeast_mono step99o69s6_targetSpan_le_action hAct
  exact quotientRankAtLeast_mono step99o69s6_sourceU_le hMono

theorem step99o69_all_dispatch (i : Fin 7) :
    QuotientRankAtLeast (o69SourceU i) (o69SourceLb i) := by
  fin_cases i
  · exact step99o69s0Dispatch
  · exact step99o69s1Dispatch
  · exact step99o69s2Dispatch
  · exact step99o69s3Dispatch
  · exact step99o69s4Dispatch
  · exact step99o69s5Dispatch
  · exact step99o69s6Dispatch

theorem step99_orbit69_lb15_unconditional :
    QuotientRankAtLeast o69W 15 :=
  o69Lb15 step99o69_all_dispatch

end QiushiMatmul
