import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit70Consumer
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc70_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc70_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc70s0_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = (codeMat 275 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * (codeMat 275 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc70s0_contain :
    (o70SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 266) (codeMat 275) orbit10W := by
  change spanCodes [256, 164, 96, 16, 8, 2, 1] ≤ actionW (codeMat 266) (codeMat 275) orbit10W
  apply step109wc70_spanCodes_le_of_gens [256, 164, 96, 16, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 275) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 266) (codeMat 275) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step109wc70s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 256 * (codeMat 275 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 228 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 228 (by decide)
    have hact : actionA (codeMat 266) (codeMat 275) (codeMat 228) = codeMat 164 := by
      unfold actionA
      rw [step109wc70s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 228 * (codeMat 275 : Mat3).transpose = codeMat 164
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 266) (codeMat 275) (codeMat 68) = codeMat 96 := by
      unfold actionA
      rw [step109wc70s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 68 * (codeMat 275 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 3 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 266) (codeMat 275) (codeMat 3) = codeMat 16 := by
      unfold actionA
      rw [step109wc70s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 3 * (codeMat 275 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 275) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step109wc70s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 275 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 266) (codeMat 275) (codeMat 24) = codeMat 2 := by
      unfold actionA
      rw [step109wc70s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 24 * (codeMat 275 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 275) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc70s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 275 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact

theorem step109wc70s0Dispatch :
    QuotientRankAtLeast (o70SourceU_wc ⟨0, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 275) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 275) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc70s0_contain hAct


private theorem step109wc70s1_QtInv :
    (codeMat 482 : Mat3).transpose⁻¹ = (codeMat 143 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 482 : Mat3).transpose * (codeMat 143 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc70s1_contain :
    (o70SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 95) (codeMat 482) orbit14W := by
  change spanCodes [258, 160, 96, 16, 10, 4, 1] ≤ actionW (codeMat 95) (codeMat 482) orbit14W
  apply step109wc70_spanCodes_le_of_gens [258, 160, 96, 16, 10, 4, 1]
    (actionW (codeMat 95) (codeMat 482) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 374 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 374 (by decide)
    have hact : actionA (codeMat 95) (codeMat 482) (codeMat 374) = codeMat 258 := by
      unfold actionA
      rw [step109wc70s1_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 374 * (codeMat 143 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 413 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 413 (by decide)
    have hact : actionA (codeMat 95) (codeMat 482) (codeMat 413) = codeMat 160 := by
      unfold actionA
      rw [step109wc70s1_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 413 * (codeMat 143 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 404 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 404 (by decide)
    have hact : actionA (codeMat 95) (codeMat 482) (codeMat 404) = codeMat 96 := by
      unfold actionA
      rw [step109wc70s1_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 404 * (codeMat 143 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 95) (codeMat 482) (codeMat 360) = codeMat 16 := by
      unfold actionA
      rw [step109wc70s1_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 360 * (codeMat 143 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 95) (codeMat 482) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step109wc70s1_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 96 * (codeMat 143 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 95) (codeMat 482) (codeMat 384) = codeMat 4 := by
      unfold actionA
      rw [step109wc70s1_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 384 * (codeMat 143 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 95) (codeMat 482) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc70s1_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 256 * (codeMat 143 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact

theorem step109wc70s1Dispatch :
    QuotientRankAtLeast (o70SourceU_wc ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 95 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 482 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 95) (codeMat 482) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 95) (codeMat 482) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc70s1_contain hAct


private theorem step109wc70s2_QtInv :
    (codeMat 417 : Mat3).transpose⁻¹ = (codeMat 177 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 417 : Mat3).transpose * (codeMat 177 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc70s2_contain :
    (o70SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 141) (codeMat 417) orbit14W := by
  change spanCodes [258, 132, 64, 32, 16, 10, 1] ≤ actionW (codeMat 141) (codeMat 417) orbit14W
  apply step109wc70_spanCodes_le_of_gens [258, 132, 64, 32, 16, 10, 1]
    (actionW (codeMat 141) (codeMat 417) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 22 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 22 (by decide)
    have hact : actionA (codeMat 141) (codeMat 417) (codeMat 22) = codeMat 258 := by
      unfold actionA
      rw [step109wc70s2_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 22 * (codeMat 177 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 20 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 20 (by decide)
    have hact : actionA (codeMat 141) (codeMat 417) (codeMat 20) = codeMat 132 := by
      unfold actionA
      rw [step109wc70s2_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 20 * (codeMat 177 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 9 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 9 (by decide)
    have hact : actionA (codeMat 141) (codeMat 417) (codeMat 9) = codeMat 64 := by
      unfold actionA
      rw [step109wc70s2_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 9 * (codeMat 177 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 141) (codeMat 417) (codeMat 384) = codeMat 32 := by
      unfold actionA
      rw [step109wc70s2_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 384 * (codeMat 177 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 141) (codeMat 417) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step109wc70s2_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 256 * (codeMat 177 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 141) (codeMat 417) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step109wc70s2_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 96 * (codeMat 177 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 141) (codeMat 417) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc70s2_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 8 * (codeMat 177 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact

theorem step109wc70s2Dispatch :
    QuotientRankAtLeast (o70SourceU_wc ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 141 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 141) (codeMat 417) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 141) (codeMat 417) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc70s2_contain hAct


private theorem step109wc70s3_QtInv :
    (codeMat 355 : Mat3).transpose⁻¹ = (codeMat 190 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 355 : Mat3).transpose * (codeMat 190 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc70s3_contain :
    (o70SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 214) (codeMat 355) orbit14W := by
  change spanCodes [258, 128, 68, 36, 16, 10, 1] ≤ actionW (codeMat 214) (codeMat 355) orbit14W
  apply step109wc70_spanCodes_le_of_gens [258, 128, 68, 36, 16, 10, 1]
    (actionW (codeMat 214) (codeMat 355) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 126 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 126 (by decide)
    have hact : actionA (codeMat 214) (codeMat 355) (codeMat 126) = codeMat 258 := by
      unfold actionA
      rw [step109wc70s3_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 126 * (codeMat 190 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 9 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 9 (by decide)
    have hact : actionA (codeMat 214) (codeMat 355) (codeMat 9) = codeMat 128 := by
      unfold actionA
      rw [step109wc70s3_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 9 * (codeMat 190 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 413 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 413 (by decide)
    have hact : actionA (codeMat 214) (codeMat 355) (codeMat 413) = codeMat 68 := by
      unfold actionA
      rw [step109wc70s3_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 413 * (codeMat 190 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 214) (codeMat 355) (codeMat 384) = codeMat 36 := by
      unfold actionA
      rw [step109wc70s3_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 384 * (codeMat 190 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 214) (codeMat 355) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step109wc70s3_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 8 * (codeMat 190 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 214) (codeMat 355) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step109wc70s3_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 96 * (codeMat 190 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 214) (codeMat 355) (codeMat 360) = codeMat 1 := by
      unfold actionA
      rw [step109wc70s3_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 360 * (codeMat 190 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact

theorem step109wc70s3Dispatch :
    QuotientRankAtLeast (o70SourceU_wc ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 214 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 355 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 214) (codeMat 355) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 214) (codeMat 355) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc70s3_contain hAct


private theorem step109wc70s4_QtInv :
    (codeMat 478 : Mat3).transpose⁻¹ = (codeMat 445 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 478 : Mat3).transpose * (codeMat 445 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc70s4_contain :
    (o70SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 110) (codeMat 478) flatW_15 := by
  change spanCodes [258, 162, 96, 16, 10, 6, 1] ≤ actionW (codeMat 110) (codeMat 478) flatW_15
  apply step109wc70_spanCodes_le_of_gens [258, 162, 96, 16, 10, 6, 1]
    (actionW (codeMat 110) (codeMat 478) flatW_15)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 168 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 168 (by decide)
    have hact : actionA (codeMat 110) (codeMat 478) (codeMat 168) = codeMat 258 := by
      unfold actionA
      rw [step109wc70s4_QtInv]
      show (codeMat 110 : Mat3).transpose * codeMat 168 * (codeMat 445 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 341 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 341 (by decide)
    have hact : actionA (codeMat 110) (codeMat 478) (codeMat 341) = codeMat 162 := by
      unfold actionA
      rw [step109wc70s4_QtInv]
      show (codeMat 110 : Mat3).transpose * codeMat 341 * (codeMat 445 : Mat3).transpose = codeMat 162
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 221 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 221 (by decide)
    have hact : actionA (codeMat 110) (codeMat 478) (codeMat 221) = codeMat 96 := by
      unfold actionA
      rw [step109wc70s4_QtInv]
      show (codeMat 110 : Mat3).transpose * codeMat 221 * (codeMat 445 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 511 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 511 (by decide)
    have hact : actionA (codeMat 110) (codeMat 478) (codeMat 511) = codeMat 16 := by
      unfold actionA
      rw [step109wc70s4_QtInv]
      show (codeMat 110 : Mat3).transpose * codeMat 511 * (codeMat 445 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 118 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 118 (by decide)
    have hact : actionA (codeMat 110) (codeMat 478) (codeMat 118) = codeMat 10 := by
      unfold actionA
      rw [step109wc70s4_QtInv]
      show (codeMat 110 : Mat3).transpose * codeMat 118 * (codeMat 445 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 110) (codeMat 478) (codeMat 128) = codeMat 6 := by
      unfold actionA
      rw [step109wc70s4_QtInv]
      show (codeMat 110 : Mat3).transpose * codeMat 128 * (codeMat 445 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 384 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 110) (codeMat 478) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step109wc70s4_QtInv]
      show (codeMat 110 : Mat3).transpose * codeMat 384 * (codeMat 445 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact

theorem step109wc70s4Dispatch :
    QuotientRankAtLeast (o70SourceU_wc ⟨4, by omega⟩) 9 := by
  have hP : Invertible (codeMat 110 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 478 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 110) (codeMat 478) flatW_15) 9 :=
    @quotientRankAtLeast_action (codeMat 110) (codeMat 478) hP hQ flatW_15 9
      flatSeed_15
  exact quotientRankAtLeast_mono step109wc70s4_contain hAct


private theorem step109wc70s5_QtInv :
    (codeMat 405 : Mat3).transpose⁻¹ = (codeMat 407 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 405 : Mat3).transpose * (codeMat 407 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc70s5_contain :
    (o70SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 183) (codeMat 405) flatW_15 := by
  change spanCodes [258, 134, 66, 34, 16, 10, 1] ≤ actionW (codeMat 183) (codeMat 405) flatW_15
  apply step109wc70_spanCodes_le_of_gens [258, 134, 66, 34, 16, 10, 1]
    (actionW (codeMat 183) (codeMat 405) flatW_15)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 350 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 350 (by decide)
    have hact : actionA (codeMat 183) (codeMat 405) (codeMat 350) = codeMat 258 := by
      unfold actionA
      rw [step109wc70s5_QtInv]
      show (codeMat 183 : Mat3).transpose * codeMat 350 * (codeMat 407 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 427 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 427 (by decide)
    have hact : actionA (codeMat 183) (codeMat 405) (codeMat 427) = codeMat 134 := by
      unfold actionA
      rw [step109wc70s5_QtInv]
      show (codeMat 183 : Mat3).transpose * codeMat 427 * (codeMat 407 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 126 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 126 (by decide)
    have hact : actionA (codeMat 183) (codeMat 405) (codeMat 126) = codeMat 66 := by
      unfold actionA
      rw [step109wc70s5_QtInv]
      show (codeMat 183 : Mat3).transpose * codeMat 126 * (codeMat 407 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 374 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 374 (by decide)
    have hact : actionA (codeMat 183) (codeMat 405) (codeMat 374) = codeMat 34 := by
      unfold actionA
      rw [step109wc70s5_QtInv]
      show (codeMat 183 : Mat3).transpose * codeMat 374 * (codeMat 407 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 384 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 183) (codeMat 405) (codeMat 384) = codeMat 16 := by
      unfold actionA
      rw [step109wc70s5_QtInv]
      show (codeMat 183 : Mat3).transpose * codeMat 384 * (codeMat 407 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 118 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 118 (by decide)
    have hact : actionA (codeMat 183) (codeMat 405) (codeMat 118) = codeMat 10 := by
      unfold actionA
      rw [step109wc70s5_QtInv]
      show (codeMat 183 : Mat3).transpose * codeMat 118 * (codeMat 407 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 9 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 9 (by decide)
    have hact : actionA (codeMat 183) (codeMat 405) (codeMat 9) = codeMat 1 := by
      unfold actionA
      rw [step109wc70s5_QtInv]
      show (codeMat 183 : Mat3).transpose * codeMat 9 * (codeMat 407 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact

theorem step109wc70s5Dispatch :
    QuotientRankAtLeast (o70SourceU_wc ⟨5, by omega⟩) 9 := by
  have hP : Invertible (codeMat 183 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 405 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 183) (codeMat 405) flatW_15) 9 :=
    @quotientRankAtLeast_action (codeMat 183) (codeMat 405) hP hQ flatW_15 9
      flatSeed_15
  exact quotientRankAtLeast_mono step109wc70s5_contain hAct


private theorem step109wc70s6_QtInv :
    (codeMat 111 : Mat3).transpose⁻¹ = (codeMat 412 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 111 : Mat3).transpose * (codeMat 412 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc70s6_contain :
    (o70SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 239) (codeMat 111) flatW_15 := by
  change spanCodes [258, 130, 70, 38, 16, 10, 1] ≤ actionW (codeMat 239) (codeMat 111) flatW_15
  apply step109wc70_spanCodes_le_of_gens [258, 130, 70, 38, 16, 10, 1]
    (actionW (codeMat 239) (codeMat 111) flatW_15)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 138 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 138 (by decide)
    have hact : actionA (codeMat 239) (codeMat 111) (codeMat 138) = codeMat 258 := by
      unfold actionA
      rw [step109wc70s6_QtInv]
      show (codeMat 239 : Mat3).transpose * codeMat 138 * (codeMat 412 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 239) (codeMat 111) (codeMat 8) = codeMat 130 := by
      unfold actionA
      rw [step109wc70s6_QtInv]
      show (codeMat 239 : Mat3).transpose * codeMat 8 * (codeMat 412 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 341 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 341 (by decide)
    have hact : actionA (codeMat 239) (codeMat 111) (codeMat 341) = codeMat 70 := by
      unfold actionA
      rw [step109wc70s6_QtInv]
      show (codeMat 239 : Mat3).transpose * codeMat 341 * (codeMat 412 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 137 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 137 (by decide)
    have hact : actionA (codeMat 239) (codeMat 111) (codeMat 137) = codeMat 38 := by
      unfold actionA
      rw [step109wc70s6_QtInv]
      show (codeMat 239 : Mat3).transpose * codeMat 137 * (codeMat 412 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 9 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 9 (by decide)
    have hact : actionA (codeMat 239) (codeMat 111) (codeMat 9) = codeMat 16 := by
      unfold actionA
      rw [step109wc70s6_QtInv]
      show (codeMat 239 : Mat3).transpose * codeMat 9 * (codeMat 412 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 118 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 118 (by decide)
    have hact : actionA (codeMat 239) (codeMat 111) (codeMat 118) = codeMat 10 := by
      unfold actionA
      rw [step109wc70s6_QtInv]
      show (codeMat 239 : Mat3).transpose * codeMat 118 * (codeMat 412 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 511 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 511 (by decide)
    have hact : actionA (codeMat 239) (codeMat 111) (codeMat 511) = codeMat 1 := by
      unfold actionA
      rw [step109wc70s6_QtInv]
      show (codeMat 239 : Mat3).transpose * codeMat 511 * (codeMat 412 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc70_codeMat_mem_actionW_of_witness hw hact

theorem step109wc70s6Dispatch :
    QuotientRankAtLeast (o70SourceU_wc ⟨6, by omega⟩) 9 := by
  have hP : Invertible (codeMat 239 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 111 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 239) (codeMat 111) flatW_15) 9 :=
    @quotientRankAtLeast_action (codeMat 239) (codeMat 111) hP hQ flatW_15 9
      flatSeed_15
  exact quotientRankAtLeast_mono step109wc70s6_contain hAct

theorem step109wc70_all_dispatch (i : Fin 7) :
    QuotientRankAtLeast (o70SourceU_wc i) (o70SourceLb_wc i) := by
  fin_cases i
  · exact step109wc70s0Dispatch
  · exact step109wc70s1Dispatch
  · exact step109wc70s2Dispatch
  · exact step109wc70s3Dispatch
  · exact step109wc70s4Dispatch
  · exact step109wc70s5Dispatch
  · exact step109wc70s6Dispatch

theorem step109_orbit70_lb13_wc : QuotientRankAtLeast o70W_wc 13 :=
  o70Lb13_wc step109wc70_all_dispatch

end QiushiMatmul
