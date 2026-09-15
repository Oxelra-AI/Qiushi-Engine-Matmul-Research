import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit233Consumer
import QiushiOrbit10FP
import QiushiOrbit14FP

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc233_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc233_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc233s0_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = (codeMat 305 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * (codeMat 305 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc233s0_contain :
    (o233SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 266) (codeMat 305) orbit10W := by
  change spanCodes [260, 132, 96, 16, 8, 2, 1] ≤ actionW (codeMat 266) (codeMat 305) orbit10W
  apply step109wc233_spanCodes_le_of_gens [260, 132, 96, 16, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 305) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 432 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide)
    have hact : actionA (codeMat 266) (codeMat 305) (codeMat 432) = codeMat 260 := by
      unfold actionA
      rw [step109wc233s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 432 * (codeMat 305 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 176 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 176 (by decide)
    have hact : actionA (codeMat 266) (codeMat 305) (codeMat 176) = codeMat 132 := by
      unfold actionA
      rw [step109wc233s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 176 * (codeMat 305 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 70 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 70 (by decide)
    have hact : actionA (codeMat 266) (codeMat 305) (codeMat 70) = codeMat 96 := by
      unfold actionA
      rw [step109wc233s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 70 * (codeMat 305 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 305) (codeMat 2) = codeMat 16 := by
      unfold actionA
      rw [step109wc233s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 305 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 305) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step109wc233s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 305 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 305) (codeMat 16) = codeMat 2 := by
      unfold actionA
      rw [step109wc233s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 305 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 305) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc233s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 305 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact

theorem step109wc233s0Dispatch :
    QuotientRankAtLeast (o233SourceU_wc ⟨0, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 305) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 305) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc233s0_contain hAct


private theorem step109wc233s1_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc233s1_contain :
    (o233SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 140) (codeMat 161) orbit10W := by
  change spanCodes [256, 136, 64, 34, 16, 4, 1] ≤ actionW (codeMat 140) (codeMat 161) orbit10W
  apply step109wc233_spanCodes_le_of_gens [256, 136, 64, 34, 16, 4, 1]
    (actionW (codeMat 140) (codeMat 161) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 2) = codeMat 256 := by
      unfold actionA
      rw [step109wc233s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 68) = codeMat 136 := by
      unfold actionA
      rw [step109wc233s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 68 * (codeMat 161 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 1) = codeMat 64 := by
      unfold actionA
      rw [step109wc233s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 160) = codeMat 34 := by
      unfold actionA
      rw [step109wc233s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 160 * (codeMat 161 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step109wc233s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 256 * (codeMat 161 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 16) = codeMat 4 := by
      unfold actionA
      rw [step109wc233s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 16 * (codeMat 161 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc233s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact

theorem step109wc233s1Dispatch :
    QuotientRankAtLeast (o233SourceU_wc ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 161) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 161) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc233s1_contain hAct


private theorem step109wc233s2_QtInv :
    (codeMat 85 : Mat3).transpose⁻¹ = (codeMat 340 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 85 : Mat3).transpose * (codeMat 340 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc233s2_contain :
    (o233SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 158) (codeMat 85) orbit14W := by
  change spanCodes [260, 128, 70, 36, 16, 12, 1] ≤ actionW (codeMat 158) (codeMat 85) orbit14W
  apply step109wc233_spanCodes_le_of_gens [260, 128, 70, 36, 16, 12, 1]
    (actionW (codeMat 158) (codeMat 85) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 9 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 9 (by decide)
    have hact : actionA (codeMat 158) (codeMat 85) (codeMat 9) = codeMat 260 := by
      unfold actionA
      rw [step109wc233s2_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 9 * (codeMat 340 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 130 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 130 (by decide)
    have hact : actionA (codeMat 158) (codeMat 85) (codeMat 130) = codeMat 128 := by
      unfold actionA
      rw [step109wc233s2_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 130 * (codeMat 340 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 413 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 413 (by decide)
    have hact : actionA (codeMat 158) (codeMat 85) (codeMat 413) = codeMat 70 := by
      unfold actionA
      rw [step109wc233s2_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 413 * (codeMat 340 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 158) (codeMat 85) (codeMat 8) = codeMat 36 := by
      unfold actionA
      rw [step109wc233s2_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 8 * (codeMat 340 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 158) (codeMat 85) (codeMat 128) = codeMat 16 := by
      unfold actionA
      rw [step109wc233s2_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 128 * (codeMat 340 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 264 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 264 (by decide)
    have hact : actionA (codeMat 158) (codeMat 85) (codeMat 264) = codeMat 12 := by
      unfold actionA
      rw [step109wc233s2_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 264 * (codeMat 340 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 158) (codeMat 85) (codeMat 360) = codeMat 1 := by
      unfold actionA
      rw [step109wc233s2_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 360 * (codeMat 340 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact

theorem step109wc233s2Dispatch :
    QuotientRankAtLeast (o233SourceU_wc ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 158 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 85 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 158) (codeMat 85) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 158) (codeMat 85) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc233s2_contain hAct


private theorem step109wc233s3_QtInv :
    (codeMat 403 : Mat3).transpose⁻¹ = (codeMat 403 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 403 : Mat3).transpose * (codeMat 403 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc233s3_contain :
    (o233SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 369) (codeMat 403) orbit14W := by
  change spanCodes [258, 138, 72, 42, 16, 6, 1] ≤ actionW (codeMat 369) (codeMat 403) orbit14W
  apply step109wc233_spanCodes_le_of_gens [258, 138, 72, 42, 16, 6, 1]
    (actionW (codeMat 369) (codeMat 403) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 259 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 259 (by decide)
    have hact : actionA (codeMat 369) (codeMat 403) (codeMat 259) = codeMat 258 := by
      unfold actionA
      rw [step109wc233s3_QtInv]
      show (codeMat 369 : Mat3).transpose * codeMat 259 * (codeMat 403 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 393 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 393 (by decide)
    have hact : actionA (codeMat 369) (codeMat 403) (codeMat 393) = codeMat 138 := by
      unfold actionA
      rw [step109wc233s3_QtInv]
      show (codeMat 369 : Mat3).transpose * codeMat 393 * (codeMat 403 : Mat3).transpose = codeMat 138
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 369) (codeMat 403) (codeMat 8) = codeMat 72 := by
      unfold actionA
      rw [step109wc233s3_QtInv]
      show (codeMat 369 : Mat3).transpose * codeMat 8 * (codeMat 403 : Mat3).transpose = codeMat 72
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 362 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 362 (by decide)
    have hact : actionA (codeMat 369) (codeMat 403) (codeMat 362) = codeMat 42 := by
      unfold actionA
      rw [step109wc233s3_QtInv]
      show (codeMat 369 : Mat3).transpose * codeMat 362 * (codeMat 403 : Mat3).transpose = codeMat 42
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 511 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 511 (by decide)
    have hact : actionA (codeMat 369) (codeMat 403) (codeMat 511) = codeMat 16 := by
      unfold actionA
      rw [step109wc233s3_QtInv]
      show (codeMat 369 : Mat3).transpose * codeMat 511 * (codeMat 403 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 369) (codeMat 403) (codeMat 3) = codeMat 6 := by
      unfold actionA
      rw [step109wc233s3_QtInv]
      show (codeMat 369 : Mat3).transpose * codeMat 3 * (codeMat 403 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 369) (codeMat 403) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc233s3_QtInv]
      show (codeMat 369 : Mat3).transpose * codeMat 1 * (codeMat 403 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact

theorem step109wc233s3Dispatch :
    QuotientRankAtLeast (o233SourceU_wc ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 369 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 403 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 369) (codeMat 403) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 369) (codeMat 403) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc233s3_contain hAct


private theorem step109wc233s4_QtInv :
    (codeMat 102 : Mat3).transpose⁻¹ = (codeMat 156 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 102 : Mat3).transpose * (codeMat 156 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc233s4_contain :
    (o233SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 85) (codeMat 102) orbit10W := by
  change spanCodes [260, 130, 66, 32, 16, 14, 1] ≤ actionW (codeMat 85) (codeMat 102) orbit10W
  apply step109wc233_spanCodes_le_of_gens [260, 130, 66, 32, 16, 14, 1]
    (actionW (codeMat 85) (codeMat 102) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 3 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 85) (codeMat 102) (codeMat 3) = codeMat 260 := by
      unfold actionA
      rw [step109wc233s4_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 3 * (codeMat 156 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 85) (codeMat 102) (codeMat 1) = codeMat 130 := by
      unfold actionA
      rw [step109wc233s4_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 1 * (codeMat 156 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 324 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 324 (by decide)
    have hact : actionA (codeMat 85) (codeMat 102) (codeMat 324) = codeMat 66 := by
      unfold actionA
      rw [step109wc233s4_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 324 * (codeMat 156 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 85) (codeMat 102) (codeMat 24) = codeMat 32 := by
      unfold actionA
      rw [step109wc233s4_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 24 * (codeMat 156 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 85) (codeMat 102) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step109wc233s4_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 8 * (codeMat 156 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 85) (codeMat 102) (codeMat 160) = codeMat 14 := by
      unfold actionA
      rw [step109wc233s4_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 160 * (codeMat 156 : Mat3).transpose = codeMat 14
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 85) (codeMat 102) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc233s4_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 256 * (codeMat 156 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc233_codeMat_mem_actionW_of_witness hw hact

theorem step109wc233s4Dispatch :
    QuotientRankAtLeast (o233SourceU_wc ⟨4, by omega⟩) 12 := by
  have hP : Invertible (codeMat 85 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 102 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 85) (codeMat 102) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 85) (codeMat 102) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc233s4_contain hAct

theorem step109wc233_all_dispatch (i : Fin 5) :
    QuotientRankAtLeast (o233SourceU_wc i) (o233SourceLb_wc i) := by
  fin_cases i
  · exact step109wc233s0Dispatch
  · exact step109wc233s1Dispatch
  · exact step109wc233s2Dispatch
  · exact step109wc233s3Dispatch
  · exact step109wc233s4Dispatch

theorem step109_orbit233_lb15_wc : QuotientRankAtLeast o233W_wc 15 :=
  o233Lb15_wc step109wc233_all_dispatch

end QiushiMatmul
