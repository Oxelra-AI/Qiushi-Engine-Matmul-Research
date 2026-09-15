import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit183Consumer
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc183_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc183_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc183s0_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc183s0_contain :
    (o183SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 84) (codeMat 84) orbit10W := by
  change spanCodes [256, 128, 68, 32, 16, 10, 1] ≤ actionW (codeMat 84) (codeMat 84) orbit10W
  apply step109wc183_spanCodes_le_of_gens [256, 128, 68, 32, 16, 10, 1]
    (actionW (codeMat 84) (codeMat 84) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc183s0_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 2) = codeMat 128 := by
      unfold actionA
      rw [step109wc183s0_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step109wc183s0_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 68 * (codeMat 84 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc183s0_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 84 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 16) = codeMat 16 := by
      unfold actionA
      rw [step109wc183s0_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 16 * (codeMat 84 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc183s0_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 160 * (codeMat 84 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc183s0_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact

theorem step109wc183s0Dispatch :
    QuotientRankAtLeast (o183SourceU_wc ⟨0, by omega⟩) 12 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 84) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 84) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc183s0_contain hAct


private theorem step109wc183s1_QtInv :
    (codeMat 421 : Mat3).transpose⁻¹ = (codeMat 179 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 421 : Mat3).transpose * (codeMat 179 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc183s1_contain :
    (o183SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 460) (codeMat 421) orbit14W := by
  change spanCodes [262, 134, 64, 32, 20, 10, 1] ≤ actionW (codeMat 460) (codeMat 421) orbit14W
  apply step109wc183_spanCodes_le_of_gens [262, 134, 64, 32, 20, 10, 1]
    (actionW (codeMat 460) (codeMat 421) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 31 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 31 (by decide)
    have hact : actionA (codeMat 460) (codeMat 421) (codeMat 31) = codeMat 262 := by
      unfold actionA
      rw [step109wc183s1_QtInv]
      show (codeMat 460 : Mat3).transpose * codeMat 31 * (codeMat 179 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 28 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 28 (by decide)
    have hact : actionA (codeMat 460) (codeMat 421) (codeMat 28) = codeMat 134 := by
      unfold actionA
      rw [step109wc183s1_QtInv]
      show (codeMat 460 : Mat3).transpose * codeMat 28 * (codeMat 179 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 460) (codeMat 421) (codeMat 1) = codeMat 64 := by
      unfold actionA
      rw [step109wc183s1_QtInv]
      show (codeMat 460 : Mat3).transpose * codeMat 1 * (codeMat 179 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 511 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 511 (by decide)
    have hact : actionA (codeMat 460) (codeMat 421) (codeMat 511) = codeMat 32 := by
      unfold actionA
      rw [step109wc183s1_QtInv]
      show (codeMat 460 : Mat3).transpose * codeMat 511 * (codeMat 179 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 284 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 284 (by decide)
    have hact : actionA (codeMat 460) (codeMat 421) (codeMat 284) = codeMat 20 := by
      unfold actionA
      rw [step109wc183s1_QtInv]
      show (codeMat 460 : Mat3).transpose * codeMat 284 * (codeMat 179 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 105 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 105 (by decide)
    have hact : actionA (codeMat 460) (codeMat 421) (codeMat 105) = codeMat 10 := by
      unfold actionA
      rw [step109wc183s1_QtInv]
      show (codeMat 460 : Mat3).transpose * codeMat 105 * (codeMat 179 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 460) (codeMat 421) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc183s1_QtInv]
      show (codeMat 460 : Mat3).transpose * codeMat 8 * (codeMat 179 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact

theorem step109wc183s1Dispatch :
    QuotientRankAtLeast (o183SourceU_wc ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 460 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 421 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 460) (codeMat 421) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 460) (codeMat 421) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc183s1_contain hAct


private theorem step109wc183s2_QtInv :
    (codeMat 423 : Mat3).transpose⁻¹ = (codeMat 181 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 423 : Mat3).transpose * (codeMat 181 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc183s2_contain :
    (o183SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 271) (codeMat 423) orbit14W := by
  change spanCodes [258, 130, 66, 32, 22, 10, 1] ≤ actionW (codeMat 271) (codeMat 423) orbit14W
  apply step109wc183_spanCodes_le_of_gens [258, 130, 66, 32, 22, 10, 1]
    (actionW (codeMat 271) (codeMat 423) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 488 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 488 (by decide)
    have hact : actionA (codeMat 271) (codeMat 423) (codeMat 488) = codeMat 258 := by
      unfold actionA
      rw [step109wc183s2_QtInv]
      show (codeMat 271 : Mat3).transpose * codeMat 488 * (codeMat 181 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 271) (codeMat 423) (codeMat 360) = codeMat 130 := by
      unfold actionA
      rw [step109wc183s2_QtInv]
      show (codeMat 271 : Mat3).transpose * codeMat 360 * (codeMat 181 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 104 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 104 (by decide)
    have hact : actionA (codeMat 271) (codeMat 423) (codeMat 104) = codeMat 66 := by
      unfold actionA
      rw [step109wc183s2_QtInv]
      show (codeMat 271 : Mat3).transpose * codeMat 104 * (codeMat 181 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 511 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 511 (by decide)
    have hact : actionA (codeMat 271) (codeMat 423) (codeMat 511) = codeMat 32 := by
      unfold actionA
      rw [step109wc183s2_QtInv]
      show (codeMat 271 : Mat3).transpose * codeMat 511 * (codeMat 181 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 381 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 381 (by decide)
    have hact : actionA (codeMat 271) (codeMat 423) (codeMat 381) = codeMat 22 := by
      unfold actionA
      rw [step109wc183s2_QtInv]
      show (codeMat 271 : Mat3).transpose * codeMat 381 * (codeMat 181 : Mat3).transpose = codeMat 22
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 97 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 97 (by decide)
    have hact : actionA (codeMat 271) (codeMat 423) (codeMat 97) = codeMat 10 := by
      unfold actionA
      rw [step109wc183s2_QtInv]
      show (codeMat 271 : Mat3).transpose * codeMat 97 * (codeMat 181 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 271) (codeMat 423) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc183s2_QtInv]
      show (codeMat 271 : Mat3).transpose * codeMat 8 * (codeMat 181 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact

theorem step109wc183s2Dispatch :
    QuotientRankAtLeast (o183SourceU_wc ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 271 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 423 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 271) (codeMat 423) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 271) (codeMat 423) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc183s2_contain hAct


private theorem step109wc183s3_QtInv :
    (codeMat 244 : Mat3).transpose⁻¹ = (codeMat 95 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 244 : Mat3).transpose * (codeMat 95 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc183s3_contain :
    (o183SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 85) (codeMat 244) orbit10W := by
  change spanCodes [260, 132, 70, 32, 18, 10, 1] ≤ actionW (codeMat 85) (codeMat 244) orbit10W
  apply step109wc183_spanCodes_le_of_gens [260, 132, 70, 32, 18, 10, 1]
    (actionW (codeMat 85) (codeMat 244) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 3 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 85) (codeMat 244) (codeMat 3) = codeMat 260 := by
      unfold actionA
      rw [step109wc183s3_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 3 * (codeMat 95 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 326 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 326 (by decide)
    have hact : actionA (codeMat 85) (codeMat 244) (codeMat 326) = codeMat 132 := by
      unfold actionA
      rw [step109wc183s3_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 326 * (codeMat 95 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 85) (codeMat 244) (codeMat 68) = codeMat 70 := by
      unfold actionA
      rw [step109wc183s3_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 68 * (codeMat 95 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 85) (codeMat 244) (codeMat 24) = codeMat 32 := by
      unfold actionA
      rw [step109wc183s3_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 24 * (codeMat 95 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 432 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide)
    have hact : actionA (codeMat 85) (codeMat 244) (codeMat 432) = codeMat 18 := by
      unfold actionA
      rw [step109wc183s3_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 432 * (codeMat 95 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 416 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 416 (by decide)
    have hact : actionA (codeMat 85) (codeMat 244) (codeMat 416) = codeMat 10 := by
      unfold actionA
      rw [step109wc183s3_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 416 * (codeMat 95 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 85) (codeMat 244) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc183s3_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 256 * (codeMat 95 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact

theorem step109wc183s3Dispatch :
    QuotientRankAtLeast (o183SourceU_wc ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 85 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 244 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 85) (codeMat 244) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 85) (codeMat 244) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc183s3_contain hAct


private theorem step109wc183s4_QtInv :
    (codeMat 177 : Mat3).transpose⁻¹ = (codeMat 417 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 177 : Mat3).transpose * (codeMat 417 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc183s4_contain :
    (o183SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 273) (codeMat 177) flatW_7 := by
  change spanCodes [384, 80, 32, 8, 4, 2, 1] ≤ actionW (codeMat 273) (codeMat 177) flatW_7
  apply step109wc183_spanCodes_le_of_gens [384, 80, 32, 8, 4, 2, 1]
    (actionW (codeMat 273) (codeMat 177) flatW_7)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 177) (codeMat 256) = codeMat 384 := by
      unfold actionA
      rw [step109wc183s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 417 : Mat3).transpose = codeMat 384
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 112 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 112 (by decide)
    have hact : actionA (codeMat 273) (codeMat 177) (codeMat 112) = codeMat 80 := by
      unfold actionA
      rw [step109wc183s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 112 * (codeMat 417 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 16 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 273) (codeMat 177) (codeMat 16) = codeMat 32 := by
      unfold actionA
      rw [step109wc183s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 16 * (codeMat 417 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 177) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc183s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 417 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 177) (codeMat 2) = codeMat 4 := by
      unfold actionA
      rw [step109wc183s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 417 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 6 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 6 (by decide)
    have hact : actionA (codeMat 273) (codeMat 177) (codeMat 6) = codeMat 2 := by
      unfold actionA
      rw [step109wc183s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 6 * (codeMat 417 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 177) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc183s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 417 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc183_codeMat_mem_actionW_of_witness hw hact

theorem step109wc183s4Dispatch :
    QuotientRankAtLeast (o183SourceU_wc ⟨4, by omega⟩) 9 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 177) flatW_7) 9 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 177) hP hQ flatW_7 9
      flatSeed_7
  exact quotientRankAtLeast_mono step109wc183s4_contain hAct

theorem step109wc183_all_dispatch (i : Fin 5) :
    QuotientRankAtLeast (o183SourceU_wc i) (o183SourceLb_wc i) := by
  fin_cases i
  · exact step109wc183s0Dispatch
  · exact step109wc183s1Dispatch
  · exact step109wc183s2Dispatch
  · exact step109wc183s3Dispatch
  · exact step109wc183s4Dispatch

theorem step109_orbit183_lb15_wc : QuotientRankAtLeast o183W_wc 15 :=
  o183Lb15_wc step109wc183_all_dispatch

end QiushiMatmul
