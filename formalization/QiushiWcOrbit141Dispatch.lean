import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit141Consumer
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiOrbit5FP

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc141_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc141_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc141s0_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = (codeMat 275 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * (codeMat 275 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc141s0_contain :
    (o141SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 142) (codeMat 275) orbit10W := by
  change spanCodes [264, 140, 72, 32, 28, 2, 1] ≤ actionW (codeMat 142) (codeMat 275) orbit10W
  apply step109wc141_spanCodes_le_of_gens [264, 140, 72, 32, 28, 2, 1]
    (actionW (codeMat 142) (codeMat 275) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 324 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 324 (by decide)
    have hact : actionA (codeMat 142) (codeMat 275) (codeMat 324) = codeMat 264 := by
      unfold actionA
      rw [step109wc141s0_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 324 * (codeMat 275 : Mat3).transpose = codeMat 264
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 163 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 163 (by decide)
    have hact : actionA (codeMat 142) (codeMat 275) (codeMat 163) = codeMat 140 := by
      unfold actionA
      rw [step109wc141s0_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 163 * (codeMat 275 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 142) (codeMat 275) (codeMat 1) = codeMat 72 := by
      unfold actionA
      rw [step109wc141s0_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 1 * (codeMat 275 : Mat3).transpose = codeMat 72
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 142) (codeMat 275) (codeMat 256) = codeMat 32 := by
      unfold actionA
      rw [step109wc141s0_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 256 * (codeMat 275 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 142) (codeMat 275) (codeMat 160) = codeMat 28 := by
      unfold actionA
      rw [step109wc141s0_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 160 * (codeMat 275 : Mat3).transpose = codeMat 28
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 142) (codeMat 275) (codeMat 24) = codeMat 2 := by
      unfold actionA
      rw [step109wc141s0_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 24 * (codeMat 275 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 142) (codeMat 275) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc141s0_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 8 * (codeMat 275 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact

theorem step109wc141s0Dispatch :
    QuotientRankAtLeast (o141SourceU_wc ⟨0, by omega⟩) 12 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 275) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 275) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc141s0_contain hAct


private theorem step109wc141s1_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc141s1_contain :
    (o141SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 140) (codeMat 273) orbit10W := by
  change spanCodes [264, 128, 64, 32, 20, 2, 1] ≤ actionW (codeMat 140) (codeMat 273) orbit10W
  apply step109wc141_spanCodes_le_of_gens [264, 128, 64, 32, 20, 2, 1]
    (actionW (codeMat 140) (codeMat 273) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 68) = codeMat 264 := by
      unfold actionA
      rw [step109wc141s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 68 * (codeMat 273 : Mat3).transpose = codeMat 264
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 2) = codeMat 128 := by
      unfold actionA
      rw [step109wc141s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 1) = codeMat 64 := by
      unfold actionA
      rw [step109wc141s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 256) = codeMat 32 := by
      unfold actionA
      rw [step109wc141s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 256 * (codeMat 273 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 160) = codeMat 20 := by
      unfold actionA
      rw [step109wc141s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 160 * (codeMat 273 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 16) = codeMat 2 := by
      unfold actionA
      rw [step109wc141s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 16 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc141s1_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact

theorem step109wc141s1Dispatch :
    QuotientRankAtLeast (o141SourceU_wc ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 273) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 273) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc141s1_contain hAct


private theorem step109wc141s2_QtInv :
    (codeMat 116 : Mat3).transpose⁻¹ = (codeMat 92 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 116 : Mat3).transpose * (codeMat 92 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc141s2_contain :
    (o141SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 98) (codeMat 116) orbit14W := by
  change spanCodes [264, 136, 68, 32, 16, 2, 1] ≤ actionW (codeMat 98) (codeMat 116) orbit14W
  apply step109wc141_spanCodes_le_of_gens [264, 136, 68, 32, 16, 2, 1]
    (actionW (codeMat 98) (codeMat 116) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 28 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 28 (by decide)
    have hact : actionA (codeMat 98) (codeMat 116) (codeMat 28) = codeMat 264 := by
      unfold actionA
      rw [step109wc141s2_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 28 * (codeMat 92 : Mat3).transpose = codeMat 264
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 20 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 20 (by decide)
    have hact : actionA (codeMat 98) (codeMat 116) (codeMat 20) = codeMat 136 := by
      unfold actionA
      rw [step109wc141s2_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 20 * (codeMat 92 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 224 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 224 (by decide)
    have hact : actionA (codeMat 98) (codeMat 116) (codeMat 224) = codeMat 68 := by
      unfold actionA
      rw [step109wc141s2_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 224 * (codeMat 92 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 98) (codeMat 116) (codeMat 3) = codeMat 32 := by
      unfold actionA
      rw [step109wc141s2_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 3 * (codeMat 92 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 98) (codeMat 116) (codeMat 2) = codeMat 16 := by
      unfold actionA
      rw [step109wc141s2_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 2 * (codeMat 92 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 98) (codeMat 116) (codeMat 128) = codeMat 2 := by
      unfold actionA
      rw [step109wc141s2_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 128 * (codeMat 92 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 98) (codeMat 116) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc141s2_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 256 * (codeMat 92 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact

theorem step109wc141s2Dispatch :
    QuotientRankAtLeast (o141SourceU_wc ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 116 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 98) (codeMat 116) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 98) (codeMat 116) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc141s2_contain hAct


private theorem step109wc141s3_QtInv :
    (codeMat 236 : Mat3).transpose⁻¹ = (codeMat 123 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 236 : Mat3).transpose * (codeMat 123 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc141s3_contain :
    (o141SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 98) (codeMat 236) orbit14W := by
  change spanCodes [264, 132, 76, 32, 24, 2, 1] ≤ actionW (codeMat 98) (codeMat 236) orbit14W
  apply step109wc141_spanCodes_le_of_gens [264, 132, 76, 32, 24, 2, 1]
    (actionW (codeMat 98) (codeMat 236) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 30 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 30 (by decide)
    have hact : actionA (codeMat 98) (codeMat 236) (codeMat 30) = codeMat 264 := by
      unfold actionA
      rw [step109wc141s3_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 30 * (codeMat 123 : Mat3).transpose = codeMat 264
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 224 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 224 (by decide)
    have hact : actionA (codeMat 98) (codeMat 236) (codeMat 224) = codeMat 132 := by
      unfold actionA
      rw [step109wc141s3_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 224 * (codeMat 123 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 246 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 246 (by decide)
    have hact : actionA (codeMat 98) (codeMat 236) (codeMat 246) = codeMat 76 := by
      unfold actionA
      rw [step109wc141s3_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 246 * (codeMat 123 : Mat3).transpose = codeMat 76
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 98) (codeMat 236) (codeMat 3) = codeMat 32 := by
      unfold actionA
      rw [step109wc141s3_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 3 * (codeMat 123 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 98) (codeMat 236) (codeMat 2) = codeMat 24 := by
      unfold actionA
      rw [step109wc141s3_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 2 * (codeMat 123 : Mat3).transpose = codeMat 24
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 98) (codeMat 236) (codeMat 256) = codeMat 2 := by
      unfold actionA
      rw [step109wc141s3_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 256 * (codeMat 123 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 98) (codeMat 236) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step109wc141s3_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 384 * (codeMat 123 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact

theorem step109wc141s3Dispatch :
    QuotientRankAtLeast (o141SourceU_wc ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 236 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 98) (codeMat 236) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 98) (codeMat 236) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc141s3_contain hAct


private theorem step109wc141s4_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc141s4_contain :
    (o141SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 273) (codeMat 140) orbit5W := by
  change spanCodes [256, 80, 32, 8, 4, 2, 1] ≤ actionW (codeMat 273) (codeMat 140) orbit5W
  apply step109wc141_spanCodes_le_of_gens [256, 80, 32, 8, 4, 2, 1]
    (actionW (codeMat 273) (codeMat 140) orbit5W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 64 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 64 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 64) = codeMat 256 := by
      unfold actionA
      rw [step109wc141s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 64 * (codeMat 98 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 160 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 160) = codeMat 80 := by
      unfold actionA
      rw [step109wc141s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 160 * (codeMat 98 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc141s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 16 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 16) = codeMat 8 := by
      unfold actionA
      rw [step109wc141s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 16 * (codeMat 98 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step109wc141s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 4 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 4 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 4) = codeMat 2 := by
      unfold actionA
      rw [step109wc141s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 4 * (codeMat 98 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc141s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc141_codeMat_mem_actionW_of_witness hw hact

theorem step109wc141s4Dispatch :
    QuotientRankAtLeast (o141SourceU_wc ⟨4, by omega⟩) 9 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 140) orbit5W) 9 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 140) hP hQ orbit5W 9
      orbit5_lb9
  exact quotientRankAtLeast_mono step109wc141s4_contain hAct

theorem step109wc141_all_dispatch (i : Fin 5) :
    QuotientRankAtLeast (o141SourceU_wc i) (o141SourceLb_wc i) := by
  fin_cases i
  · exact step109wc141s0Dispatch
  · exact step109wc141s1Dispatch
  · exact step109wc141s2Dispatch
  · exact step109wc141s3Dispatch
  · exact step109wc141s4Dispatch

theorem step109_orbit141_lb15_wc : QuotientRankAtLeast o141W_wc 15 :=
  o141Lb15_wc step109wc141_all_dispatch

end QiushiMatmul
