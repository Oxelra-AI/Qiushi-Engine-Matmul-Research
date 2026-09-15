import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit300Consumer
import QiushiStep126Mono159From75
import QiushiOrbit29FP
import QiushiStep81Qdim2Generated

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc300_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc300_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc300s0_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc300s0_contain :
    (o300SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 273) (codeMat 273) o159W_mono := by
  change spanCodes [160, 68, 20, 10, 1] ≤ actionW (codeMat 273) (codeMat 273) o159W_mono
  apply step109wc300_spanCodes_le_of_gens [160, 68, 20, 10, 1]
    (actionW (codeMat 273) (codeMat 273) o159W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 160 ∈ o159W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [160, 68, 20, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 160) = codeMat 160 := by
      unfold actionA
      rw [step109wc300s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 160 * (codeMat 273 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ o159W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [160, 68, 20, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step109wc300s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 68 * (codeMat 273 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 20 ∈ o159W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [160, 68, 20, 10, 1] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 20) = codeMat 20 := by
      unfold actionA
      rw [step109wc300s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * (codeMat 273 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 10 ∈ o159W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [160, 68, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step109wc300s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 10 * (codeMat 273 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o159W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [160, 68, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc300s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact

theorem step109wc300s0Dispatch :
    QuotientRankAtLeast (o300SourceU_wc ⟨0, by omega⟩) 16 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 273) o159W_mono) 16 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 273) hP hQ o159W_mono 16
      orbit159_lb16_mono
  exact quotientRankAtLeast_mono step109wc300s0_contain hAct


private theorem step109wc300s1_QtInv :
    (codeMat 177 : Mat3).transpose⁻¹ = (codeMat 417 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 177 : Mat3).transpose * (codeMat 417 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc300s1_contain :
    (o300SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 417) (codeMat 177) o159W_mono := by
  change spanCodes [262, 160, 68, 10, 1] ≤ actionW (codeMat 417) (codeMat 177) o159W_mono
  apply step109wc300_spanCodes_le_of_gens [262, 160, 68, 10, 1]
    (actionW (codeMat 417) (codeMat 177) o159W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 20 ∈ o159W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [160, 68, 20, 10, 1] 20 (by decide)
    have hact : actionA (codeMat 417) (codeMat 177) (codeMat 20) = codeMat 262 := by
      unfold actionA
      rw [step109wc300s1_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 20 * (codeMat 417 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ o159W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [160, 68, 20, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 417) (codeMat 177) (codeMat 160) = codeMat 160 := by
      unfold actionA
      rw [step109wc300s1_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 160 * (codeMat 417 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 10 ∈ o159W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [160, 68, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 417) (codeMat 177) (codeMat 10) = codeMat 68 := by
      unfold actionA
      rw [step109wc300s1_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 10 * (codeMat 417 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 78 ∈ o159W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [160, 68, 20, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 417) (codeMat 177) (codeMat 78) = codeMat 10 := by
      unfold actionA
      rw [step109wc300s1_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 78 * (codeMat 417 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o159W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [160, 68, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 417) (codeMat 177) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc300s1_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 1 * (codeMat 417 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact

theorem step109wc300s1Dispatch :
    QuotientRankAtLeast (o300SourceU_wc ⟨1, by omega⟩) 16 := by
  have hP : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 417) (codeMat 177) o159W_mono) 16 :=
    @quotientRankAtLeast_action (codeMat 417) (codeMat 177) hP hQ o159W_mono 16
      orbit159_lb16_mono
  exact quotientRankAtLeast_mono step109wc300s1_contain hAct


private theorem step109wc300s2_QtInv :
    (codeMat 417 : Mat3).transpose⁻¹ = (codeMat 177 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 417 : Mat3).transpose * (codeMat 177 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc300s2_contain :
    (o300SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 177) (codeMat 417) o159W_mono := by
  change spanCodes [274, 160, 68, 10, 1] ≤ actionW (codeMat 177) (codeMat 417) o159W_mono
  apply step109wc300_spanCodes_le_of_gens [274, 160, 68, 10, 1]
    (actionW (codeMat 177) (codeMat 417) o159W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 180 ∈ o159W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [160, 68, 20, 10, 1] 180 (by decide)
    have hact : actionA (codeMat 177) (codeMat 417) (codeMat 180) = codeMat 274 := by
      unfold actionA
      rw [step109wc300s2_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 180 * (codeMat 177 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ o159W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [160, 68, 20, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 177) (codeMat 417) (codeMat 160) = codeMat 160 := by
      unfold actionA
      rw [step109wc300s2_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 160 * (codeMat 177 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 78 ∈ o159W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [160, 68, 20, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 177) (codeMat 417) (codeMat 78) = codeMat 68 := by
      unfold actionA
      rw [step109wc300s2_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 78 * (codeMat 177 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 68 ∈ o159W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [160, 68, 20, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 177) (codeMat 417) (codeMat 68) = codeMat 10 := by
      unfold actionA
      rw [step109wc300s2_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 68 * (codeMat 177 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o159W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [160, 68, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 417) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc300s2_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * (codeMat 177 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact

theorem step109wc300s2Dispatch :
    QuotientRankAtLeast (o300SourceU_wc ⟨2, by omega⟩) 16 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 417) o159W_mono) 16 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 417) hP hQ o159W_mono 16
      orbit159_lb16_mono
  exact quotientRankAtLeast_mono step109wc300s2_contain hAct


private theorem step109wc300s3_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc300s3_contain :
    (o300SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 266) (codeMat 266) orbit29W := by
  change spanCodes [160, 68, 16, 8, 2, 1] ≤ actionW (codeMat 266) (codeMat 266) orbit29W
  apply step109wc300_spanCodes_le_of_gens [160, 68, 16, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 266) orbit29W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 68 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 68 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 68) = codeMat 160 := by
      unfold actionA
      rw [step109wc300s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 68 * (codeMat 266 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 160 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 160) = codeMat 68 := by
      unfold actionA
      rw [step109wc300s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 160 * (codeMat 266 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc300s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 2) = codeMat 8 := by
      unfold actionA
      rw [step109wc300s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 8) = codeMat 2 := by
      unfold actionA
      rw [step109wc300s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc300s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact

theorem step109wc300s3Dispatch :
    QuotientRankAtLeast (o300SourceU_wc ⟨3, by omega⟩) 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 266) orbit29W) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 266) hP hQ orbit29W 15
      orbit29_lb15
  exact quotientRankAtLeast_mono step109wc300s3_contain hAct


private theorem step109wc300s4_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc300s4_contain :
    (o300SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 140) (codeMat 140) orbit29W := by
  change spanCodes [256, 160, 64, 10, 4, 1] ≤ actionW (codeMat 140) (codeMat 140) orbit29W
  apply step109wc300_spanCodes_le_of_gens [256, 160, 64, 10, 4, 1]
    (actionW (codeMat 140) (codeMat 140) orbit29W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 1 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc300s4_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 68 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 68) = codeMat 160 := by
      unfold actionA
      rw [step109wc300s4_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 68 * (codeMat 98 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 2) = codeMat 64 := by
      unfold actionA
      rw [step109wc300s4_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 160 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 160 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc300s4_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 160 * (codeMat 98 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 8 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 8) = codeMat 4 := by
      unfold actionA
      rw [step109wc300s4_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 16 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc300s4_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 16 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact

theorem step109wc300s4Dispatch :
    QuotientRankAtLeast (o300SourceU_wc ⟨4, by omega⟩) 15 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 140) orbit29W) 15 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 140) hP hQ orbit29W 15
      orbit29_lb15
  exact quotientRankAtLeast_mono step109wc300s4_contain hAct


private theorem step109wc300s5_QtInv :
    (codeMat 394 : Mat3).transpose⁻¹ = (codeMat 330 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 394 : Mat3).transpose * (codeMat 330 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc300s5_contain :
    (o300SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 142) (codeMat 394) orbit29W := by
  change spanCodes [272, 160, 66, 10, 6, 1] ≤ actionW (codeMat 142) (codeMat 394) orbit29W
  apply step109wc300_spanCodes_le_of_gens [272, 160, 66, 10, 6, 1]
    (actionW (codeMat 142) (codeMat 394) orbit29W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 68 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 68 (by decide)
    have hact : actionA (codeMat 142) (codeMat 394) (codeMat 68) = codeMat 272 := by
      unfold actionA
      rw [step109wc300s5_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 68 * (codeMat 330 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 69 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 69 (by decide)
    have hact : actionA (codeMat 142) (codeMat 394) (codeMat 69) = codeMat 160 := by
      unfold actionA
      rw [step109wc300s5_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 69 * (codeMat 330 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 170 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 170 (by decide)
    have hact : actionA (codeMat 142) (codeMat 394) (codeMat 170) = codeMat 66 := by
      unfold actionA
      rw [step109wc300s5_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 170 * (codeMat 330 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 168 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 168 (by decide)
    have hact : actionA (codeMat 142) (codeMat 394) (codeMat 168) = codeMat 10 := by
      unfold actionA
      rw [step109wc300s5_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 168 * (codeMat 330 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 8 (by decide)
    have hact : actionA (codeMat 142) (codeMat 394) (codeMat 8) = codeMat 6 := by
      unfold actionA
      rw [step109wc300s5_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 8 * (codeMat 330 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 16 (by decide)
    have hact : actionA (codeMat 142) (codeMat 394) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc300s5_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 16 * (codeMat 330 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact

theorem step109wc300s5Dispatch :
    QuotientRankAtLeast (o300SourceU_wc ⟨5, by omega⟩) 15 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 394 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 394) orbit29W) 15 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 394) hP hQ orbit29W 15
      orbit29_lb15
  exact quotientRankAtLeast_mono step109wc300s5_contain hAct


private theorem step109wc300s6_QtInv :
    (codeMat 286 : Mat3).transpose⁻¹ = (codeMat 303 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 286 : Mat3).transpose * (codeMat 303 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc300s6_contain :
    (o300SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 84) (codeMat 286) step81o17s4Wspan := by
  change spanCodes [258, 132, 68, 36, 22, 10, 1] ≤ actionW (codeMat 84) (codeMat 286) step81o17s4Wspan
  apply step109wc300_spanCodes_le_of_gens [258, 132, 68, 36, 22, 10, 1]
    (actionW (codeMat 84) (codeMat 286) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 197 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 197 (by decide)
    have hact : actionA (codeMat 84) (codeMat 286) (codeMat 197) = codeMat 258 := by
      unfold actionA
      rw [step109wc300s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 197 * (codeMat 303 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 323 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 323 (by decide)
    have hact : actionA (codeMat 84) (codeMat 286) (codeMat 323) = codeMat 132 := by
      unfold actionA
      rw [step109wc300s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 323 * (codeMat 303 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 322 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 322 (by decide)
    have hact : actionA (codeMat 84) (codeMat 286) (codeMat 322) = codeMat 68 := by
      unfold actionA
      rw [step109wc300s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 322 * (codeMat 303 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 360 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 360 (by decide)
    have hact : actionA (codeMat 84) (codeMat 286) (codeMat 360) = codeMat 36 := by
      unfold actionA
      rw [step109wc300s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 360 * (codeMat 303 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 408 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 408 (by decide)
    have hact : actionA (codeMat 84) (codeMat 286) (codeMat 408) = codeMat 22 := by
      unfold actionA
      rw [step109wc300s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 408 * (codeMat 303 : Mat3).transpose = codeMat 22
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 208 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 208 (by decide)
    have hact : actionA (codeMat 84) (codeMat 286) (codeMat 208) = codeMat 10 := by
      unfold actionA
      rw [step109wc300s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 208 * (codeMat 303 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 286) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc300s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 303 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact

theorem step109wc300s6Dispatch :
    QuotientRankAtLeast (o300SourceU_wc ⟨6, by omega⟩) 14 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 286 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 286) step81o17s4Wspan) 14 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 286) hP hQ step81o17s4Wspan 14
      step81o17s4Span_lb
  exact quotientRankAtLeast_mono step109wc300s6_contain hAct


private theorem step109wc300s7_QtInv :
    (codeMat 318 : Mat3).transpose⁻¹ = (codeMat 299 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 318 : Mat3).transpose * (codeMat 299 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc300s7_contain :
    (o300SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 85) (codeMat 318) step81o17s4Wspan := by
  change spanCodes [258, 134, 68, 38, 22, 10, 1] ≤ actionW (codeMat 85) (codeMat 318) step81o17s4Wspan
  apply step109wc300_spanCodes_le_of_gens [258, 134, 68, 38, 22, 10, 1]
    (actionW (codeMat 85) (codeMat 318) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 263 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 263 (by decide)
    have hact : actionA (codeMat 85) (codeMat 318) (codeMat 263) = codeMat 258 := by
      unfold actionA
      rw [step109wc300s7_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 263 * (codeMat 299 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 451 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 451 (by decide)
    have hact : actionA (codeMat 85) (codeMat 318) (codeMat 451) = codeMat 134 := by
      unfold actionA
      rw [step109wc300s7_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 451 * (codeMat 299 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 322 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 322 (by decide)
    have hact : actionA (codeMat 85) (codeMat 318) (codeMat 322) = codeMat 68 := by
      unfold actionA
      rw [step109wc300s7_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 322 * (codeMat 299 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 312 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 312 (by decide)
    have hact : actionA (codeMat 85) (codeMat 318) (codeMat 312) = codeMat 38 := by
      unfold actionA
      rw [step109wc300s7_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 312 * (codeMat 299 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 280 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 280 (by decide)
    have hact : actionA (codeMat 85) (codeMat 318) (codeMat 280) = codeMat 22 := by
      unfold actionA
      rw [step109wc300s7_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 280 * (codeMat 299 : Mat3).transpose = codeMat 22
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 208 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 208 (by decide)
    have hact : actionA (codeMat 85) (codeMat 318) (codeMat 208) = codeMat 10 := by
      unfold actionA
      rw [step109wc300s7_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 208 * (codeMat 299 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 85) (codeMat 318) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc300s7_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 128 * (codeMat 299 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact

theorem step109wc300s7Dispatch :
    QuotientRankAtLeast (o300SourceU_wc ⟨7, by omega⟩) 14 := by
  have hP : Invertible (codeMat 85 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 318 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 85) (codeMat 318) step81o17s4Wspan) 14 :=
    @quotientRankAtLeast_action (codeMat 85) (codeMat 318) hP hQ step81o17s4Wspan 14
      step81o17s4Span_lb
  exact quotientRankAtLeast_mono step109wc300s7_contain hAct


private theorem step109wc300s8_QtInv :
    (codeMat 270 : Mat3).transpose⁻¹ = (codeMat 298 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 270 : Mat3).transpose * (codeMat 298 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc300s8_contain :
    (o300SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 92) (codeMat 270) step81o17s4Wspan := by
  change spanCodes [258, 128, 68, 32, 22, 10, 1] ≤ actionW (codeMat 92) (codeMat 270) step81o17s4Wspan
  apply step109wc300_spanCodes_le_of_gens [258, 128, 68, 32, 22, 10, 1]
    (actionW (codeMat 92) (codeMat 270) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 69 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 92) (codeMat 270) (codeMat 69) = codeMat 258 := by
      unfold actionA
      rw [step109wc300s8_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 69 * (codeMat 298 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 92) (codeMat 270) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step109wc300s8_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 1 * (codeMat 298 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 322 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 322 (by decide)
    have hact : actionA (codeMat 92) (codeMat 270) (codeMat 322) = codeMat 68 := by
      unfold actionA
      rw [step109wc300s8_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 322 * (codeMat 298 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 360 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 360 (by decide)
    have hact : actionA (codeMat 92) (codeMat 270) (codeMat 360) = codeMat 32 := by
      unfold actionA
      rw [step109wc300s8_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 360 * (codeMat 298 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 328 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 328 (by decide)
    have hact : actionA (codeMat 92) (codeMat 270) (codeMat 328) = codeMat 22 := by
      unfold actionA
      rw [step109wc300s8_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 328 * (codeMat 298 : Mat3).transpose = codeMat 22
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 208 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 208 (by decide)
    have hact : actionA (codeMat 92) (codeMat 270) (codeMat 208) = codeMat 10 := by
      unfold actionA
      rw [step109wc300s8_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 208 * (codeMat 298 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 92) (codeMat 270) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc300s8_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 128 * (codeMat 298 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact

theorem step109wc300s8Dispatch :
    QuotientRankAtLeast (o300SourceU_wc ⟨8, by omega⟩) 14 := by
  have hP : Invertible (codeMat 92 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 270 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 92) (codeMat 270) step81o17s4Wspan) 14 :=
    @quotientRankAtLeast_action (codeMat 92) (codeMat 270) hP hQ step81o17s4Wspan 14
      step81o17s4Span_lb
  exact quotientRankAtLeast_mono step109wc300s8_contain hAct


private theorem step109wc300s9_QtInv :
    (codeMat 302 : Mat3).transpose⁻¹ = (codeMat 302 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 302 : Mat3).transpose * (codeMat 302 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc300s9_contain :
    (o300SourceU_wc ⟨9, by omega⟩) ≤ actionW (codeMat 93) (codeMat 302) step81o17s4Wspan := by
  change spanCodes [258, 130, 68, 34, 22, 10, 1] ≤ actionW (codeMat 93) (codeMat 302) step81o17s4Wspan
  apply step109wc300_spanCodes_le_of_gens [258, 130, 68, 34, 22, 10, 1]
    (actionW (codeMat 93) (codeMat 302) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 391 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 391 (by decide)
    have hact : actionA (codeMat 93) (codeMat 302) (codeMat 391) = codeMat 258 := by
      unfold actionA
      rw [step109wc300s9_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 391 * (codeMat 302 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 93) (codeMat 302) (codeMat 1) = codeMat 130 := by
      unfold actionA
      rw [step109wc300s9_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 1 * (codeMat 302 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 322 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 322 (by decide)
    have hact : actionA (codeMat 93) (codeMat 302) (codeMat 322) = codeMat 68 := by
      unfold actionA
      rw [step109wc300s9_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 322 * (codeMat 302 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 440 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 440 (by decide)
    have hact : actionA (codeMat 93) (codeMat 302) (codeMat 440) = codeMat 34 := by
      unfold actionA
      rw [step109wc300s9_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 440 * (codeMat 302 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 456 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 456 (by decide)
    have hact : actionA (codeMat 93) (codeMat 302) (codeMat 456) = codeMat 22 := by
      unfold actionA
      rw [step109wc300s9_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 456 * (codeMat 302 : Mat3).transpose = codeMat 22
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 208 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 208 (by decide)
    have hact : actionA (codeMat 93) (codeMat 302) (codeMat 208) = codeMat 10 := by
      unfold actionA
      rw [step109wc300s9_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 208 * (codeMat 302 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 93) (codeMat 302) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc300s9_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 128 * (codeMat 302 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc300_codeMat_mem_actionW_of_witness hw hact

theorem step109wc300s9Dispatch :
    QuotientRankAtLeast (o300SourceU_wc ⟨9, by omega⟩) 14 := by
  have hP : Invertible (codeMat 93 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 302 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 93) (codeMat 302) step81o17s4Wspan) 14 :=
    @quotientRankAtLeast_action (codeMat 93) (codeMat 302) hP hQ step81o17s4Wspan 14
      step81o17s4Span_lb
  exact quotientRankAtLeast_mono step109wc300s9_contain hAct

theorem step109wc300_all_dispatch (i : Fin 10) :
    QuotientRankAtLeast (o300SourceU_wc i) (o300SourceLb_wc i) := by
  fin_cases i
  · exact step109wc300s0Dispatch
  · exact step109wc300s1Dispatch
  · exact step109wc300s2Dispatch
  · exact step109wc300s3Dispatch
  · exact step109wc300s4Dispatch
  · exact step109wc300s5Dispatch
  · exact step109wc300s6Dispatch
  · exact step109wc300s7Dispatch
  · exact step109wc300s8Dispatch
  · exact step109wc300s9Dispatch

theorem step109_orbit300_lb17_wc : QuotientRankAtLeast o300W_wc 17 :=
  o300Lb17_wc step109wc300_all_dispatch

end QiushiMatmul
