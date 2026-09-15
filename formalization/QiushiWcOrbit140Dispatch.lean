import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit140Consumer
import QiushiOrbit40FP
import QiushiMonoOrbit43From14
import QiushiOrbit5FP
import QiushiOrbit14FP

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc140_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc140_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc140s0_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc140s0_contain :
    (o140SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 266) (codeMat 161) orbit40W := by
  change spanCodes [256, 84, 32, 8, 2, 1] ≤ actionW (codeMat 266) (codeMat 161) orbit40W
  apply step109wc140_spanCodes_le_of_gens [256, 84, 32, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 161) orbit40W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 128 ∈ orbit40W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 128] 128 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 128) = codeMat 256 := by
      unfold actionA
      rw [step109wc140s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 128 * (codeMat 161 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 84 ∈ orbit40W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 128] 84 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 84) = codeMat 84 := by
      unfold actionA
      rw [step109wc140s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 84 * (codeMat 161 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit40W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 128] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [step109wc140s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ orbit40W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 128] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step109wc140s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ orbit40W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 128] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 32) = codeMat 2 := by
      unfold actionA
      rw [step109wc140s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 161 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit40W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 128] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc140s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact

theorem step109wc140s0Dispatch :
    QuotientRankAtLeast (o140SourceU_wc ⟨0, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 161) orbit40W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 161) hP hQ orbit40W 12
      orbit40_lb12
  exact quotientRankAtLeast_mono step109wc140s0_contain hAct


private theorem step109wc140s1_QtInv :
    (codeMat 226 : Mat3).transpose⁻¹ = (codeMat 141 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 226 : Mat3).transpose * (codeMat 141 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc140s1_contain :
    (o140SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 394) (codeMat 226) o43W_mono := by
  change spanCodes [256, 76, 32, 24, 2, 1] ≤ actionW (codeMat 394) (codeMat 226) o43W_mono
  apply step109wc140_spanCodes_le_of_gens [256, 76, 32, 24, 2, 1]
    (actionW (codeMat 394) (codeMat 226) o43W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 130 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 130 (by decide)
    have hact : actionA (codeMat 394) (codeMat 226) (codeMat 130) = codeMat 256 := by
      unfold actionA
      rw [step109wc140s1_QtInv]
      show (codeMat 394 : Mat3).transpose * codeMat 130 * (codeMat 141 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 272 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 272 (by decide)
    have hact : actionA (codeMat 394) (codeMat 226) (codeMat 272) = codeMat 76 := by
      unfold actionA
      rw [step109wc140s1_QtInv]
      show (codeMat 394 : Mat3).transpose * codeMat 272 * (codeMat 141 : Mat3).transpose = codeMat 76
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 394) (codeMat 226) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [step109wc140s1_QtInv]
      show (codeMat 394 : Mat3).transpose * codeMat 2 * (codeMat 141 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 394) (codeMat 226) (codeMat 1) = codeMat 24 := by
      unfold actionA
      rw [step109wc140s1_QtInv]
      show (codeMat 394 : Mat3).transpose * codeMat 1 * (codeMat 141 : Mat3).transpose = codeMat 24
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 40 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 394) (codeMat 226) (codeMat 40) = codeMat 2 := by
      unfold actionA
      rw [step109wc140s1_QtInv]
      show (codeMat 394 : Mat3).transpose * codeMat 40 * (codeMat 141 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 394) (codeMat 226) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc140s1_QtInv]
      show (codeMat 394 : Mat3).transpose * codeMat 32 * (codeMat 141 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact

theorem step109wc140s1Dispatch :
    QuotientRankAtLeast (o140SourceU_wc ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 394 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 226 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 394) (codeMat 226) o43W_mono) 12 :=
    @quotientRankAtLeast_action (codeMat 394) (codeMat 226) hP hQ o43W_mono 12
      orbit43_lb12_mono
  exact quotientRankAtLeast_mono step109wc140s1_contain hAct


private theorem step109wc140s2_QtInv :
    (codeMat 225 : Mat3).transpose⁻¹ = (codeMat 169 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 225 : Mat3).transpose * (codeMat 169 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc140s2_contain :
    (o140SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 142) (codeMat 225) orbit40W := by
  change spanCodes [256, 140, 84, 32, 2, 1] ≤ actionW (codeMat 142) (codeMat 225) orbit40W
  apply step109wc140_spanCodes_le_of_gens [256, 140, 84, 32, 2, 1]
    (actionW (codeMat 142) (codeMat 225) orbit40W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 130 ∈ orbit40W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 128] 130 (by decide)
    have hact : actionA (codeMat 142) (codeMat 225) (codeMat 130) = codeMat 256 := by
      unfold actionA
      rw [step109wc140s2_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 130 * (codeMat 169 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 84 ∈ orbit40W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 128] 84 (by decide)
    have hact : actionA (codeMat 142) (codeMat 225) (codeMat 84) = codeMat 140 := by
      unfold actionA
      rw [step109wc140s2_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 84 * (codeMat 169 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 85 ∈ orbit40W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 128] 85 (by decide)
    have hact : actionA (codeMat 142) (codeMat 225) (codeMat 85) = codeMat 84 := by
      unfold actionA
      rw [step109wc140s2_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 85 * (codeMat 169 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ orbit40W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 128] 128 (by decide)
    have hact : actionA (codeMat 142) (codeMat 225) (codeMat 128) = codeMat 32 := by
      unfold actionA
      rw [step109wc140s2_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 128 * (codeMat 169 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ orbit40W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 128] 32 (by decide)
    have hact : actionA (codeMat 142) (codeMat 225) (codeMat 32) = codeMat 2 := by
      unfold actionA
      rw [step109wc140s2_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 32 * (codeMat 169 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 40 ∈ orbit40W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 128] 40 (by decide)
    have hact : actionA (codeMat 142) (codeMat 225) (codeMat 40) = codeMat 1 := by
      unfold actionA
      rw [step109wc140s2_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 40 * (codeMat 169 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact

theorem step109wc140s2Dispatch :
    QuotientRankAtLeast (o140SourceU_wc ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 225) orbit40W) 12 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 225) hP hQ orbit40W 12
      orbit40_lb12
  exact quotientRankAtLeast_mono step109wc140s2_contain hAct


private theorem step109wc140s3_QtInv :
    (codeMat 225 : Mat3).transpose⁻¹ = (codeMat 169 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 225 : Mat3).transpose * (codeMat 169 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc140s3_contain :
    (o140SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 396) (codeMat 225) o43W_mono := by
  change spanCodes [256, 148, 84, 32, 2, 1] ≤ actionW (codeMat 396) (codeMat 225) o43W_mono
  apply step109wc140_spanCodes_le_of_gens [256, 148, 84, 32, 2, 1]
    (actionW (codeMat 396) (codeMat 225) o43W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 2 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 396) (codeMat 225) (codeMat 2) = codeMat 256 := by
      unfold actionA
      rw [step109wc140s3_QtInv]
      show (codeMat 396 : Mat3).transpose * codeMat 2 * (codeMat 169 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 272 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 272 (by decide)
    have hact : actionA (codeMat 396) (codeMat 225) (codeMat 272) = codeMat 148 := by
      unfold actionA
      rw [step109wc140s3_QtInv]
      show (codeMat 396 : Mat3).transpose * codeMat 272 * (codeMat 169 : Mat3).transpose = codeMat 148
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 273 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 273 (by decide)
    have hact : actionA (codeMat 396) (codeMat 225) (codeMat 273) = codeMat 84 := by
      unfold actionA
      rw [step109wc140s3_QtInv]
      show (codeMat 396 : Mat3).transpose * codeMat 273 * (codeMat 169 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 130 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 130 (by decide)
    have hact : actionA (codeMat 396) (codeMat 225) (codeMat 130) = codeMat 32 := by
      unfold actionA
      rw [step109wc140s3_QtInv]
      show (codeMat 396 : Mat3).transpose * codeMat 130 * (codeMat 169 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 396) (codeMat 225) (codeMat 32) = codeMat 2 := by
      unfold actionA
      rw [step109wc140s3_QtInv]
      show (codeMat 396 : Mat3).transpose * codeMat 32 * (codeMat 169 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 40 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 396) (codeMat 225) (codeMat 40) = codeMat 1 := by
      unfold actionA
      rw [step109wc140s3_QtInv]
      show (codeMat 396 : Mat3).transpose * codeMat 40 * (codeMat 169 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact

theorem step109wc140s3Dispatch :
    QuotientRankAtLeast (o140SourceU_wc ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 396 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 396) (codeMat 225) o43W_mono) 12 :=
    @quotientRankAtLeast_action (codeMat 396) (codeMat 225) hP hQ o43W_mono 12
      orbit43_lb12_mono
  exact quotientRankAtLeast_mono step109wc140s3_contain hAct


private theorem step109wc140s4_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc140s4_contain :
    (o140SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 161) (codeMat 84) orbit5W := by
  change spanCodes [256, 128, 80, 32, 4, 2, 1] ≤ actionW (codeMat 161) (codeMat 84) orbit5W
  apply step109wc140_spanCodes_le_of_gens [256, 128, 80, 32, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 84) orbit5W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 8 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 84) (codeMat 8) = codeMat 256 := by
      unfold actionA
      rw [step109wc140s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 84 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 16 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 16 (by decide)
    have hact : actionA (codeMat 161) (codeMat 84) (codeMat 16) = codeMat 128 := by
      unfold actionA
      rw [step109wc140s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 16 * (codeMat 84 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 160 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 84) (codeMat 160) = codeMat 80 := by
      unfold actionA
      rw [step109wc140s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * (codeMat 84 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 64 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 64 (by decide)
    have hact : actionA (codeMat 161) (codeMat 84) (codeMat 64) = codeMat 32 := by
      unfold actionA
      rw [step109wc140s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 64 * (codeMat 84 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 84) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step109wc140s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 84) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc140s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 4 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 4 (by decide)
    have hact : actionA (codeMat 161) (codeMat 84) (codeMat 4) = codeMat 1 := by
      unfold actionA
      rw [step109wc140s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 4 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact

theorem step109wc140s4Dispatch :
    QuotientRankAtLeast (o140SourceU_wc ⟨4, by omega⟩) 9 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 84) orbit5W) 9 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 84) hP hQ orbit5W 9
      orbit5_lb9
  exact quotientRankAtLeast_mono step109wc140s4_contain hAct


private theorem step109wc140s5_QtInv :
    (codeMat 156 : Mat3).transpose⁻¹ = (codeMat 102 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 156 : Mat3).transpose * (codeMat 102 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc140s5_contain :
    (o140SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 86) (codeMat 156) orbit14W := by
  change spanCodes [256, 132, 72, 32, 28, 2, 1] ≤ actionW (codeMat 86) (codeMat 156) orbit14W
  apply step109wc140_spanCodes_le_of_gens [256, 132, 72, 32, 28, 2, 1]
    (actionW (codeMat 86) (codeMat 156) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 9 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 9 (by decide)
    have hact : actionA (codeMat 86) (codeMat 156) (codeMat 9) = codeMat 256 := by
      unfold actionA
      rw [step109wc140s5_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 9 * (codeMat 102 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 118 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 118 (by decide)
    have hact : actionA (codeMat 86) (codeMat 156) (codeMat 118) = codeMat 132 := by
      unfold actionA
      rw [step109wc140s5_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 118 * (codeMat 102 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 86) (codeMat 156) (codeMat 2) = codeMat 72 := by
      unfold actionA
      rw [step109wc140s5_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 2 * (codeMat 102 : Mat3).transpose = codeMat 72
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 86) (codeMat 156) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc140s5_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 8 * (codeMat 102 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 86) (codeMat 156) (codeMat 96) = codeMat 28 := by
      unfold actionA
      rw [step109wc140s5_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 96 * (codeMat 102 : Mat3).transpose = codeMat 28
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 86) (codeMat 156) (codeMat 384) = codeMat 2 := by
      unfold actionA
      rw [step109wc140s5_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 384 * (codeMat 102 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 86) (codeMat 156) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc140s5_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 128 * (codeMat 102 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact

theorem step109wc140s5Dispatch :
    QuotientRankAtLeast (o140SourceU_wc ⟨5, by omega⟩) 12 := by
  have hP : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 156 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 86) (codeMat 156) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 86) (codeMat 156) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc140s5_contain hAct


private theorem step109wc140s6_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc140s6_contain :
    (o140SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 98) (codeMat 84) orbit14W := by
  change spanCodes [256, 136, 68, 32, 16, 2, 1] ≤ actionW (codeMat 98) (codeMat 84) orbit14W
  apply step109wc140_spanCodes_le_of_gens [256, 136, 68, 32, 16, 2, 1]
    (actionW (codeMat 98) (codeMat 84) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 98) (codeMat 84) (codeMat 8) = codeMat 256 := by
      unfold actionA
      rw [step109wc140s6_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 8 * (codeMat 84 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 20 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 20 (by decide)
    have hact : actionA (codeMat 98) (codeMat 84) (codeMat 20) = codeMat 136 := by
      unfold actionA
      rw [step109wc140s6_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 20 * (codeMat 84 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 98) (codeMat 84) (codeMat 96) = codeMat 68 := by
      unfold actionA
      rw [step109wc140s6_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 96 * (codeMat 84 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 98) (codeMat 84) (codeMat 1) = codeMat 32 := by
      unfold actionA
      rw [step109wc140s6_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 98) (codeMat 84) (codeMat 2) = codeMat 16 := by
      unfold actionA
      rw [step109wc140s6_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 98) (codeMat 84) (codeMat 128) = codeMat 2 := by
      unfold actionA
      rw [step109wc140s6_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 128 * (codeMat 84 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 98) (codeMat 84) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc140s6_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 256 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact

theorem step109wc140s6Dispatch :
    QuotientRankAtLeast (o140SourceU_wc ⟨6, by omega⟩) 12 := by
  have hP : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 98) (codeMat 84) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 98) (codeMat 84) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc140s6_contain hAct


private theorem step109wc140s7_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc140s7_contain :
    (o140SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 84) (codeMat 140) orbit14W := by
  change spanCodes [256, 136, 64, 32, 20, 2, 1] ≤ actionW (codeMat 84) (codeMat 140) orbit14W
  apply step109wc140_spanCodes_le_of_gens [256, 136, 64, 32, 20, 2, 1]
    (actionW (codeMat 84) (codeMat 140) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc140s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 20 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 20 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 20) = codeMat 136 := by
      unfold actionA
      rw [step109wc140s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 20 * (codeMat 98 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 2) = codeMat 64 := by
      unfold actionA
      rw [step109wc140s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc140s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 96) = codeMat 20 := by
      unfold actionA
      rw [step109wc140s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 96 * (codeMat 98 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 256) = codeMat 2 := by
      unfold actionA
      rw [step109wc140s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 98 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc140s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact

theorem step109wc140s7Dispatch :
    QuotientRankAtLeast (o140SourceU_wc ⟨7, by omega⟩) 12 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 140) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 140) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc140s7_contain hAct


private theorem step109wc140s8_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc140s8_contain :
    (o140SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 86) (codeMat 84) orbit14W := by
  change spanCodes [256, 144, 84, 32, 12, 2, 1] ≤ actionW (codeMat 86) (codeMat 84) orbit14W
  apply step109wc140_spanCodes_le_of_gens [256, 144, 84, 32, 12, 2, 1]
    (actionW (codeMat 86) (codeMat 84) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 9 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 9 (by decide)
    have hact : actionA (codeMat 86) (codeMat 84) (codeMat 9) = codeMat 256 := by
      unfold actionA
      rw [step109wc140s8_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 9 * (codeMat 84 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 86) (codeMat 84) (codeMat 2) = codeMat 144 := by
      unfold actionA
      rw [step109wc140s8_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 116 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 116 (by decide)
    have hact : actionA (codeMat 86) (codeMat 84) (codeMat 116) = codeMat 84 := by
      unfold actionA
      rw [step109wc140s8_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 116 * (codeMat 84 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 86) (codeMat 84) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc140s8_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 8 * (codeMat 84 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 86) (codeMat 84) (codeMat 96) = codeMat 12 := by
      unfold actionA
      rw [step109wc140s8_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 96 * (codeMat 84 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 86) (codeMat 84) (codeMat 128) = codeMat 2 := by
      unfold actionA
      rw [step109wc140s8_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 128 * (codeMat 84 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 86) (codeMat 84) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc140s8_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 256 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc140_codeMat_mem_actionW_of_witness hw hact

theorem step109wc140s8Dispatch :
    QuotientRankAtLeast (o140SourceU_wc ⟨8, by omega⟩) 12 := by
  have hP : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 86) (codeMat 84) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 86) (codeMat 84) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc140s8_contain hAct

theorem step109wc140_all_dispatch (i : Fin 9) :
    QuotientRankAtLeast (o140SourceU_wc i) (o140SourceLb_wc i) := by
  fin_cases i
  · exact step109wc140s0Dispatch
  · exact step109wc140s1Dispatch
  · exact step109wc140s2Dispatch
  · exact step109wc140s3Dispatch
  · exact step109wc140s4Dispatch
  · exact step109wc140s5Dispatch
  · exact step109wc140s6Dispatch
  · exact step109wc140s7Dispatch
  · exact step109wc140s8Dispatch

theorem step109_orbit140_lb14_wc : QuotientRankAtLeast o140W_wc 14 :=
  o140Lb14_wc step109wc140_all_dispatch

end QiushiMatmul
