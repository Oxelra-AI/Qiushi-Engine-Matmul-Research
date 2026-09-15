import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit83Consumer
import QiushiOrbit14FP
import QiushiOrbit13FP
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc83_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc83_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc83s0_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc83s0_contain :
    (o83SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 177) (codeMat 266) orbit14W := by
  change spanCodes [272, 144, 68, 32, 8, 2, 1] ≤ actionW (codeMat 177) (codeMat 266) orbit14W
  apply step109wc83_spanCodes_le_of_gens [272, 144, 68, 32, 8, 2, 1]
    (actionW (codeMat 177) (codeMat 266) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 352 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 352 (by decide)
    have hact : actionA (codeMat 177) (codeMat 266) (codeMat 352) = codeMat 272 := by
      unfold actionA
      rw [step109wc83s0_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 352 * (codeMat 266 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 177) (codeMat 266) (codeMat 8) = codeMat 144 := by
      unfold actionA
      rw [step109wc83s0_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 148 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 148 (by decide)
    have hact : actionA (codeMat 177) (codeMat 266) (codeMat 148) = codeMat 68 := by
      unfold actionA
      rw [step109wc83s0_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 148 * (codeMat 266 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 177) (codeMat 266) (codeMat 256) = codeMat 32 := by
      unfold actionA
      rw [step109wc83s0_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 256 * (codeMat 266 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 177) (codeMat 266) (codeMat 128) = codeMat 8 := by
      unfold actionA
      rw [step109wc83s0_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 128 * (codeMat 266 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 266) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step109wc83s0_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 177) (codeMat 266) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc83s0_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact

theorem step109wc83s0Dispatch :
    QuotientRankAtLeast (o83SourceU_wc ⟨0, by omega⟩) 12 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 266) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 266) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc83s0_contain hAct


private theorem step109wc83s1_QtInv :
    (codeMat 158 : Mat3).transpose⁻¹ = (codeMat 358 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 158 : Mat3).transpose * (codeMat 358 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc83s1_contain :
    (o83SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 337) (codeMat 158) orbit14W := by
  change spanCodes [274, 144, 64, 32, 10, 4, 1] ≤ actionW (codeMat 337) (codeMat 158) orbit14W
  apply step109wc83_spanCodes_le_of_gens [274, 144, 64, 32, 10, 4, 1]
    (actionW (codeMat 337) (codeMat 158) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 126 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 126 (by decide)
    have hact : actionA (codeMat 337) (codeMat 158) (codeMat 126) = codeMat 274 := by
      unfold actionA
      rw [step109wc83s1_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 126 * (codeMat 358 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 511 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 511 (by decide)
    have hact : actionA (codeMat 337) (codeMat 158) (codeMat 511) = codeMat 144 := by
      unfold actionA
      rw [step109wc83s1_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 511 * (codeMat 358 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 130 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 130 (by decide)
    have hact : actionA (codeMat 337) (codeMat 158) (codeMat 130) = codeMat 64 := by
      unfold actionA
      rw [step109wc83s1_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 130 * (codeMat 358 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 337) (codeMat 158) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc83s1_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 8 * (codeMat 358 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 23 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 23 (by decide)
    have hact : actionA (codeMat 337) (codeMat 158) (codeMat 23) = codeMat 10 := by
      unfold actionA
      rw [step109wc83s1_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 23 * (codeMat 358 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 337) (codeMat 158) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step109wc83s1_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 1 * (codeMat 358 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 337) (codeMat 158) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc83s1_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 2 * (codeMat 358 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact

theorem step109wc83s1Dispatch :
    QuotientRankAtLeast (o83SourceU_wc ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 337 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 158 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 337) (codeMat 158) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 337) (codeMat 158) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc83s1_contain hAct


private theorem step109wc83s2_QtInv :
    (codeMat 412 : Mat3).transpose⁻¹ = (codeMat 111 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 412 : Mat3).transpose * (codeMat 111 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc83s2_contain :
    (o83SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 417) (codeMat 412) orbit14W := by
  change spanCodes [274, 144, 66, 32, 10, 6, 1] ≤ actionW (codeMat 417) (codeMat 412) orbit14W
  apply step109wc83_spanCodes_le_of_gens [274, 144, 66, 32, 10, 6, 1]
    (actionW (codeMat 417) (codeMat 412) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 414 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 414 (by decide)
    have hact : actionA (codeMat 417) (codeMat 412) (codeMat 414) = codeMat 274 := by
      unfold actionA
      rw [step109wc83s2_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 414 * (codeMat 111 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 417) (codeMat 412) (codeMat 384) = codeMat 144 := by
      unfold actionA
      rw [step109wc83s2_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 384 * (codeMat 111 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 22 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 22 (by decide)
    have hact : actionA (codeMat 417) (codeMat 412) (codeMat 22) = codeMat 66 := by
      unfold actionA
      rw [step109wc83s2_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 22 * (codeMat 111 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 417) (codeMat 412) (codeMat 360) = codeMat 32 := by
      unfold actionA
      rw [step109wc83s2_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 360 * (codeMat 111 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 150 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 150 (by decide)
    have hact : actionA (codeMat 417) (codeMat 412) (codeMat 150) = codeMat 10 := by
      unfold actionA
      rw [step109wc83s2_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 150 * (codeMat 111 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 417) (codeMat 412) (codeMat 3) = codeMat 6 := by
      unfold actionA
      rw [step109wc83s2_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 3 * (codeMat 111 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 417) (codeMat 412) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc83s2_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 2 * (codeMat 111 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact

theorem step109wc83s2Dispatch :
    QuotientRankAtLeast (o83SourceU_wc ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 412 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 417) (codeMat 412) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 417) (codeMat 412) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc83s2_contain hAct


private theorem step109wc83s3_QtInv :
    (codeMat 98 : Mat3).transpose⁻¹ = (codeMat 140 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 98 : Mat3).transpose * (codeMat 140 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc83s3_contain :
    (o83SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 98) (codeMat 98) orbit13W := by
  change spanCodes [258, 128, 68, 32, 16, 10, 1] ≤ actionW (codeMat 98) (codeMat 98) orbit13W
  apply step109wc83_spanCodes_le_of_gens [258, 128, 68, 32, 16, 10, 1]
    (actionW (codeMat 98) (codeMat 98) orbit13W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 80 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 80 (by decide)
    have hact : actionA (codeMat 98) (codeMat 98) (codeMat 80) = codeMat 258 := by
      unfold actionA
      rw [step109wc83s3_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 80 * (codeMat 140 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 98) (codeMat 98) (codeMat 8) = codeMat 128 := by
      unfold actionA
      rw [step109wc83s3_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 8 * (codeMat 140 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 160 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 98) (codeMat 98) (codeMat 160) = codeMat 68 := by
      unfold actionA
      rw [step109wc83s3_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 160 * (codeMat 140 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 98) (codeMat 98) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [step109wc83s3_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 2 * (codeMat 140 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 98) (codeMat 98) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc83s3_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 1 * (codeMat 140 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 68 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 98) (codeMat 98) (codeMat 68) = codeMat 10 := by
      unfold actionA
      rw [step109wc83s3_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 68 * (codeMat 140 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 98) (codeMat 98) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc83s3_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 256 * (codeMat 140 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact

theorem step109wc83s3Dispatch :
    QuotientRankAtLeast (o83SourceU_wc ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 98) (codeMat 98) orbit13W) 12 :=
    @quotientRankAtLeast_action (codeMat 98) (codeMat 98) hP hQ orbit13W 12
      orbit13_lb12
  exact quotientRankAtLeast_mono step109wc83s3_contain hAct


private theorem step109wc83s4_QtInv :
    (codeMat 372 : Mat3).transpose⁻¹ = (codeMat 93 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 372 : Mat3).transpose * (codeMat 93 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc83s4_contain :
    (o83SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 94) (codeMat 372) orbit13W := by
  change spanCodes [262, 132, 68, 32, 20, 10, 1] ≤ actionW (codeMat 94) (codeMat 372) orbit13W
  apply step109wc83_spanCodes_le_of_gens [262, 132, 68, 32, 20, 10, 1]
    (actionW (codeMat 94) (codeMat 372) orbit13W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 191 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 191 (by decide)
    have hact : actionA (codeMat 94) (codeMat 372) (codeMat 191) = codeMat 262 := by
      unfold actionA
      rw [step109wc83s4_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 191 * (codeMat 93 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 338 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 338 (by decide)
    have hact : actionA (codeMat 94) (codeMat 372) (codeMat 338) = codeMat 132 := by
      unfold actionA
      rw [step109wc83s4_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 338 * (codeMat 93 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 228 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 228 (by decide)
    have hact : actionA (codeMat 94) (codeMat 372) (codeMat 228) = codeMat 68 := by
      unfold actionA
      rw [step109wc83s4_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 228 * (codeMat 93 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 504 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 504 (by decide)
    have hact : actionA (codeMat 94) (codeMat 372) (codeMat 504) = codeMat 32 := by
      unfold actionA
      rw [step109wc83s4_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 504 * (codeMat 93 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 336 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 336 (by decide)
    have hact : actionA (codeMat 94) (codeMat 372) (codeMat 336) = codeMat 20 := by
      unfold actionA
      rw [step109wc83s4_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 336 * (codeMat 93 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 416 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 416 (by decide)
    have hact : actionA (codeMat 94) (codeMat 372) (codeMat 416) = codeMat 10 := by
      unfold actionA
      rw [step109wc83s4_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 416 * (codeMat 93 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 94) (codeMat 372) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc83s4_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 256 * (codeMat 93 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact

theorem step109wc83s4Dispatch :
    QuotientRankAtLeast (o83SourceU_wc ⟨4, by omega⟩) 12 := by
  have hP : Invertible (codeMat 94 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 372 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 94) (codeMat 372) orbit13W) 12 :=
    @quotientRankAtLeast_action (codeMat 94) (codeMat 372) hP hQ orbit13W 12
      orbit13_lb12
  exact quotientRankAtLeast_mono step109wc83s4_contain hAct


private theorem step109wc83s5_QtInv :
    (codeMat 212 : Mat3).transpose⁻¹ = (codeMat 86 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 212 : Mat3).transpose * (codeMat 86 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc83s5_contain :
    (o83SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 85) (codeMat 212) orbit13W := by
  change spanCodes [260, 134, 68, 32, 22, 10, 1] ≤ actionW (codeMat 85) (codeMat 212) orbit13W
  apply step109wc83_spanCodes_le_of_gens [260, 134, 68, 32, 22, 10, 1]
    (actionW (codeMat 85) (codeMat 212) orbit13W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 85) (codeMat 212) (codeMat 1) = codeMat 260 := by
      unfold actionA
      rw [step109wc83s5_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 1 * (codeMat 86 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 70 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 70 (by decide)
    have hact : actionA (codeMat 85) (codeMat 212) (codeMat 70) = codeMat 134 := by
      unfold actionA
      rw [step109wc83s5_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 70 * (codeMat 86 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 324 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 324 (by decide)
    have hact : actionA (codeMat 85) (codeMat 212) (codeMat 324) = codeMat 68 := by
      unfold actionA
      rw [step109wc83s5_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 324 * (codeMat 86 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 85) (codeMat 212) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc83s5_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 8 * (codeMat 86 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 496 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 496 (by decide)
    have hact : actionA (codeMat 85) (codeMat 212) (codeMat 496) = codeMat 22 := by
      unfold actionA
      rw [step109wc83s5_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 496 * (codeMat 86 : Mat3).transpose = codeMat 22
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 416 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 416 (by decide)
    have hact : actionA (codeMat 85) (codeMat 212) (codeMat 416) = codeMat 10 := by
      unfold actionA
      rw [step109wc83s5_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 416 * (codeMat 86 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 85) (codeMat 212) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc83s5_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 256 * (codeMat 86 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact

theorem step109wc83s5Dispatch :
    QuotientRankAtLeast (o83SourceU_wc ⟨5, by omega⟩) 12 := by
  have hP : Invertible (codeMat 85 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 212 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 85) (codeMat 212) orbit13W) 12 :=
    @quotientRankAtLeast_action (codeMat 85) (codeMat 212) hP hQ orbit13W 12
      orbit13_lb12
  exact quotientRankAtLeast_mono step109wc83s5_contain hAct


private theorem step109wc83s6_QtInv :
    (codeMat 107 : Mat3).transpose⁻¹ = (codeMat 428 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 107 : Mat3).transpose * (codeMat 428 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc83s6_contain :
    (o83SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 174) (codeMat 107) flatW_15 := by
  change spanCodes [256, 130, 68, 32, 18, 10, 1] ≤ actionW (codeMat 174) (codeMat 107) flatW_15
  apply step109wc83_spanCodes_le_of_gens [256, 130, 68, 32, 18, 10, 1]
    (actionW (codeMat 174) (codeMat 107) flatW_15)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 130 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 130 (by decide)
    have hact : actionA (codeMat 174) (codeMat 107) (codeMat 130) = codeMat 256 := by
      unfold actionA
      rw [step109wc83s6_QtInv]
      show (codeMat 174 : Mat3).transpose * codeMat 130 * (codeMat 428 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 174) (codeMat 107) (codeMat 8) = codeMat 130 := by
      unfold actionA
      rw [step109wc83s6_QtInv]
      show (codeMat 174 : Mat3).transpose * codeMat 8 * (codeMat 428 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 341 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 341 (by decide)
    have hact : actionA (codeMat 174) (codeMat 107) (codeMat 341) = codeMat 68 := by
      unfold actionA
      rw [step109wc83s6_QtInv]
      show (codeMat 174 : Mat3).transpose * codeMat 341 * (codeMat 428 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 174) (codeMat 107) (codeMat 128) = codeMat 32 := by
      unfold actionA
      rw [step109wc83s6_QtInv]
      show (codeMat 174 : Mat3).transpose * codeMat 128 * (codeMat 428 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 9 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 9 (by decide)
    have hact : actionA (codeMat 174) (codeMat 107) (codeMat 9) = codeMat 18 := by
      unfold actionA
      rw [step109wc83s6_QtInv]
      show (codeMat 174 : Mat3).transpose * codeMat 9 * (codeMat 428 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 393 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 393 (by decide)
    have hact : actionA (codeMat 174) (codeMat 107) (codeMat 393) = codeMat 10 := by
      unfold actionA
      rw [step109wc83s6_QtInv]
      show (codeMat 174 : Mat3).transpose * codeMat 393 * (codeMat 428 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 511 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 511 (by decide)
    have hact : actionA (codeMat 174) (codeMat 107) (codeMat 511) = codeMat 1 := by
      unfold actionA
      rw [step109wc83s6_QtInv]
      show (codeMat 174 : Mat3).transpose * codeMat 511 * (codeMat 428 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc83_codeMat_mem_actionW_of_witness hw hact

theorem step109wc83s6Dispatch :
    QuotientRankAtLeast (o83SourceU_wc ⟨6, by omega⟩) 9 := by
  have hP : Invertible (codeMat 174 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 107 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 174) (codeMat 107) flatW_15) 9 :=
    @quotientRankAtLeast_action (codeMat 174) (codeMat 107) hP hQ flatW_15 9
      flatSeed_15
  exact quotientRankAtLeast_mono step109wc83s6_contain hAct

theorem step109wc83_all_dispatch (i : Fin 7) :
    QuotientRankAtLeast (o83SourceU_wc i) (o83SourceLb_wc i) := by
  fin_cases i
  · exact step109wc83s0Dispatch
  · exact step109wc83s1Dispatch
  · exact step109wc83s2Dispatch
  · exact step109wc83s3Dispatch
  · exact step109wc83s4Dispatch
  · exact step109wc83s5Dispatch
  · exact step109wc83s6Dispatch

theorem step109_orbit83_lb14_wc : QuotientRankAtLeast o83W_wc 14 :=
  o83Lb14_wc step109wc83_all_dispatch

end QiushiMatmul
