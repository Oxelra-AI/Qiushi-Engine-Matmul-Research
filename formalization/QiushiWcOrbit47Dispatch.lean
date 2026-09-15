import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit47Consumer
import QiushiOrbit10FP
import QiushiOrbit13FP
import QiushiOrbit14FP
import QiushiOrbit8Closed

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc47_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc47_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc47s0_QtInv :
    (codeMat 270 : Mat3).transpose⁻¹ = (codeMat 298 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 270 : Mat3).transpose * (codeMat 298 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc47s0_contain :
    (o47SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 266) (codeMat 270) orbit10W := by
  change spanCodes [288, 160, 68, 16, 8, 2, 1] ≤ actionW (codeMat 266) (codeMat 270) orbit10W
  apply step109wc47_spanCodes_le_of_gens [288, 160, 68, 16, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 270) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 325 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 325 (by decide)
    have hact : actionA (codeMat 266) (codeMat 270) (codeMat 325) = codeMat 288 := by
      unfold actionA
      rw [step109wc47s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 325 * (codeMat 298 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 69 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 69 (by decide)
    have hact : actionA (codeMat 266) (codeMat 270) (codeMat 69) = codeMat 160 := by
      unfold actionA
      rw [step109wc47s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 69 * (codeMat 298 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 168 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 168 (by decide)
    have hact : actionA (codeMat 266) (codeMat 270) (codeMat 168) = codeMat 68 := by
      unfold actionA
      rw [step109wc47s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 168 * (codeMat 298 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 270) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc47s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 298 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 270) (codeMat 2) = codeMat 8 := by
      unfold actionA
      rw [step109wc47s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 298 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 270) (codeMat 8) = codeMat 2 := by
      unfold actionA
      rw [step109wc47s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 298 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 270) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc47s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 298 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact

theorem step109wc47s0Dispatch :
    QuotientRankAtLeast (o47SourceU_wc ⟨0, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 270 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 270) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 270) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc47s0_contain hAct


private theorem step109wc47s1_QtInv :
    (codeMat 307 : Mat3).transpose⁻¹ = (codeMat 311 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 307 : Mat3).transpose * (codeMat 311 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc47s1_contain :
    (o47SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 273) (codeMat 307) orbit13W := by
  change spanCodes [292, 160, 68, 20, 8, 2, 1] ≤ actionW (codeMat 273) (codeMat 307) orbit13W
  apply step109wc47_spanCodes_le_of_gens [292, 160, 68, 20, 8, 2, 1]
    (actionW (codeMat 273) (codeMat 307) orbit13W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 438 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 438 (by decide)
    have hact : actionA (codeMat 273) (codeMat 307) (codeMat 438) = codeMat 292 := by
      unfold actionA
      rw [step109wc47s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 438 * (codeMat 311 : Mat3).transpose = codeMat 292
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 240 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 240 (by decide)
    have hact : actionA (codeMat 273) (codeMat 307) (codeMat 240) = codeMat 160 := by
      unfold actionA
      rw [step109wc47s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 240 * (codeMat 311 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 70 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 70 (by decide)
    have hact : actionA (codeMat 273) (codeMat 307) (codeMat 70) = codeMat 68 := by
      unfold actionA
      rw [step109wc47s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 70 * (codeMat 311 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 30 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 30 (by decide)
    have hact : actionA (codeMat 273) (codeMat 307) (codeMat 30) = codeMat 20 := by
      unfold actionA
      rw [step109wc47s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 30 * (codeMat 311 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 307) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc47s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 311 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 273) (codeMat 307) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc47s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 3 * (codeMat 311 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 307) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc47s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 311 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact

theorem step109wc47s1Dispatch :
    QuotientRankAtLeast (o47SourceU_wc ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 307 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 307) orbit13W) 12 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 307) hP hQ orbit13W 12
      orbit13_lb12
  exact quotientRankAtLeast_mono step109wc47s1_contain hAct


private theorem step109wc47s2_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc47s2_contain :
    (o47SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 161) (codeMat 266) orbit14W := by
  change spanCodes [272, 128, 68, 32, 8, 2, 1] ≤ actionW (codeMat 161) (codeMat 266) orbit14W
  apply step109wc47_spanCodes_le_of_gens [272, 128, 68, 32, 8, 2, 1]
    (actionW (codeMat 161) (codeMat 266) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 96) = codeMat 272 := by
      unfold actionA
      rw [step109wc47s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 96 * (codeMat 266 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 8) = codeMat 128 := by
      unfold actionA
      rw [step109wc47s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 20 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 20 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 20) = codeMat 68 := by
      unfold actionA
      rw [step109wc47s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 20 * (codeMat 266 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 256) = codeMat 32 := by
      unfold actionA
      rw [step109wc47s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 266 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 128) = codeMat 8 := by
      unfold actionA
      rw [step109wc47s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 128 * (codeMat 266 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step109wc47s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc47s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact

theorem step109wc47s2Dispatch :
    QuotientRankAtLeast (o47SourceU_wc ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 266) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 266) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc47s2_contain hAct


private theorem step109wc47s3_QtInv :
    (codeMat 314 : Mat3).transpose⁻¹ = (codeMat 271 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 314 : Mat3).transpose * (codeMat 271 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc47s3_contain :
    (o47SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 225) (codeMat 314) orbit14W := by
  change spanCodes [276, 132, 68, 36, 8, 2, 1] ≤ actionW (codeMat 225) (codeMat 314) orbit14W
  apply step109wc47_spanCodes_le_of_gens [276, 132, 68, 36, 8, 2, 1]
    (actionW (codeMat 225) (codeMat 314) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 245 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 245 (by decide)
    have hact : actionA (codeMat 225) (codeMat 314) (codeMat 245) = codeMat 276 := by
      unfold actionA
      rw [step109wc47s3_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 245 * (codeMat 271 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 30 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 30 (by decide)
    have hact : actionA (codeMat 225) (codeMat 314) (codeMat 30) = codeMat 132 := by
      unfold actionA
      rw [step109wc47s3_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 30 * (codeMat 271 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 22 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 22 (by decide)
    have hact : actionA (codeMat 225) (codeMat 314) (codeMat 22) = codeMat 68 := by
      unfold actionA
      rw [step109wc47s3_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 22 * (codeMat 271 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 225) (codeMat 314) (codeMat 384) = codeMat 36 := by
      unfold actionA
      rw [step109wc47s3_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 384 * (codeMat 271 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 130 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 130 (by decide)
    have hact : actionA (codeMat 225) (codeMat 314) (codeMat 130) = codeMat 8 := by
      unfold actionA
      rw [step109wc47s3_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 130 * (codeMat 271 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 225) (codeMat 314) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc47s3_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 3 * (codeMat 271 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 225) (codeMat 314) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc47s3_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 2 * (codeMat 271 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact

theorem step109wc47s3Dispatch :
    QuotientRankAtLeast (o47SourceU_wc ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 314 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 314) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 314) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc47s3_contain hAct


private theorem step109wc47s4_QtInv :
    (codeMat 270 : Mat3).transpose⁻¹ = (codeMat 298 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 270 : Mat3).transpose * (codeMat 298 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc47s4_contain :
    (o47SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 177) (codeMat 270) orbit14W := by
  change spanCodes [256, 144, 68, 48, 8, 2, 1] ≤ actionW (codeMat 177) (codeMat 270) orbit14W
  apply step109wc47_spanCodes_le_of_gens [256, 144, 68, 48, 8, 2, 1]
    (actionW (codeMat 177) (codeMat 270) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 177) (codeMat 270) (codeMat 360) = codeMat 256 := by
      unfold actionA
      rw [step109wc47s4_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 360 * (codeMat 298 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 177) (codeMat 270) (codeMat 8) = codeMat 144 := by
      unfold actionA
      rw [step109wc47s4_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 8 * (codeMat 298 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 149 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 149 (by decide)
    have hact : actionA (codeMat 177) (codeMat 270) (codeMat 149) = codeMat 68 := by
      unfold actionA
      rw [step109wc47s4_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 149 * (codeMat 298 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 177) (codeMat 270) (codeMat 256) = codeMat 48 := by
      unfold actionA
      rw [step109wc47s4_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 256 * (codeMat 298 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 177) (codeMat 270) (codeMat 128) = codeMat 8 := by
      unfold actionA
      rw [step109wc47s4_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 128 * (codeMat 298 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 270) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step109wc47s4_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * (codeMat 298 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 177) (codeMat 270) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc47s4_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 2 * (codeMat 298 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact

theorem step109wc47s4Dispatch :
    QuotientRankAtLeast (o47SourceU_wc ⟨4, by omega⟩) 12 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 270 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 270) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 270) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc47s4_contain hAct


private theorem step109wc47s5_QtInv :
    (codeMat 286 : Mat3).transpose⁻¹ = (codeMat 303 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 286 : Mat3).transpose * (codeMat 303 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc47s5_contain :
    (o47SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 241) (codeMat 286) orbit14W := by
  change spanCodes [260, 148, 68, 52, 8, 2, 1] ≤ actionW (codeMat 241) (codeMat 286) orbit14W
  apply step109wc47_spanCodes_le_of_gens [260, 148, 68, 52, 8, 2, 1]
    (actionW (codeMat 241) (codeMat 286) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 241) (codeMat 286) (codeMat 360) = codeMat 260 := by
      unfold actionA
      rw [step109wc47s5_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 360 * (codeMat 303 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 29 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 29 (by decide)
    have hact : actionA (codeMat 241) (codeMat 286) (codeMat 29) = codeMat 148 := by
      unfold actionA
      rw [step109wc47s5_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 29 * (codeMat 303 : Mat3).transpose = codeMat 148
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 151 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 151 (by decide)
    have hact : actionA (codeMat 241) (codeMat 286) (codeMat 151) = codeMat 68 := by
      unfold actionA
      rw [step109wc47s5_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 151 * (codeMat 303 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 387 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 387 (by decide)
    have hact : actionA (codeMat 241) (codeMat 286) (codeMat 387) = codeMat 52 := by
      unfold actionA
      rw [step109wc47s5_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 387 * (codeMat 303 : Mat3).transpose = codeMat 52
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 130 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 130 (by decide)
    have hact : actionA (codeMat 241) (codeMat 286) (codeMat 130) = codeMat 8 := by
      unfold actionA
      rw [step109wc47s5_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 130 * (codeMat 303 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 241) (codeMat 286) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc47s5_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 3 * (codeMat 303 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 241) (codeMat 286) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc47s5_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 2 * (codeMat 303 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact

theorem step109wc47s5Dispatch :
    QuotientRankAtLeast (o47SourceU_wc ⟨5, by omega⟩) 12 := by
  have hP : Invertible (codeMat 241 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 286 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 241) (codeMat 286) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 241) (codeMat 286) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc47s5_contain hAct


private theorem step109wc47s6_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc47s6_contain :
    (o47SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 161) (codeMat 161) orbit8W := by
  change spanCodes [304, 160, 64, 8, 4, 2, 1] ≤ actionW (codeMat 161) (codeMat 161) orbit8W
  apply step109wc47_spanCodes_le_of_gens [304, 160, 64, 8, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 161) orbit8W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 400 ∈ orbit8W :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 64, 8, 4, 2, 1] 400 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 400) = codeMat 304 := by
      unfold actionA
      rw [step109wc47s6_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 400 * (codeMat 161 : Mat3).transpose = codeMat 304
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ orbit8W :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 64, 8, 4, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 160) = codeMat 160 := by
      unfold actionA
      rw [step109wc47s6_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * (codeMat 161 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ orbit8W :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 64, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 8) = codeMat 64 := by
      unfold actionA
      rw [step109wc47s6_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 64 ∈ orbit8W :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 64, 8, 4, 2, 1] 64 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 64) = codeMat 8 := by
      unfold actionA
      rw [step109wc47s6_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 64 * (codeMat 161 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ orbit8W :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 64, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 2) = codeMat 4 := by
      unfold actionA
      rw [step109wc47s6_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 4 ∈ orbit8W :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 64, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 4) = codeMat 2 := by
      unfold actionA
      rw [step109wc47s6_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 4 * (codeMat 161 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ orbit8W :=
      spanContainsCodeCore_implies_mem_spanCodes [304, 160, 64, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc47s6_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc47_codeMat_mem_actionW_of_witness hw hact

theorem step109wc47s6Dispatch :
    QuotientRankAtLeast (o47SourceU_wc ⟨6, by omega⟩) 9 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 161) orbit8W) 9 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 161) hP hQ orbit8W 9
      orbit8_lb9
  exact quotientRankAtLeast_mono step109wc47s6_contain hAct

theorem step109wc47_all_dispatch (i : Fin 7) :
    QuotientRankAtLeast (o47SourceU_wc i) (o47SourceLb_wc i) := by
  fin_cases i
  · exact step109wc47s0Dispatch
  · exact step109wc47s1Dispatch
  · exact step109wc47s2Dispatch
  · exact step109wc47s3Dispatch
  · exact step109wc47s4Dispatch
  · exact step109wc47s5Dispatch
  · exact step109wc47s6Dispatch

theorem step109_orbit47_lb14_wc : QuotientRankAtLeast o47W_wc 14 :=
  o47Lb14_wc step109wc47_all_dispatch

end QiushiMatmul
