import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit45Consumer
import QiushiOrbit10FP
import QiushiOrbit13FP
import QiushiOrbit14FP
import QiushiOrbit5FP
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc45_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc45_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc45s0_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc45s0_contain :
    (o45SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 266) (codeMat 266) orbit10W := by
  change spanCodes [256, 160, 68, 16, 8, 2, 1] ≤ actionW (codeMat 266) (codeMat 266) orbit10W
  apply step109wc45_spanCodes_le_of_gens [256, 160, 68, 16, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 266) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step109wc45s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 256 * (codeMat 266 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 68) = codeMat 160 := by
      unfold actionA
      rw [step109wc45s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 68 * (codeMat 266 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 160) = codeMat 68 := by
      unfold actionA
      rw [step109wc45s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 160 * (codeMat 266 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc45s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 2) = codeMat 8 := by
      unfold actionA
      rw [step109wc45s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 8) = codeMat 2 := by
      unfold actionA
      rw [step109wc45s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc45s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact

theorem step109wc45s0Dispatch :
    QuotientRankAtLeast (o45SourceU_wc ⟨0, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 266) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 266) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc45s0_contain hAct


private theorem step109wc45s1_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc45s1_contain :
    (o45SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 273) (codeMat 273) orbit13W := by
  change spanCodes [256, 160, 68, 20, 8, 2, 1] ≤ actionW (codeMat 273) (codeMat 273) orbit13W
  apply step109wc45_spanCodes_le_of_gens [256, 160, 68, 20, 8, 2, 1]
    (actionW (codeMat 273) (codeMat 273) orbit13W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step109wc45s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 273 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 160) = codeMat 160 := by
      unfold actionA
      rw [step109wc45s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 160 * (codeMat 273 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step109wc45s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 68 * (codeMat 273 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 20 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 20) = codeMat 20 := by
      unfold actionA
      rw [step109wc45s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * (codeMat 273 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc45s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc45s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc45s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact

theorem step109wc45s1Dispatch :
    QuotientRankAtLeast (o45SourceU_wc ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 273) orbit13W) 12 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 273) hP hQ orbit13W 12
      orbit13_lb12
  exact quotientRankAtLeast_mono step109wc45s1_contain hAct


private theorem step109wc45s2_QtInv :
    (codeMat 270 : Mat3).transpose⁻¹ = (codeMat 298 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 270 : Mat3).transpose * (codeMat 298 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc45s2_contain :
    (o45SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 177) (codeMat 270) orbit14W := by
  change spanCodes [256, 144, 68, 48, 8, 2, 1] ≤ actionW (codeMat 177) (codeMat 270) orbit14W
  apply step109wc45_spanCodes_le_of_gens [256, 144, 68, 48, 8, 2, 1]
    (actionW (codeMat 177) (codeMat 270) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 177) (codeMat 270) (codeMat 360) = codeMat 256 := by
      unfold actionA
      rw [step109wc45s2_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 360 * (codeMat 298 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 177) (codeMat 270) (codeMat 8) = codeMat 144 := by
      unfold actionA
      rw [step109wc45s2_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 8 * (codeMat 298 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 149 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 149 (by decide)
    have hact : actionA (codeMat 177) (codeMat 270) (codeMat 149) = codeMat 68 := by
      unfold actionA
      rw [step109wc45s2_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 149 * (codeMat 298 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 177) (codeMat 270) (codeMat 256) = codeMat 48 := by
      unfold actionA
      rw [step109wc45s2_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 256 * (codeMat 298 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 177) (codeMat 270) (codeMat 128) = codeMat 8 := by
      unfold actionA
      rw [step109wc45s2_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 128 * (codeMat 298 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 270) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step109wc45s2_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * (codeMat 298 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 177) (codeMat 270) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc45s2_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 2 * (codeMat 298 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact

theorem step109wc45s2Dispatch :
    QuotientRankAtLeast (o45SourceU_wc ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 270 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 270) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 270) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc45s2_contain hAct


private theorem step109wc45s3_QtInv :
    (codeMat 318 : Mat3).transpose⁻¹ = (codeMat 299 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 318 : Mat3).transpose * (codeMat 299 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc45s3_contain :
    (o45SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 241) (codeMat 318) orbit14W := by
  change spanCodes [256, 148, 68, 52, 8, 2, 1] ≤ actionW (codeMat 241) (codeMat 318) orbit14W
  apply step109wc45_spanCodes_le_of_gens [256, 148, 68, 52, 8, 2, 1]
    (actionW (codeMat 241) (codeMat 318) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 511 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 511 (by decide)
    have hact : actionA (codeMat 241) (codeMat 318) (codeMat 511) = codeMat 256 := by
      unfold actionA
      rw [step109wc45s3_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 511 * (codeMat 299 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 31 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 31 (by decide)
    have hact : actionA (codeMat 241) (codeMat 318) (codeMat 31) = codeMat 148 := by
      unfold actionA
      rw [step109wc45s3_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 31 * (codeMat 299 : Mat3).transpose = codeMat 148
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 149 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 149 (by decide)
    have hact : actionA (codeMat 241) (codeMat 318) (codeMat 149) = codeMat 68 := by
      unfold actionA
      rw [step109wc45s3_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 149 * (codeMat 299 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 259 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 259 (by decide)
    have hact : actionA (codeMat 241) (codeMat 318) (codeMat 259) = codeMat 52 := by
      unfold actionA
      rw [step109wc45s3_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 259 * (codeMat 299 : Mat3).transpose = codeMat 52
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 130 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 130 (by decide)
    have hact : actionA (codeMat 241) (codeMat 318) (codeMat 130) = codeMat 8 := by
      unfold actionA
      rw [step109wc45s3_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 130 * (codeMat 299 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 241) (codeMat 318) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc45s3_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 3 * (codeMat 299 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 241) (codeMat 318) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc45s3_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 2 * (codeMat 299 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact

theorem step109wc45s3Dispatch :
    QuotientRankAtLeast (o45SourceU_wc ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 241 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 318 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 241) (codeMat 318) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 241) (codeMat 318) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc45s3_contain hAct


private theorem step109wc45s4_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc45s4_contain :
    (o45SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 161) (codeMat 161) orbit5W := by
  change spanCodes [256, 160, 64, 8, 4, 2, 1] ≤ actionW (codeMat 161) (codeMat 161) orbit5W
  apply step109wc45_spanCodes_le_of_gens [256, 160, 64, 8, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 161) orbit5W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 16 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 16 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 16) = codeMat 256 := by
      unfold actionA
      rw [step109wc45s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 16 * (codeMat 161 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 160) = codeMat 160 := by
      unfold actionA
      rw [step109wc45s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * (codeMat 161 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 8) = codeMat 64 := by
      unfold actionA
      rw [step109wc45s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 64 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 64 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 64) = codeMat 8 := by
      unfold actionA
      rw [step109wc45s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 64 * (codeMat 161 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 2) = codeMat 4 := by
      unfold actionA
      rw [step109wc45s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 4 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 4 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 4) = codeMat 2 := by
      unfold actionA
      rw [step109wc45s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 4 * (codeMat 161 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc45s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact

theorem step109wc45s4Dispatch :
    QuotientRankAtLeast (o45SourceU_wc ⟨4, by omega⟩) 9 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 161) orbit5W) 9 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 161) hP hQ orbit5W 9
      orbit5_lb9
  exact quotientRankAtLeast_mono step109wc45s4_contain hAct


private theorem step109wc45s5_QtInv :
    (codeMat 98 : Mat3).transpose⁻¹ = (codeMat 140 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 98 : Mat3).transpose * (codeMat 140 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc45s5_contain :
    (o45SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 140) (codeMat 98) flatW_12 := by
  change spanCodes [256, 128, 68, 32, 8, 2, 1] ≤ actionW (codeMat 140) (codeMat 98) flatW_12
  apply step109wc45_spanCodes_le_of_gens [256, 128, 68, 32, 8, 2, 1]
    (actionW (codeMat 140) (codeMat 98) flatW_12)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 2 ∈ flatW_12 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 98) (codeMat 2) = codeMat 256 := by
      unfold actionA
      rw [step109wc45s5_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 140 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ flatW_12 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 98) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step109wc45s5_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * (codeMat 140 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 20 ∈ flatW_12 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 32, 20, 8, 2, 1] 20 (by decide)
    have hact : actionA (codeMat 140) (codeMat 98) (codeMat 20) = codeMat 68 := by
      unfold actionA
      rw [step109wc45s5_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 20 * (codeMat 140 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ flatW_12 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 140) (codeMat 98) (codeMat 128) = codeMat 32 := by
      unfold actionA
      rw [step109wc45s5_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 128 * (codeMat 140 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ flatW_12 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 140) (codeMat 98) (codeMat 256) = codeMat 8 := by
      unfold actionA
      rw [step109wc45s5_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 256 * (codeMat 140 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ flatW_12 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 140) (codeMat 98) (codeMat 8) = codeMat 2 := by
      unfold actionA
      rw [step109wc45s5_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 8 * (codeMat 140 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 32 ∈ flatW_12 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 32, 20, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 140) (codeMat 98) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc45s5_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 32 * (codeMat 140 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact

theorem step109wc45s5Dispatch :
    QuotientRankAtLeast (o45SourceU_wc ⟨5, by omega⟩) 9 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 98) flatW_12) 9 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 98) hP hQ flatW_12 9
      flatSeed_12
  exact quotientRankAtLeast_mono step109wc45s5_contain hAct


private theorem step109wc45s6_QtInv :
    (codeMat 226 : Mat3).transpose⁻¹ = (codeMat 141 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 226 : Mat3).transpose * (codeMat 141 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc45s6_contain :
    (o45SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 204) (codeMat 226) flatW_12 := by
  change spanCodes [256, 132, 68, 36, 8, 2, 1] ≤ actionW (codeMat 204) (codeMat 226) flatW_12
  apply step109wc45_spanCodes_le_of_gens [256, 132, 68, 36, 8, 2, 1]
    (actionW (codeMat 204) (codeMat 226) flatW_12)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 2 ∈ flatW_12 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 204) (codeMat 226) (codeMat 2) = codeMat 256 := by
      unfold actionA
      rw [step109wc45s6_QtInv]
      show (codeMat 204 : Mat3).transpose * codeMat 2 * (codeMat 141 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 21 ∈ flatW_12 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 32, 20, 8, 2, 1] 21 (by decide)
    have hact : actionA (codeMat 204) (codeMat 226) (codeMat 21) = codeMat 132 := by
      unfold actionA
      rw [step109wc45s6_QtInv]
      show (codeMat 204 : Mat3).transpose * codeMat 21 * (codeMat 141 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 20 ∈ flatW_12 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 32, 20, 8, 2, 1] 20 (by decide)
    have hact : actionA (codeMat 204) (codeMat 226) (codeMat 20) = codeMat 68 := by
      unfold actionA
      rw [step109wc45s6_QtInv]
      show (codeMat 204 : Mat3).transpose * codeMat 20 * (codeMat 141 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ flatW_12 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 204) (codeMat 226) (codeMat 128) = codeMat 36 := by
      unfold actionA
      rw [step109wc45s6_QtInv]
      show (codeMat 204 : Mat3).transpose * codeMat 128 * (codeMat 141 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 288 ∈ flatW_12 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 32, 20, 8, 2, 1] 288 (by decide)
    have hact : actionA (codeMat 204) (codeMat 226) (codeMat 288) = codeMat 8 := by
      unfold actionA
      rw [step109wc45s6_QtInv]
      show (codeMat 204 : Mat3).transpose * codeMat 288 * (codeMat 141 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 40 ∈ flatW_12 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 204) (codeMat 226) (codeMat 40) = codeMat 2 := by
      unfold actionA
      rw [step109wc45s6_QtInv]
      show (codeMat 204 : Mat3).transpose * codeMat 40 * (codeMat 141 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 32 ∈ flatW_12 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 32, 20, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 204) (codeMat 226) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc45s6_QtInv]
      show (codeMat 204 : Mat3).transpose * codeMat 32 * (codeMat 141 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc45_codeMat_mem_actionW_of_witness hw hact

theorem step109wc45s6Dispatch :
    QuotientRankAtLeast (o45SourceU_wc ⟨6, by omega⟩) 9 := by
  have hP : Invertible (codeMat 204 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 226 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 204) (codeMat 226) flatW_12) 9 :=
    @quotientRankAtLeast_action (codeMat 204) (codeMat 226) hP hQ flatW_12 9
      flatSeed_12
  exact quotientRankAtLeast_mono step109wc45s6_contain hAct

theorem step109wc45_all_dispatch (i : Fin 7) :
    QuotientRankAtLeast (o45SourceU_wc i) (o45SourceLb_wc i) := by
  fin_cases i
  · exact step109wc45s0Dispatch
  · exact step109wc45s1Dispatch
  · exact step109wc45s2Dispatch
  · exact step109wc45s3Dispatch
  · exact step109wc45s4Dispatch
  · exact step109wc45s5Dispatch
  · exact step109wc45s6Dispatch

theorem step109_orbit45_lb13_wc : QuotientRankAtLeast o45W_wc 13 :=
  o45Lb13_wc step109wc45_all_dispatch

end QiushiMatmul
