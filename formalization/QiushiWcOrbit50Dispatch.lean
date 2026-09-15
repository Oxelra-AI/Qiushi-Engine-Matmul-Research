import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit50Consumer
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc50_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc50_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc50s0_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc50s0_contain :
    (o50SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 266) (codeMat 273) orbit10W := by
  change spanCodes [256, 132, 96, 16, 8, 2, 1] ≤ actionW (codeMat 266) (codeMat 273) orbit10W
  apply step109wc50_spanCodes_le_of_gens [256, 132, 96, 16, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 273) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step109wc50s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 256 * (codeMat 273 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 160) = codeMat 132 := by
      unfold actionA
      rw [step109wc50s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 160 * (codeMat 273 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 68) = codeMat 96 := by
      unfold actionA
      rw [step109wc50s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 68 * (codeMat 273 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 2) = codeMat 16 := by
      unfold actionA
      rw [step109wc50s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step109wc50s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 16) = codeMat 2 := by
      unfold actionA
      rw [step109wc50s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc50s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact

theorem step109wc50s0Dispatch :
    QuotientRankAtLeast (o50SourceU_wc ⟨0, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 273) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 273) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc50s0_contain hAct


private theorem step109wc50s1_QtInv :
    (codeMat 277 : Mat3).transpose⁻¹ = (codeMat 277 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 277 : Mat3).transpose * (codeMat 277 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc50s1_contain :
    (o50SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 465) (codeMat 277) orbit14W := by
  change spanCodes [260, 132, 96, 20, 8, 2, 1] ≤ actionW (codeMat 465) (codeMat 277) orbit14W
  apply step109wc50_spanCodes_le_of_gens [260, 132, 96, 20, 8, 2, 1]
    (actionW (codeMat 465) (codeMat 277) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 465) (codeMat 277) (codeMat 360) = codeMat 260 := by
      unfold actionA
      rw [step109wc50s1_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 360 * (codeMat 277 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 151 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 151 (by decide)
    have hact : actionA (codeMat 465) (codeMat 277) (codeMat 151) = codeMat 132 := by
      unfold actionA
      rw [step109wc50s1_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 151 * (codeMat 277 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 97 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 97 (by decide)
    have hact : actionA (codeMat 465) (codeMat 277) (codeMat 97) = codeMat 96 := by
      unfold actionA
      rw [step109wc50s1_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 97 * (codeMat 277 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 21 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 21 (by decide)
    have hact : actionA (codeMat 465) (codeMat 277) (codeMat 21) = codeMat 20 := by
      unfold actionA
      rw [step109wc50s1_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 21 * (codeMat 277 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 465) (codeMat 277) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc50s1_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 8 * (codeMat 277 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 465) (codeMat 277) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc50s1_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 2 * (codeMat 277 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 465) (codeMat 277) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc50s1_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 1 * (codeMat 277 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact

theorem step109wc50s1Dispatch :
    QuotientRankAtLeast (o50SourceU_wc ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 465 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 277 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 465) (codeMat 277) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 465) (codeMat 277) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc50s1_contain hAct


private theorem step109wc50s2_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = (codeMat 267 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * (codeMat 267 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc50s2_contain :
    (o50SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 225) (codeMat 282) orbit14W := by
  change spanCodes [272, 132, 68, 36, 8, 2, 1] ≤ actionW (codeMat 225) (codeMat 282) orbit14W
  apply step109wc50_spanCodes_le_of_gens [272, 132, 68, 36, 8, 2, 1]
    (actionW (codeMat 225) (codeMat 282) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 227 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 227 (by decide)
    have hact : actionA (codeMat 225) (codeMat 282) (codeMat 227) = codeMat 272 := by
      unfold actionA
      rw [step109wc50s2_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 227 * (codeMat 267 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 28 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 28 (by decide)
    have hact : actionA (codeMat 225) (codeMat 282) (codeMat 28) = codeMat 132 := by
      unfold actionA
      rw [step109wc50s2_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 28 * (codeMat 267 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 20 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 20 (by decide)
    have hact : actionA (codeMat 225) (codeMat 282) (codeMat 20) = codeMat 68 := by
      unfold actionA
      rw [step109wc50s2_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 20 * (codeMat 267 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 225) (codeMat 282) (codeMat 256) = codeMat 36 := by
      unfold actionA
      rw [step109wc50s2_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 256 * (codeMat 267 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 130 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 130 (by decide)
    have hact : actionA (codeMat 225) (codeMat 282) (codeMat 130) = codeMat 8 := by
      unfold actionA
      rw [step109wc50s2_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 130 * (codeMat 267 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 225) (codeMat 282) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc50s2_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 3 * (codeMat 267 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 225) (codeMat 282) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc50s2_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 2 * (codeMat 267 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact

theorem step109wc50s2Dispatch :
    QuotientRankAtLeast (o50SourceU_wc ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 282) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 282) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc50s2_contain hAct


private theorem step109wc50s3_QtInv :
    (codeMat 428 : Mat3).transpose⁻¹ = (codeMat 107 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 428 : Mat3).transpose * (codeMat 107 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc50s3_contain :
    (o50SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 106) (codeMat 428) orbit14W := by
  change spanCodes [272, 132, 80, 48, 8, 2, 1] ≤ actionW (codeMat 106) (codeMat 428) orbit14W
  apply step109wc50_spanCodes_le_of_gens [272, 132, 80, 48, 8, 2, 1]
    (actionW (codeMat 106) (codeMat 428) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 508 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 508 (by decide)
    have hact : actionA (codeMat 106) (codeMat 428) (codeMat 508) = codeMat 272 := by
      unfold actionA
      rw [step109wc50s3_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 508 * (codeMat 107 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 224 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 224 (by decide)
    have hact : actionA (codeMat 106) (codeMat 428) (codeMat 224) = codeMat 132 := by
      unfold actionA
      rw [step109wc50s3_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 224 * (codeMat 107 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 148 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 148 (by decide)
    have hact : actionA (codeMat 106) (codeMat 428) (codeMat 148) = codeMat 80 := by
      unfold actionA
      rw [step109wc50s3_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 148 * (codeMat 107 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 106) (codeMat 428) (codeMat 3) = codeMat 48 := by
      unfold actionA
      rw [step109wc50s3_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 3 * (codeMat 107 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 106) (codeMat 428) (codeMat 2) = codeMat 8 := by
      unfold actionA
      rw [step109wc50s3_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 2 * (codeMat 107 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 106) (codeMat 428) (codeMat 256) = codeMat 2 := by
      unfold actionA
      rw [step109wc50s3_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 256 * (codeMat 107 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 106) (codeMat 428) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc50s3_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 128 * (codeMat 107 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact

theorem step109wc50s3Dispatch :
    QuotientRankAtLeast (o50SourceU_wc ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 106 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 428 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 106) (codeMat 428) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 106) (codeMat 428) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc50s3_contain hAct


private theorem step109wc50s4_QtInv :
    (codeMat 98 : Mat3).transpose⁻¹ = (codeMat 140 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 98 : Mat3).transpose * (codeMat 140 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc50s4_contain :
    (o50SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 161) (codeMat 98) flatW_9 := by
  change spanCodes [272, 128, 96, 8, 4, 2, 1] ≤ actionW (codeMat 161) (codeMat 98) flatW_9
  apply step109wc50_spanCodes_le_of_gens [272, 128, 96, 8, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 98) flatW_9)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 80 ∈ flatW_9 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 8, 4, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 161) (codeMat 98) (codeMat 80) = codeMat 272 := by
      unfold actionA
      rw [step109wc50s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 80 * (codeMat 140 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ flatW_9 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 98) (codeMat 8) = codeMat 128 := by
      unfold actionA
      rw [step109wc50s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 140 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 160 ∈ flatW_9 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 8, 4, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 98) (codeMat 160) = codeMat 96 := by
      unfold actionA
      rw [step109wc50s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * (codeMat 140 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ flatW_9 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 98) (codeMat 256) = codeMat 8 := by
      unfold actionA
      rw [step109wc50s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 140 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ flatW_9 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 98) (codeMat 2) = codeMat 4 := by
      unfold actionA
      rw [step109wc50s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 140 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ flatW_9 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 98) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step109wc50s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 140 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 4 ∈ flatW_9 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 161) (codeMat 98) (codeMat 4) = codeMat 1 := by
      unfold actionA
      rw [step109wc50s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 4 * (codeMat 140 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact

theorem step109wc50s4Dispatch :
    QuotientRankAtLeast (o50SourceU_wc ⟨4, by omega⟩) 9 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 98) flatW_9) 9 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 98) hP hQ flatW_9 9
      flatSeed_9
  exact quotientRankAtLeast_mono step109wc50s4_contain hAct

private def step109wc50s5SrcT : Submodule F2 Mat3 := spanCodes [256, 160, 64, 20, 8, 2, 1]

private theorem step109wc50s5SrcT_lb : QuotientRankAtLeast step109wc50s5SrcT 9 := by
  have ht := quotientRankAtLeast_transpose flatSeed_9
  have hle : step109wc50s5SrcT ≤ transposeW flatW_9 := by
    unfold step109wc50s5SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
    · subst h0
      show codeMat 256 ∈ Submodule.map transposeLinearMap flatW_9
      exact ⟨codeMat 256, spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 8, 4, 2, 1] 256 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 160 ∈ Submodule.map transposeLinearMap flatW_9
      exact ⟨codeMat 160, spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 8, 4, 2, 1] 160 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 64 ∈ Submodule.map transposeLinearMap flatW_9
      exact ⟨codeMat 4, spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 8, 4, 2, 1] 4 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 20 ∈ Submodule.map transposeLinearMap flatW_9
      exact ⟨codeMat 80, spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 8, 4, 2, 1] 80 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 8 ∈ Submodule.map transposeLinearMap flatW_9
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 8, 4, 2, 1] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h5
      show codeMat 2 ∈ Submodule.map transposeLinearMap flatW_9
      exact ⟨codeMat 8, spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 8, 4, 2, 1] 8 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h6
      show codeMat 1 ∈ Submodule.map transposeLinearMap flatW_9
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 8, 4, 2, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc50s5_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc50s5_contain :
    (o50SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 98) (codeMat 161) step109wc50s5SrcT := by
  change spanCodes [272, 132, 64, 32, 8, 2, 1] ≤ actionW (codeMat 98) (codeMat 161) step109wc50s5SrcT
  apply step109wc50_spanCodes_le_of_gens [272, 132, 64, 32, 8, 2, 1]
    (actionW (codeMat 98) (codeMat 161) step109wc50s5SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 20 ∈ step109wc50s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 20, 8, 2, 1] 20 (by decide)
    have hact : actionA (codeMat 98) (codeMat 161) (codeMat 20) = codeMat 272 := by
      unfold actionA
      rw [step109wc50s5_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 20 * (codeMat 161 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ step109wc50s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 20, 8, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 98) (codeMat 161) (codeMat 160) = codeMat 132 := by
      unfold actionA
      rw [step109wc50s5_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 160 * (codeMat 161 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ step109wc50s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 98) (codeMat 161) (codeMat 8) = codeMat 64 := by
      unfold actionA
      rw [step109wc50s5_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ step109wc50s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 98) (codeMat 161) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [step109wc50s5_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ step109wc50s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 98) (codeMat 161) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step109wc50s5_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ step109wc50s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 98) (codeMat 161) (codeMat 256) = codeMat 2 := by
      unfold actionA
      rw [step109wc50s5_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 256 * (codeMat 161 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 64 ∈ step109wc50s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 20, 8, 2, 1] 64 (by decide)
    have hact : actionA (codeMat 98) (codeMat 161) (codeMat 64) = codeMat 1 := by
      unfold actionA
      rw [step109wc50s5_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 64 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact

theorem step109wc50s5Dispatch :
    QuotientRankAtLeast (o50SourceU_wc ⟨5, by omega⟩) 9 := by
  have hP : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 98) (codeMat 161) step109wc50s5SrcT) 9 :=
    @quotientRankAtLeast_action (codeMat 98) (codeMat 161) hP hQ step109wc50s5SrcT 9
      step109wc50s5SrcT_lb
  exact quotientRankAtLeast_mono step109wc50s5_contain hAct


private theorem step109wc50s6_QtInv :
    (codeMat 244 : Mat3).transpose⁻¹ = (codeMat 95 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 244 : Mat3).transpose * (codeMat 95 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc50s6_contain :
    (o50SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 95) (codeMat 244) flatW_15 := by
  change spanCodes [272, 132, 84, 52, 8, 2, 1] ≤ actionW (codeMat 95) (codeMat 244) flatW_15
  apply step109wc50_spanCodes_le_of_gens [272, 132, 84, 52, 8, 2, 1]
    (actionW (codeMat 95) (codeMat 244) flatW_15)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 427 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 427 (by decide)
    have hact : actionA (codeMat 95) (codeMat 244) (codeMat 427) = codeMat 272 := by
      unfold actionA
      rw [step109wc50s6_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 427 * (codeMat 95 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 246 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 246 (by decide)
    have hact : actionA (codeMat 95) (codeMat 244) (codeMat 246) = codeMat 132 := by
      unfold actionA
      rw [step109wc50s6_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 246 * (codeMat 95 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 340 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 340 (by decide)
    have hact : actionA (codeMat 95) (codeMat 244) (codeMat 340) = codeMat 84 := by
      unfold actionA
      rw [step109wc50s6_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 340 * (codeMat 95 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 424 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 424 (by decide)
    have hact : actionA (codeMat 95) (codeMat 244) (codeMat 424) = codeMat 52 := by
      unfold actionA
      rw [step109wc50s6_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 424 * (codeMat 95 : Mat3).transpose = codeMat 52
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 288 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 288 (by decide)
    have hact : actionA (codeMat 95) (codeMat 244) (codeMat 288) = codeMat 8 := by
      unfold actionA
      rw [step109wc50s6_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 288 * (codeMat 95 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 384 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 95) (codeMat 244) (codeMat 384) = codeMat 2 := by
      unfold actionA
      rw [step109wc50s6_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 384 * (codeMat 95 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 95) (codeMat 244) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc50s6_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 256 * (codeMat 95 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc50_codeMat_mem_actionW_of_witness hw hact

theorem step109wc50s6Dispatch :
    QuotientRankAtLeast (o50SourceU_wc ⟨6, by omega⟩) 9 := by
  have hP : Invertible (codeMat 95 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 244 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 95) (codeMat 244) flatW_15) 9 :=
    @quotientRankAtLeast_action (codeMat 95) (codeMat 244) hP hQ flatW_15 9
      flatSeed_15
  exact quotientRankAtLeast_mono step109wc50s6_contain hAct

theorem step109wc50_all_dispatch (i : Fin 7) :
    QuotientRankAtLeast (o50SourceU_wc i) (o50SourceLb_wc i) := by
  fin_cases i
  · exact step109wc50s0Dispatch
  · exact step109wc50s1Dispatch
  · exact step109wc50s2Dispatch
  · exact step109wc50s3Dispatch
  · exact step109wc50s4Dispatch
  · exact step109wc50s5Dispatch
  · exact step109wc50s6Dispatch

theorem step109_orbit50_lb13_wc : QuotientRankAtLeast o50W_wc 13 :=
  o50Lb13_wc step109wc50_all_dispatch

end QiushiMatmul
