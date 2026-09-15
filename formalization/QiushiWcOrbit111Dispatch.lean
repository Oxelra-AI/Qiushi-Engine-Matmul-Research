import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit111Consumer
import QiushiOrbit23FP
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiOrbit10FP
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc111_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc111_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc111s0_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc111s0_contain :
    (o111SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 161) (codeMat 140) orbit23W := by
  change spanCodes [256, 96, 8, 4, 2, 1] ≤ actionW (codeMat 161) (codeMat 140) orbit23W
  apply step109wc111_spanCodes_le_of_gens [256, 96, 8, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 140) orbit23W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 8 ∈ orbit23W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 80, 128] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 140) (codeMat 8) = codeMat 256 := by
      unfold actionA
      rw [step109wc111s0_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 80 ∈ orbit23W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 80, 128] 80 (by decide)
    have hact : actionA (codeMat 161) (codeMat 140) (codeMat 80) = codeMat 96 := by
      unfold actionA
      rw [step109wc111s0_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 80 * (codeMat 98 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 128 ∈ orbit23W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 80, 128] 128 (by decide)
    have hact : actionA (codeMat 161) (codeMat 140) (codeMat 128) = codeMat 8 := by
      unfold actionA
      rw [step109wc111s0_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 128 * (codeMat 98 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ orbit23W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 80, 128] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 140) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step109wc111s0_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 4 ∈ orbit23W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 80, 128] 4 (by decide)
    have hact : actionA (codeMat 161) (codeMat 140) (codeMat 4) = codeMat 2 := by
      unfold actionA
      rw [step109wc111s0_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 4 * (codeMat 98 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ orbit23W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 80, 128] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 140) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc111s0_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact

theorem step109wc111s0Dispatch :
    QuotientRankAtLeast (o111SourceU_wc ⟨0, by omega⟩) 12 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 140) orbit23W) 12 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 140) hP hQ orbit23W 12
      orbit23_lb12
  exact quotientRankAtLeast_mono step109wc111s0_contain hAct


private theorem step109wc111s1_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc111s1_contain :
    (o111SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 267) (codeMat 161) orbit11W := by
  change spanCodes [256, 68, 36, 20, 8, 2, 1] ≤ actionW (codeMat 267) (codeMat 161) orbit11W
  apply step109wc111_spanCodes_le_of_gens [256, 68, 36, 20, 8, 2, 1]
    (actionW (codeMat 267) (codeMat 161) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 267) (codeMat 161) (codeMat 128) = codeMat 256 := by
      unfold actionA
      rw [step109wc111s1_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 128 * (codeMat 161 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 80 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 80 (by decide)
    have hact : actionA (codeMat 267) (codeMat 161) (codeMat 80) = codeMat 68 := by
      unfold actionA
      rw [step109wc111s1_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 80 * (codeMat 161 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 2 (by decide)
    have hact : actionA (codeMat 267) (codeMat 161) (codeMat 2) = codeMat 36 := by
      unfold actionA
      rw [step109wc111s1_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 52 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 52 (by decide)
    have hact : actionA (codeMat 267) (codeMat 161) (codeMat 52) = codeMat 20 := by
      unfold actionA
      rw [step109wc111s1_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 52 * (codeMat 161 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 9 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 9 (by decide)
    have hact : actionA (codeMat 267) (codeMat 161) (codeMat 9) = codeMat 8 := by
      unfold actionA
      rw [step109wc111s1_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 9 * (codeMat 161 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 267) (codeMat 161) (codeMat 32) = codeMat 2 := by
      unfold actionA
      rw [step109wc111s1_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 32 * (codeMat 161 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 8 (by decide)
    have hact : actionA (codeMat 267) (codeMat 161) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc111s1_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact

theorem step109wc111s1Dispatch :
    QuotientRankAtLeast (o111SourceU_wc ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 161) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 161) hP hQ orbit11W 12
      orbit11_lb12
  exact quotientRankAtLeast_mono step109wc111s1_contain hAct


private theorem step109wc111s2_QtInv :
    (codeMat 277 : Mat3).transpose⁻¹ = (codeMat 277 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 277 : Mat3).transpose * (codeMat 277 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc111s2_contain :
    (o111SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 401) (codeMat 277) orbit14W := by
  change spanCodes [256, 132, 96, 20, 8, 2, 1] ≤ actionW (codeMat 401) (codeMat 277) orbit14W
  apply step109wc111_spanCodes_le_of_gens [256, 132, 96, 20, 8, 2, 1]
    (actionW (codeMat 401) (codeMat 277) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 401) (codeMat 277) (codeMat 360) = codeMat 256 := by
      unfold actionA
      rw [step109wc111s2_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 360 * (codeMat 277 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 149 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 149 (by decide)
    have hact : actionA (codeMat 401) (codeMat 277) (codeMat 149) = codeMat 132 := by
      unfold actionA
      rw [step109wc111s2_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 149 * (codeMat 277 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 401) (codeMat 277) (codeMat 96) = codeMat 96 := by
      unfold actionA
      rw [step109wc111s2_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 96 * (codeMat 277 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 21 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 21 (by decide)
    have hact : actionA (codeMat 401) (codeMat 277) (codeMat 21) = codeMat 20 := by
      unfold actionA
      rw [step109wc111s2_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 21 * (codeMat 277 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 401) (codeMat 277) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc111s2_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 8 * (codeMat 277 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 401) (codeMat 277) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc111s2_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 2 * (codeMat 277 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 401) (codeMat 277) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc111s2_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 1 * (codeMat 277 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact

theorem step109wc111s2Dispatch :
    QuotientRankAtLeast (o111SourceU_wc ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 277 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 401) (codeMat 277) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 401) (codeMat 277) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc111s2_contain hAct


private theorem step109wc111s3_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc111s3_contain :
    (o111SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 273) (codeMat 273) orbit14W := by
  change spanCodes [256, 128, 96, 20, 8, 2, 1] ≤ actionW (codeMat 273) (codeMat 273) orbit14W
  apply step109wc111_spanCodes_le_of_gens [256, 128, 96, 20, 8, 2, 1]
    (actionW (codeMat 273) (codeMat 273) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step109wc111s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 273 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 128) = codeMat 128 := by
      unfold actionA
      rw [step109wc111s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 128 * (codeMat 273 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 96) = codeMat 96 := by
      unfold actionA
      rw [step109wc111s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 96 * (codeMat 273 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 20 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 20) = codeMat 20 := by
      unfold actionA
      rw [step109wc111s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * (codeMat 273 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc111s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc111s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc111s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact

theorem step109wc111s3Dispatch :
    QuotientRankAtLeast (o111SourceU_wc ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 273) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 273) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc111s3_contain hAct


private theorem step109wc111s4_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc111s4_contain :
    (o111SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 266) (codeMat 273) orbit10W := by
  change spanCodes [256, 132, 96, 16, 8, 2, 1] ≤ actionW (codeMat 266) (codeMat 273) orbit10W
  apply step109wc111_spanCodes_le_of_gens [256, 132, 96, 16, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 273) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step109wc111s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 256 * (codeMat 273 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 160) = codeMat 132 := by
      unfold actionA
      rw [step109wc111s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 160 * (codeMat 273 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 68) = codeMat 96 := by
      unfold actionA
      rw [step109wc111s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 68 * (codeMat 273 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 2) = codeMat 16 := by
      unfold actionA
      rw [step109wc111s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step109wc111s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 16) = codeMat 2 := by
      unfold actionA
      rw [step109wc111s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc111s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact

theorem step109wc111s4Dispatch :
    QuotientRankAtLeast (o111SourceU_wc ⟨4, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 273) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 273) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc111s4_contain hAct


private theorem step109wc111s5_QtInv :
    (codeMat 279 : Mat3).transpose⁻¹ = (codeMat 279 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 279 : Mat3).transpose * (codeMat 279 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc111s5_contain :
    (o111SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 401) (codeMat 279) orbit14W := by
  change spanCodes [256, 164, 96, 20, 8, 2, 1] ≤ actionW (codeMat 401) (codeMat 279) orbit14W
  apply step109wc111_spanCodes_le_of_gens [256, 164, 96, 20, 8, 2, 1]
    (actionW (codeMat 401) (codeMat 279) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 401) (codeMat 279) (codeMat 360) = codeMat 256 := by
      unfold actionA
      rw [step109wc111s5_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 360 * (codeMat 279 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 245 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 245 (by decide)
    have hact : actionA (codeMat 401) (codeMat 279) (codeMat 245) = codeMat 164 := by
      unfold actionA
      rw [step109wc111s5_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 245 * (codeMat 279 : Mat3).transpose = codeMat 164
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 401) (codeMat 279) (codeMat 96) = codeMat 96 := by
      unfold actionA
      rw [step109wc111s5_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 96 * (codeMat 279 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 29 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 29 (by decide)
    have hact : actionA (codeMat 401) (codeMat 279) (codeMat 29) = codeMat 20 := by
      unfold actionA
      rw [step109wc111s5_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 29 * (codeMat 279 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 401) (codeMat 279) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc111s5_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 8 * (codeMat 279 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 401) (codeMat 279) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc111s5_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 3 * (codeMat 279 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 401) (codeMat 279) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc111s5_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 1 * (codeMat 279 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact

theorem step109wc111s5Dispatch :
    QuotientRankAtLeast (o111SourceU_wc ⟨5, by omega⟩) 12 := by
  have hP : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 279 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 401) (codeMat 279) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 401) (codeMat 279) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc111s5_contain hAct


private theorem step109wc111s6_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = (codeMat 275 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * (codeMat 275 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc111s6_contain :
    (o111SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 273) (codeMat 275) orbit14W := by
  change spanCodes [256, 160, 96, 20, 8, 2, 1] ≤ actionW (codeMat 273) (codeMat 275) orbit14W
  apply step109wc111_spanCodes_le_of_gens [256, 160, 96, 20, 8, 2, 1]
    (actionW (codeMat 273) (codeMat 275) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step109wc111s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 275 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 224 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 224 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 224) = codeMat 160 := by
      unfold actionA
      rw [step109wc111s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 224 * (codeMat 275 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 96) = codeMat 96 := by
      unfold actionA
      rw [step109wc111s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 96 * (codeMat 275 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 28 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 28 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 28) = codeMat 20 := by
      unfold actionA
      rw [step109wc111s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 28 * (codeMat 275 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc111s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 275 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc111s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 3 * (codeMat 275 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc111s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 275 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact

theorem step109wc111s6Dispatch :
    QuotientRankAtLeast (o111SourceU_wc ⟨6, by omega⟩) 12 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 275) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 275) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc111s6_contain hAct

private def step109wc111s7SrcT : Submodule F2 Mat3 := spanCodes [256, 132, 64, 16, 8, 2, 1]

private theorem step109wc111s7SrcT_lb : QuotientRankAtLeast step109wc111s7SrcT 9 := by
  have ht := quotientRankAtLeast_transpose flatSeed_7
  have hle : step109wc111s7SrcT ≤ transposeW flatW_7 := by
    unfold step109wc111s7SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
    · subst h0
      show codeMat 256 ∈ Submodule.map transposeLinearMap flatW_7
      exact ⟨codeMat 256, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 256 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 132 ∈ Submodule.map transposeLinearMap flatW_7
      exact ⟨codeMat 96, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 96 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 64 ∈ Submodule.map transposeLinearMap flatW_7
      exact ⟨codeMat 4, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 4 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 16 ∈ Submodule.map transposeLinearMap flatW_7
      exact ⟨codeMat 16, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 16 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 8 ∈ Submodule.map transposeLinearMap flatW_7
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h5
      show codeMat 2 ∈ Submodule.map transposeLinearMap flatW_7
      exact ⟨codeMat 8, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 8 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h6
      show codeMat 1 ∈ Submodule.map transposeLinearMap flatW_7
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc111s7_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc111s7_contain :
    (o111SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 98) (codeMat 161) step109wc111s7SrcT := by
  change spanCodes [256, 64, 32, 20, 8, 2, 1] ≤ actionW (codeMat 98) (codeMat 161) step109wc111s7SrcT
  apply step109wc111_spanCodes_le_of_gens [256, 64, 32, 20, 8, 2, 1]
    (actionW (codeMat 98) (codeMat 161) step109wc111s7SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 16 ∈ step109wc111s7SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 98) (codeMat 161) (codeMat 16) = codeMat 256 := by
      unfold actionA
      rw [step109wc111s7_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 16 * (codeMat 161 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ step109wc111s7SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 98) (codeMat 161) (codeMat 8) = codeMat 64 := by
      unfold actionA
      rw [step109wc111s7_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ step109wc111s7SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 98) (codeMat 161) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [step109wc111s7_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 132 ∈ step109wc111s7SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 132 (by decide)
    have hact : actionA (codeMat 98) (codeMat 161) (codeMat 132) = codeMat 20 := by
      unfold actionA
      rw [step109wc111s7_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 132 * (codeMat 161 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ step109wc111s7SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 98) (codeMat 161) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step109wc111s7_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ step109wc111s7SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 98) (codeMat 161) (codeMat 256) = codeMat 2 := by
      unfold actionA
      rw [step109wc111s7_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 256 * (codeMat 161 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 64 ∈ step109wc111s7SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 64 (by decide)
    have hact : actionA (codeMat 98) (codeMat 161) (codeMat 64) = codeMat 1 := by
      unfold actionA
      rw [step109wc111s7_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 64 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc111_codeMat_mem_actionW_of_witness hw hact

theorem step109wc111s7Dispatch :
    QuotientRankAtLeast (o111SourceU_wc ⟨7, by omega⟩) 9 := by
  have hP : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 98) (codeMat 161) step109wc111s7SrcT) 9 :=
    @quotientRankAtLeast_action (codeMat 98) (codeMat 161) hP hQ step109wc111s7SrcT 9
      step109wc111s7SrcT_lb
  exact quotientRankAtLeast_mono step109wc111s7_contain hAct

theorem step109wc111_all_dispatch (i : Fin 8) :
    QuotientRankAtLeast (o111SourceU_wc i) (o111SourceLb_wc i) := by
  fin_cases i
  · exact step109wc111s0Dispatch
  · exact step109wc111s1Dispatch
  · exact step109wc111s2Dispatch
  · exact step109wc111s3Dispatch
  · exact step109wc111s4Dispatch
  · exact step109wc111s5Dispatch
  · exact step109wc111s6Dispatch
  · exact step109wc111s7Dispatch

theorem step109_orbit111_lb14_wc : QuotientRankAtLeast o111W_wc 14 :=
  o111Lb14_wc step109wc111_all_dispatch

end QiushiMatmul
