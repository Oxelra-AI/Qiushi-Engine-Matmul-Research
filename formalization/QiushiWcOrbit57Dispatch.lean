import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit57Consumer
import QiushiOrbit13FP
import QiushiOrbit14FP
import QiushiWcOrbit16Dispatch
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc57_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc57_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc57s0_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc57s0_contain :
    (o57SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 273) (codeMat 266) orbit13W := by
  change spanCodes [256, 132, 96, 16, 12, 2, 1] ≤ actionW (codeMat 273) (codeMat 266) orbit13W
  apply step109wc57_spanCodes_le_of_gens [256, 132, 96, 16, 12, 2, 1]
    (actionW (codeMat 273) (codeMat 266) orbit13W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 266) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step109wc57s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 266 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 273) (codeMat 266) (codeMat 68) = codeMat 132 := by
      unfold actionA
      rw [step109wc57s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 68 * (codeMat 266 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 160 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 273) (codeMat 266) (codeMat 160) = codeMat 96 := by
      unfold actionA
      rw [step109wc57s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 160 * (codeMat 266 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 266) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step109wc57s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 20 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 266) (codeMat 20) = codeMat 12 := by
      unfold actionA
      rw [step109wc57s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * (codeMat 266 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 266) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step109wc57s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 266) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc57s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact

theorem step109wc57s0Dispatch :
    QuotientRankAtLeast (o57SourceU_wc ⟨0, by omega⟩) 12 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 266) orbit13W) 12 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 266) hP hQ orbit13W 12
      orbit13_lb12
  exact quotientRankAtLeast_mono step109wc57s0_contain hAct


private theorem step109wc57s1_QtInv :
    (codeMat 317 : Mat3).transpose⁻¹ = (codeMat 285 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 317 : Mat3).transpose * (codeMat 285 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc57s1_contain :
    (o57SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 401) (codeMat 317) orbit14W := by
  change spanCodes [260, 132, 96, 20, 12, 2, 1] ≤ actionW (codeMat 401) (codeMat 317) orbit14W
  apply step109wc57_spanCodes_le_of_gens [260, 132, 96, 20, 12, 2, 1]
    (actionW (codeMat 401) (codeMat 317) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 511 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 511 (by decide)
    have hact : actionA (codeMat 401) (codeMat 317) (codeMat 511) = codeMat 260 := by
      unfold actionA
      rw [step109wc57s1_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 511 * (codeMat 285 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 151 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 151 (by decide)
    have hact : actionA (codeMat 401) (codeMat 317) (codeMat 151) = codeMat 132 := by
      unfold actionA
      rw [step109wc57s1_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 151 * (codeMat 285 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 224 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 224 (by decide)
    have hact : actionA (codeMat 401) (codeMat 317) (codeMat 224) = codeMat 96 := by
      unfold actionA
      rw [step109wc57s1_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 224 * (codeMat 285 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 23 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 23 (by decide)
    have hact : actionA (codeMat 401) (codeMat 317) (codeMat 23) = codeMat 20 := by
      unfold actionA
      rw [step109wc57s1_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 23 * (codeMat 285 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 31 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 31 (by decide)
    have hact : actionA (codeMat 401) (codeMat 317) (codeMat 31) = codeMat 12 := by
      unfold actionA
      rw [step109wc57s1_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 31 * (codeMat 285 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 401) (codeMat 317) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc57s1_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 2 * (codeMat 285 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 401) (codeMat 317) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step109wc57s1_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 3 * (codeMat 285 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact

theorem step109wc57s1Dispatch :
    QuotientRankAtLeast (o57SourceU_wc ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 317 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 401) (codeMat 317) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 401) (codeMat 317) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc57s1_contain hAct


private theorem step109wc57s2_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc57s2_contain :
    (o57SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 161) (codeMat 273) orbit13W := by
  change spanCodes [272, 132, 64, 32, 12, 2, 1] ≤ actionW (codeMat 161) (codeMat 273) orbit13W
  apply step109wc57_spanCodes_le_of_gens [272, 132, 64, 32, 12, 2, 1]
    (actionW (codeMat 161) (codeMat 273) orbit13W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 160 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 160) = codeMat 272 := by
      unfold actionA
      rw [step109wc57s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * (codeMat 273 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 20 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 20 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 20) = codeMat 132 := by
      unfold actionA
      rw [step109wc57s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 20 * (codeMat 273 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 8) = codeMat 64 := by
      unfold actionA
      rw [step109wc57s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 256) = codeMat 32 := by
      unfold actionA
      rw [step109wc57s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 273 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 68 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 68) = codeMat 12 := by
      unfold actionA
      rw [step109wc57s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 68 * (codeMat 273 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc57s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc57s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact

theorem step109wc57s2Dispatch :
    QuotientRankAtLeast (o57SourceU_wc ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 273) orbit13W) 12 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 273) hP hQ orbit13W 12
      orbit13_lb12
  exact quotientRankAtLeast_mono step109wc57s2_contain hAct


private theorem step109wc57s3_QtInv :
    (codeMat 318 : Mat3).transpose⁻¹ = (codeMat 299 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 318 : Mat3).transpose * (codeMat 299 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc57s3_contain :
    (o57SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 417) (codeMat 318) orbit14W := by
  change spanCodes [272, 132, 68, 36, 12, 2, 1] ≤ actionW (codeMat 417) (codeMat 318) orbit14W
  apply step109wc57_spanCodes_le_of_gens [272, 132, 68, 36, 12, 2, 1]
    (actionW (codeMat 417) (codeMat 318) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 224 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 224 (by decide)
    have hact : actionA (codeMat 417) (codeMat 318) (codeMat 224) = codeMat 272 := by
      unfold actionA
      rw [step109wc57s3_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 224 * (codeMat 299 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 31 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 31 (by decide)
    have hact : actionA (codeMat 417) (codeMat 318) (codeMat 31) = codeMat 132 := by
      unfold actionA
      rw [step109wc57s3_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 31 * (codeMat 299 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 23 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 23 (by decide)
    have hact : actionA (codeMat 417) (codeMat 318) (codeMat 23) = codeMat 68 := by
      unfold actionA
      rw [step109wc57s3_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 23 * (codeMat 299 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 511 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 511 (by decide)
    have hact : actionA (codeMat 417) (codeMat 318) (codeMat 511) = codeMat 36 := by
      unfold actionA
      rw [step109wc57s3_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 511 * (codeMat 299 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 151 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 151 (by decide)
    have hact : actionA (codeMat 417) (codeMat 318) (codeMat 151) = codeMat 12 := by
      unfold actionA
      rw [step109wc57s3_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 151 * (codeMat 299 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 417) (codeMat 318) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc57s3_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 3 * (codeMat 299 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 417) (codeMat 318) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc57s3_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 2 * (codeMat 299 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact

theorem step109wc57s3Dispatch :
    QuotientRankAtLeast (o57SourceU_wc ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 318 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 417) (codeMat 318) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 417) (codeMat 318) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc57s3_contain hAct


private theorem step109wc57s4_QtInv :
    (codeMat 244 : Mat3).transpose⁻¹ = (codeMat 95 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 244 : Mat3).transpose * (codeMat 95 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc57s4_contain :
    (o57SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 94) (codeMat 244) orbit14W := by
  change spanCodes [272, 132, 80, 48, 12, 2, 1] ≤ actionW (codeMat 94) (codeMat 244) orbit14W
  apply step109wc57_spanCodes_le_of_gens [272, 132, 80, 48, 12, 2, 1]
    (actionW (codeMat 94) (codeMat 244) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 363 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 363 (by decide)
    have hact : actionA (codeMat 94) (codeMat 244) (codeMat 363) = codeMat 272 := by
      unfold actionA
      rw [step109wc57s4_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 363 * (codeMat 95 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 374 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 374 (by decide)
    have hact : actionA (codeMat 94) (codeMat 244) (codeMat 374) = codeMat 132 := by
      unfold actionA
      rw [step109wc57s4_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 374 * (codeMat 95 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 148 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 148 (by decide)
    have hact : actionA (codeMat 94) (codeMat 244) (codeMat 148) = codeMat 80 := by
      unfold actionA
      rw [step109wc57s4_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 148 * (codeMat 95 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 94) (codeMat 244) (codeMat 360) = codeMat 48 := by
      unfold actionA
      rw [step109wc57s4_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 360 * (codeMat 95 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 480 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 480 (by decide)
    have hact : actionA (codeMat 94) (codeMat 244) (codeMat 480) = codeMat 12 := by
      unfold actionA
      rw [step109wc57s4_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 480 * (codeMat 95 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 94) (codeMat 244) (codeMat 384) = codeMat 2 := by
      unfold actionA
      rw [step109wc57s4_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 384 * (codeMat 95 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 94) (codeMat 244) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc57s4_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 256 * (codeMat 95 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact

theorem step109wc57s4Dispatch :
    QuotientRankAtLeast (o57SourceU_wc ⟨4, by omega⟩) 12 := by
  have hP : Invertible (codeMat 94 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 244 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 94) (codeMat 244) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 94) (codeMat 244) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc57s4_contain hAct


private theorem step109wc57s5_QtInv :
    (codeMat 299 : Mat3).transpose⁻¹ = (codeMat 318 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 299 : Mat3).transpose * (codeMat 318 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc57s5_contain :
    (o57SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 161) (codeMat 299) o16W_wc := by
  change spanCodes [272, 132, 84, 52, 12, 2, 1] ≤ actionW (codeMat 161) (codeMat 299) o16W_wc
  apply step109wc57_spanCodes_le_of_gens [272, 132, 84, 52, 12, 2, 1]
    (actionW (codeMat 161) (codeMat 299) o16W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 112 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 112 (by decide)
    have hact : actionA (codeMat 161) (codeMat 299) (codeMat 112) = codeMat 272 := by
      unfold actionA
      rw [step109wc57s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 112 * (codeMat 318 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 14 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 14 (by decide)
    have hact : actionA (codeMat 161) (codeMat 299) (codeMat 14) = codeMat 132 := by
      unfold actionA
      rw [step109wc57s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 14 * (codeMat 318 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 94 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 94 (by decide)
    have hact : actionA (codeMat 161) (codeMat 299) (codeMat 94) = codeMat 84 := by
      unfold actionA
      rw [step109wc57s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 94 * (codeMat 318 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 454 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 454 (by decide)
    have hact : actionA (codeMat 161) (codeMat 299) (codeMat 454) = codeMat 52 := by
      unfold actionA
      rw [step109wc57s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 454 * (codeMat 318 : Mat3).transpose = codeMat 52
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 198 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 198 (by decide)
    have hact : actionA (codeMat 161) (codeMat 299) (codeMat 198) = codeMat 12 := by
      unfold actionA
      rw [step109wc57s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 198 * (codeMat 318 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 299) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step109wc57s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 318 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 161) (codeMat 299) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step109wc57s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 3 * (codeMat 318 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact

theorem step109wc57s5Dispatch :
    QuotientRankAtLeast (o57SourceU_wc ⟨5, by omega⟩) 12 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 299 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 299) o16W_wc) 12 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 299) hP hQ o16W_wc 12
      step109_orbit16_lb12_wc
  exact quotientRankAtLeast_mono step109wc57s5_contain hAct


private theorem step109wc57s6_QtInv :
    (codeMat 98 : Mat3).transpose⁻¹ = (codeMat 140 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 98 : Mat3).transpose * (codeMat 140 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc57s6_contain :
    (o57SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 161) (codeMat 98) flatW_9 := by
  change spanCodes [272, 128, 96, 8, 4, 2, 1] ≤ actionW (codeMat 161) (codeMat 98) flatW_9
  apply step109wc57_spanCodes_le_of_gens [272, 128, 96, 8, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 98) flatW_9)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 80 ∈ flatW_9 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 8, 4, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 161) (codeMat 98) (codeMat 80) = codeMat 272 := by
      unfold actionA
      rw [step109wc57s6_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 80 * (codeMat 140 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ flatW_9 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 98) (codeMat 8) = codeMat 128 := by
      unfold actionA
      rw [step109wc57s6_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 140 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 160 ∈ flatW_9 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 8, 4, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 98) (codeMat 160) = codeMat 96 := by
      unfold actionA
      rw [step109wc57s6_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * (codeMat 140 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ flatW_9 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 98) (codeMat 256) = codeMat 8 := by
      unfold actionA
      rw [step109wc57s6_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 140 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ flatW_9 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 98) (codeMat 2) = codeMat 4 := by
      unfold actionA
      rw [step109wc57s6_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 140 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ flatW_9 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 98) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step109wc57s6_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 140 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 4 ∈ flatW_9 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 161) (codeMat 98) (codeMat 4) = codeMat 1 := by
      unfold actionA
      rw [step109wc57s6_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 4 * (codeMat 140 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc57_codeMat_mem_actionW_of_witness hw hact

theorem step109wc57s6Dispatch :
    QuotientRankAtLeast (o57SourceU_wc ⟨6, by omega⟩) 9 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 98) flatW_9) 9 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 98) hP hQ flatW_9 9
      flatSeed_9
  exact quotientRankAtLeast_mono step109wc57s6_contain hAct

theorem step109wc57_all_dispatch (i : Fin 7) :
    QuotientRankAtLeast (o57SourceU_wc i) (o57SourceLb_wc i) := by
  fin_cases i
  · exact step109wc57s0Dispatch
  · exact step109wc57s1Dispatch
  · exact step109wc57s2Dispatch
  · exact step109wc57s3Dispatch
  · exact step109wc57s4Dispatch
  · exact step109wc57s5Dispatch
  · exact step109wc57s6Dispatch

theorem step109_orbit57_lb14_wc : QuotientRankAtLeast o57W_wc 14 :=
  o57Lb14_wc step109wc57_all_dispatch

end QiushiMatmul
