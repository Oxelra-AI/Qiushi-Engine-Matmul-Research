import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit127Consumer
import QiushiWcOrbit57Dispatch
import QiushiWcOrbit45Dispatch
import QiushiOrbit14FP
import QiushiOrbit10FP
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc127_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc127_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc127s0_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc127s0_contain :
    (o127SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 161) (codeMat 266) o57W_wc := by
  change spanCodes [272, 132, 96, 12, 2, 1] ≤ actionW (codeMat 161) (codeMat 266) o57W_wc
  apply step109wc127_spanCodes_le_of_gens [272, 132, 96, 12, 2, 1]
    (actionW (codeMat 161) (codeMat 266) o57W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 96 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 96 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 96) = codeMat 272 := by
      unfold actionA
      rw [step109wc127s0_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 96 * (codeMat 266 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 12 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 12) = codeMat 132 := by
      unfold actionA
      rw [step109wc127s0_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 12 * (codeMat 266 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 272 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 272 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 272) = codeMat 96 := by
      unfold actionA
      rw [step109wc127s0_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 272 * (codeMat 266 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 132 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 132 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 132) = codeMat 12 := by
      unfold actionA
      rw [step109wc127s0_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 132 * (codeMat 266 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step109wc127s0_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc127s0_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact

theorem step109wc127s0Dispatch :
    QuotientRankAtLeast (o127SourceU_wc ⟨0, by omega⟩) 14 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 266) o57W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 266) hP hQ o57W_wc 14
      step109_orbit57_lb14_wc
  exact quotientRankAtLeast_mono step109wc127s0_contain hAct


private theorem step109wc127s1_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = (codeMat 267 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * (codeMat 267 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc127s1_contain :
    (o127SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 169) (codeMat 282) o57W_wc := by
  change spanCodes [272, 164, 96, 12, 2, 1] ≤ actionW (codeMat 169) (codeMat 282) o57W_wc
  apply step109wc127_spanCodes_le_of_gens [272, 164, 96, 12, 2, 1]
    (actionW (codeMat 169) (codeMat 282) o57W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 228 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 228 (by decide)
    have hact : actionA (codeMat 169) (codeMat 282) (codeMat 228) = codeMat 272 := by
      unfold actionA
      rw [step109wc127s1_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 228 * (codeMat 267 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 287 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 287 (by decide)
    have hact : actionA (codeMat 169) (codeMat 282) (codeMat 287) = codeMat 164 := by
      unfold actionA
      rw [step109wc127s1_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 287 * (codeMat 267 : Mat3).transpose = codeMat 164
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 274 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 274 (by decide)
    have hact : actionA (codeMat 169) (codeMat 282) (codeMat 274) = codeMat 96 := by
      unfold actionA
      rw [step109wc127s1_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 274 * (codeMat 267 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 132 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 132 (by decide)
    have hact : actionA (codeMat 169) (codeMat 282) (codeMat 132) = codeMat 12 := by
      unfold actionA
      rw [step109wc127s1_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 132 * (codeMat 267 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 169) (codeMat 282) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc127s1_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 3 * (codeMat 267 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 169) (codeMat 282) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc127s1_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 2 * (codeMat 267 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact

theorem step109wc127s1Dispatch :
    QuotientRankAtLeast (o127SourceU_wc ⟨1, by omega⟩) 14 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 282) o57W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 282) hP hQ o57W_wc 14
      step109_orbit57_lb14_wc
  exact quotientRankAtLeast_mono step109wc127s1_contain hAct


private theorem step109wc127s2_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc127s2_contain :
    (o127SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 161) (codeMat 273) o45W_wc := by
  change spanCodes [272, 64, 32, 12, 2, 1] ≤ actionW (codeMat 161) (codeMat 273) o45W_wc
  apply step109wc127_spanCodes_le_of_gens [272, 64, 32, 12, 2, 1]
    (actionW (codeMat 161) (codeMat 273) o45W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 160 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 160) = codeMat 272 := by
      unfold actionA
      rw [step109wc127s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * (codeMat 273 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 8) = codeMat 64 := by
      unfold actionA
      rw [step109wc127s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 256 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 256) = codeMat 32 := by
      unfold actionA
      rw [step109wc127s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 273 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 68 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 68 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 68) = codeMat 12 := by
      unfold actionA
      rw [step109wc127s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 68 * (codeMat 273 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc127s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc127s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact

theorem step109wc127s2Dispatch :
    QuotientRankAtLeast (o127SourceU_wc ⟨2, by omega⟩) 13 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 273) o45W_wc) 13 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 273) hP hQ o45W_wc 13
      step109_orbit45_lb13_wc
  exact quotientRankAtLeast_mono step109wc127s2_contain hAct


private theorem step109wc127s3_QtInv :
    (codeMat 500 : Mat3).transpose⁻¹ = (codeMat 94 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 500 : Mat3).transpose * (codeMat 94 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc127s3_contain :
    (o127SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 93) (codeMat 500) orbit14W := by
  change spanCodes [272, 148, 84, 52, 12, 2, 1] ≤ actionW (codeMat 93) (codeMat 500) orbit14W
  apply step109wc127_spanCodes_le_of_gens [272, 148, 84, 52, 12, 2, 1]
    (actionW (codeMat 93) (codeMat 500) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 119 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 119 (by decide)
    have hact : actionA (codeMat 93) (codeMat 500) (codeMat 119) = codeMat 272 := by
      unfold actionA
      rw [step109wc127s3_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 119 * (codeMat 94 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 502 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 502 (by decide)
    have hact : actionA (codeMat 93) (codeMat 500) (codeMat 502) = codeMat 148 := by
      unfold actionA
      rw [step109wc127s3_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 502 * (codeMat 94 : Mat3).transpose = codeMat 148
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 372 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 372 (by decide)
    have hact : actionA (codeMat 93) (codeMat 500) (codeMat 372) = codeMat 84 := by
      unfold actionA
      rw [step109wc127s3_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 372 * (codeMat 94 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 392 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 392 (by decide)
    have hact : actionA (codeMat 93) (codeMat 500) (codeMat 392) = codeMat 52 := by
      unfold actionA
      rw [step109wc127s3_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 392 * (codeMat 94 : Mat3).transpose = codeMat 52
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 224 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 224 (by decide)
    have hact : actionA (codeMat 93) (codeMat 500) (codeMat 224) = codeMat 12 := by
      unfold actionA
      rw [step109wc127s3_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 224 * (codeMat 94 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 93) (codeMat 500) (codeMat 384) = codeMat 2 := by
      unfold actionA
      rw [step109wc127s3_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 384 * (codeMat 94 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 93) (codeMat 500) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc127s3_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 256 * (codeMat 94 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact

theorem step109wc127s3Dispatch :
    QuotientRankAtLeast (o127SourceU_wc ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 93 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 500 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 93) (codeMat 500) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 93) (codeMat 500) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc127s3_contain hAct


private theorem step109wc127s4_QtInv :
    (codeMat 372 : Mat3).transpose⁻¹ = (codeMat 93 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 372 : Mat3).transpose * (codeMat 93 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc127s4_contain :
    (o127SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 92) (codeMat 372) orbit14W := by
  change spanCodes [272, 128, 80, 48, 12, 2, 1] ≤ actionW (codeMat 92) (codeMat 372) orbit14W
  apply step109wc127_spanCodes_le_of_gens [272, 128, 80, 48, 12, 2, 1]
    (actionW (codeMat 92) (codeMat 372) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 151 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 151 (by decide)
    have hact : actionA (codeMat 92) (codeMat 372) (codeMat 151) = codeMat 272 := by
      unfold actionA
      rw [step109wc127s4_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 151 * (codeMat 93 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 92) (codeMat 372) (codeMat 2) = codeMat 128 := by
      unfold actionA
      rw [step109wc127s4_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 2 * (codeMat 93 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 148 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 148 (by decide)
    have hact : actionA (codeMat 92) (codeMat 372) (codeMat 148) = codeMat 80 := by
      unfold actionA
      rw [step109wc127s4_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 148 * (codeMat 93 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 92) (codeMat 372) (codeMat 360) = codeMat 48 := by
      unfold actionA
      rw [step109wc127s4_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 360 * (codeMat 93 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 224 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 224 (by decide)
    have hact : actionA (codeMat 92) (codeMat 372) (codeMat 224) = codeMat 12 := by
      unfold actionA
      rw [step109wc127s4_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 224 * (codeMat 93 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 92) (codeMat 372) (codeMat 128) = codeMat 2 := by
      unfold actionA
      rw [step109wc127s4_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 128 * (codeMat 93 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 92) (codeMat 372) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc127s4_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 256 * (codeMat 93 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact

theorem step109wc127s4Dispatch :
    QuotientRankAtLeast (o127SourceU_wc ⟨4, by omega⟩) 12 := by
  have hP : Invertible (codeMat 92 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 372 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 92) (codeMat 372) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 92) (codeMat 372) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc127s4_contain hAct


private theorem step109wc127s5_QtInv :
    (codeMat 314 : Mat3).transpose⁻¹ = (codeMat 271 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 314 : Mat3).transpose * (codeMat 271 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc127s5_contain :
    (o127SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 142) (codeMat 314) orbit10W := by
  change spanCodes [272, 144, 68, 36, 12, 2, 1] ≤ actionW (codeMat 142) (codeMat 314) orbit10W
  apply step109wc127_spanCodes_le_of_gens [272, 144, 68, 36, 12, 2, 1]
    (actionW (codeMat 142) (codeMat 314) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 326 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 326 (by decide)
    have hact : actionA (codeMat 142) (codeMat 314) (codeMat 326) = codeMat 272 := by
      unfold actionA
      rw [step109wc127s5_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 326 * (codeMat 271 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 3 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 142) (codeMat 314) (codeMat 3) = codeMat 144 := by
      unfold actionA
      rw [step109wc127s5_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 3 * (codeMat 271 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 178 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 178 (by decide)
    have hact : actionA (codeMat 142) (codeMat 314) (codeMat 178) = codeMat 68 := by
      unfold actionA
      rw [step109wc127s5_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 178 * (codeMat 271 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 432 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide)
    have hact : actionA (codeMat 142) (codeMat 314) (codeMat 432) = codeMat 36 := by
      unfold actionA
      rw [step109wc127s5_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 432 * (codeMat 271 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 176 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 176 (by decide)
    have hact : actionA (codeMat 142) (codeMat 314) (codeMat 176) = codeMat 12 := by
      unfold actionA
      rw [step109wc127s5_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 176 * (codeMat 271 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 142) (codeMat 314) (codeMat 24) = codeMat 2 := by
      unfold actionA
      rw [step109wc127s5_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 24 * (codeMat 271 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 142) (codeMat 314) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc127s5_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 16 * (codeMat 271 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact

theorem step109wc127s5Dispatch :
    QuotientRankAtLeast (o127SourceU_wc ⟨5, by omega⟩) 12 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 314 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 314) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 314) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc127s5_contain hAct


private theorem step109wc127s6_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc127s6_contain :
    (o127SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 273) (codeMat 273) flatW_7 := by
  change spanCodes [256, 96, 16, 8, 4, 2, 1] ≤ actionW (codeMat 273) (codeMat 273) flatW_7
  apply step109wc127_spanCodes_le_of_gens [256, 96, 16, 8, 4, 2, 1]
    (actionW (codeMat 273) (codeMat 273) flatW_7)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step109wc127s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 273 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 96 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 96 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 96) = codeMat 96 := by
      unfold actionA
      rw [step109wc127s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 96 * (codeMat 273 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 16 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 16) = codeMat 16 := by
      unfold actionA
      rw [step109wc127s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 16 * (codeMat 273 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc127s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 4 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 4) = codeMat 4 := by
      unfold actionA
      rw [step109wc127s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 4 * (codeMat 273 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc127s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc127s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc127_codeMat_mem_actionW_of_witness hw hact

theorem step109wc127s6Dispatch :
    QuotientRankAtLeast (o127SourceU_wc ⟨6, by omega⟩) 9 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 273) flatW_7) 9 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 273) hP hQ flatW_7 9
      flatSeed_7
  exact quotientRankAtLeast_mono step109wc127s6_contain hAct

theorem step109wc127_all_dispatch (i : Fin 7) :
    QuotientRankAtLeast (o127SourceU_wc i) (o127SourceLb_wc i) := by
  fin_cases i
  · exact step109wc127s0Dispatch
  · exact step109wc127s1Dispatch
  · exact step109wc127s2Dispatch
  · exact step109wc127s3Dispatch
  · exact step109wc127s4Dispatch
  · exact step109wc127s5Dispatch
  · exact step109wc127s6Dispatch

theorem step109_orbit127_lb15_wc : QuotientRankAtLeast o127W_wc 15 :=
  o127Lb15_wc step109wc127_all_dispatch

end QiushiMatmul
