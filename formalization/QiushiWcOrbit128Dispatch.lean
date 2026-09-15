import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit128Consumer
import QiushiStep99Orbit55Dispatch
import QiushiOrbit14FP
import QiushiOrbit10FP
import QiushiWcOrbit25Dispatch
import QiushiOrbit5FP
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc128_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc128_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc128s0_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc128s0_contain :
    (o128SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 169) (codeMat 266) o55W := by
  change spanCodes [260, 132, 96, 12, 2, 1] ≤ actionW (codeMat 169) (codeMat 266) o55W
  apply step109wc128_spanCodes_le_of_gens [260, 132, 96, 12, 2, 1]
    (actionW (codeMat 169) (codeMat 266) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 32 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 169) (codeMat 266) (codeMat 32) = codeMat 260 := by
      unfold actionA
      rw [step109wc128s0_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 32 * (codeMat 266 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 13 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 13 (by decide)
    have hact : actionA (codeMat 169) (codeMat 266) (codeMat 13) = codeMat 132 := by
      unfold actionA
      rw [step109wc128s0_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 13 * (codeMat 266 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 274 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 274 (by decide)
    have hact : actionA (codeMat 169) (codeMat 266) (codeMat 274) = codeMat 96 := by
      unfold actionA
      rw [step109wc128s0_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 274 * (codeMat 266 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 132 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 132 (by decide)
    have hact : actionA (codeMat 169) (codeMat 266) (codeMat 132) = codeMat 12 := by
      unfold actionA
      rw [step109wc128s0_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 132 * (codeMat 266 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 266) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step109wc128s0_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 169) (codeMat 266) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc128s0_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact

theorem step109wc128s0Dispatch :
    QuotientRankAtLeast (o128SourceU_wc ⟨0, by omega⟩) 14 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 266) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 266) hP hQ o55W 14
      step99_orbit55_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc128s0_contain hAct


private theorem step109wc128s1_QtInv :
    (codeMat 314 : Mat3).transpose⁻¹ = (codeMat 271 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 314 : Mat3).transpose * (codeMat 271 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc128s1_contain :
    (o128SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 233) (codeMat 314) o55W := by
  change spanCodes [292, 164, 96, 12, 2, 1] ≤ actionW (codeMat 233) (codeMat 314) o55W
  apply step109wc128_spanCodes_le_of_gens [292, 164, 96, 12, 2, 1]
    (actionW (codeMat 233) (codeMat 314) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 438 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 438 (by decide)
    have hact : actionA (codeMat 233) (codeMat 314) (codeMat 438) = codeMat 292 := by
      unfold actionA
      rw [step109wc128s1_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 438 * (codeMat 271 : Mat3).transpose = codeMat 292
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 411 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 411 (by decide)
    have hact : actionA (codeMat 233) (codeMat 314) (codeMat 411) = codeMat 164 := by
      unfold actionA
      rw [step109wc128s1_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 411 * (codeMat 271 : Mat3).transpose = codeMat 164
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 404 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 404 (by decide)
    have hact : actionA (codeMat 233) (codeMat 314) (codeMat 404) = codeMat 96 := by
      unfold actionA
      rw [step109wc128s1_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 404 * (codeMat 271 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 132 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 132 (by decide)
    have hact : actionA (codeMat 233) (codeMat 314) (codeMat 132) = codeMat 12 := by
      unfold actionA
      rw [step109wc128s1_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 132 * (codeMat 271 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 233) (codeMat 314) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc128s1_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 3 * (codeMat 271 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 233) (codeMat 314) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc128s1_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 2 * (codeMat 271 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact

theorem step109wc128s1Dispatch :
    QuotientRankAtLeast (o128SourceU_wc ⟨1, by omega⟩) 14 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 314 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 314) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 314) hP hQ o55W 14
      step99_orbit55_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc128s1_contain hAct


private theorem step109wc128s2_QtInv :
    (codeMat 281 : Mat3).transpose⁻¹ = (codeMat 281 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 281 : Mat3).transpose * (codeMat 281 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc128s2_contain :
    (o128SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 273) (codeMat 281) orbit14W := by
  change spanCodes [256, 128, 96, 20, 12, 2, 1] ≤ actionW (codeMat 273) (codeMat 281) orbit14W
  apply step109wc128_spanCodes_le_of_gens [256, 128, 96, 20, 12, 2, 1]
    (actionW (codeMat 273) (codeMat 281) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 281) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step109wc128s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 281 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 273) (codeMat 281) (codeMat 128) = codeMat 128 := by
      unfold actionA
      rw [step109wc128s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 128 * (codeMat 281 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 224 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 224 (by decide)
    have hact : actionA (codeMat 273) (codeMat 281) (codeMat 224) = codeMat 96 := by
      unfold actionA
      rw [step109wc128s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 224 * (codeMat 281 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 20 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 281) (codeMat 20) = codeMat 20 := by
      unfold actionA
      rw [step109wc128s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * (codeMat 281 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 28 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 28 (by decide)
    have hact : actionA (codeMat 273) (codeMat 281) (codeMat 28) = codeMat 12 := by
      unfold actionA
      rw [step109wc128s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 28 * (codeMat 281 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 281) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc128s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 281 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 273) (codeMat 281) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step109wc128s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 3 * (codeMat 281 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact

theorem step109wc128s2Dispatch :
    QuotientRankAtLeast (o128SourceU_wc ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 281) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 281) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc128s2_contain hAct


private theorem step109wc128s3_QtInv :
    (codeMat 500 : Mat3).transpose⁻¹ = (codeMat 94 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 500 : Mat3).transpose * (codeMat 94 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc128s3_contain :
    (o128SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 92) (codeMat 500) orbit14W := by
  change spanCodes [276, 148, 84, 52, 12, 2, 1] ≤ actionW (codeMat 92) (codeMat 500) orbit14W
  apply step109wc128_spanCodes_le_of_gens [276, 148, 84, 52, 12, 2, 1]
    (actionW (codeMat 92) (codeMat 500) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 119 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 119 (by decide)
    have hact : actionA (codeMat 92) (codeMat 500) (codeMat 119) = codeMat 276 := by
      unfold actionA
      rw [step109wc128s3_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 119 * (codeMat 94 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 118 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 118 (by decide)
    have hact : actionA (codeMat 92) (codeMat 500) (codeMat 118) = codeMat 148 := by
      unfold actionA
      rw [step109wc128s3_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 118 * (codeMat 94 : Mat3).transpose = codeMat 148
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 116 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 116 (by decide)
    have hact : actionA (codeMat 92) (codeMat 500) (codeMat 116) = codeMat 84 := by
      unfold actionA
      rw [step109wc128s3_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 116 * (codeMat 94 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 392 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 392 (by decide)
    have hact : actionA (codeMat 92) (codeMat 500) (codeMat 392) = codeMat 52 := by
      unfold actionA
      rw [step109wc128s3_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 392 * (codeMat 94 : Mat3).transpose = codeMat 52
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 224 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 224 (by decide)
    have hact : actionA (codeMat 92) (codeMat 500) (codeMat 224) = codeMat 12 := by
      unfold actionA
      rw [step109wc128s3_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 224 * (codeMat 94 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 92) (codeMat 500) (codeMat 384) = codeMat 2 := by
      unfold actionA
      rw [step109wc128s3_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 384 * (codeMat 94 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 92) (codeMat 500) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc128s3_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 256 * (codeMat 94 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact

theorem step109wc128s3Dispatch :
    QuotientRankAtLeast (o128SourceU_wc ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 92 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 500 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 92) (codeMat 500) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 92) (codeMat 500) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc128s3_contain hAct


private theorem step109wc128s4_QtInv :
    (codeMat 116 : Mat3).transpose⁻¹ = (codeMat 92 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 116 : Mat3).transpose * (codeMat 92 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc128s4_contain :
    (o128SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 84) (codeMat 116) orbit14W := by
  change spanCodes [256, 128, 80, 48, 12, 2, 1] ≤ actionW (codeMat 84) (codeMat 116) orbit14W
  apply step109wc128_spanCodes_le_of_gens [256, 128, 80, 48, 12, 2, 1]
    (actionW (codeMat 84) (codeMat 116) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 84) (codeMat 116) (codeMat 3) = codeMat 256 := by
      unfold actionA
      rw [step109wc128s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 3 * (codeMat 92 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 116) (codeMat 2) = codeMat 128 := by
      unfold actionA
      rw [step109wc128s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 92 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 20 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 20 (by decide)
    have hact : actionA (codeMat 84) (codeMat 116) (codeMat 20) = codeMat 80 := by
      unfold actionA
      rw [step109wc128s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 20 * (codeMat 92 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 116) (codeMat 8) = codeMat 48 := by
      unfold actionA
      rw [step109wc128s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 92 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 224 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 224 (by decide)
    have hact : actionA (codeMat 84) (codeMat 116) (codeMat 224) = codeMat 12 := by
      unfold actionA
      rw [step109wc128s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 224 * (codeMat 92 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 116) (codeMat 128) = codeMat 2 := by
      unfold actionA
      rw [step109wc128s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 92 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 116) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc128s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 92 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact

theorem step109wc128s4Dispatch :
    QuotientRankAtLeast (o128SourceU_wc ⟨4, by omega⟩) 12 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 116 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 116) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 116) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc128s4_contain hAct


private theorem step109wc128s5_QtInv :
    (codeMat 270 : Mat3).transpose⁻¹ = (codeMat 298 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 270 : Mat3).transpose * (codeMat 298 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc128s5_contain :
    (o128SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 305) (codeMat 270) orbit14W := by
  change spanCodes [272, 144, 64, 32, 12, 2, 1] ≤ actionW (codeMat 305) (codeMat 270) orbit14W
  apply step109wc128_spanCodes_le_of_gens [272, 144, 64, 32, 12, 2, 1]
    (actionW (codeMat 305) (codeMat 270) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 264 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 264 (by decide)
    have hact : actionA (codeMat 305) (codeMat 270) (codeMat 264) = codeMat 272 := by
      unfold actionA
      rw [step109wc128s5_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 264 * (codeMat 298 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 305) (codeMat 270) (codeMat 8) = codeMat 144 := by
      unfold actionA
      rw [step109wc128s5_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 8 * (codeMat 298 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 305) (codeMat 270) (codeMat 128) = codeMat 64 := by
      unfold actionA
      rw [step109wc128s5_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 128 * (codeMat 298 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 305) (codeMat 270) (codeMat 360) = codeMat 32 := by
      unfold actionA
      rw [step109wc128s5_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 360 * (codeMat 298 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 149 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 149 (by decide)
    have hact : actionA (codeMat 305) (codeMat 270) (codeMat 149) = codeMat 12 := by
      unfold actionA
      rw [step109wc128s5_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 149 * (codeMat 298 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 305) (codeMat 270) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step109wc128s5_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 1 * (codeMat 298 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 305) (codeMat 270) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc128s5_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 2 * (codeMat 298 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact

theorem step109wc128s5Dispatch :
    QuotientRankAtLeast (o128SourceU_wc ⟨5, by omega⟩) 12 := by
  have hP : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 270 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 305) (codeMat 270) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 305) (codeMat 270) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc128s5_contain hAct


private theorem step109wc128s6_QtInv :
    (codeMat 271 : Mat3).transpose⁻¹ = (codeMat 314 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 271 : Mat3).transpose * (codeMat 314 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc128s6_contain :
    (o128SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 273) (codeMat 271) orbit14W := by
  change spanCodes [288, 160, 96, 16, 12, 2, 1] ≤ actionW (codeMat 273) (codeMat 271) orbit14W
  apply step109wc128_spanCodes_le_of_gens [288, 160, 96, 16, 12, 2, 1]
    (actionW (codeMat 273) (codeMat 271) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 273) (codeMat 271) (codeMat 360) = codeMat 288 := by
      unfold actionA
      rw [step109wc128s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 360 * (codeMat 314 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 104 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 104 (by decide)
    have hact : actionA (codeMat 273) (codeMat 271) (codeMat 104) = codeMat 160 := by
      unfold actionA
      rw [step109wc128s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 104 * (codeMat 314 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 232 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 232 (by decide)
    have hact : actionA (codeMat 273) (codeMat 271) (codeMat 232) = codeMat 96 := by
      unfold actionA
      rw [step109wc128s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 232 * (codeMat 314 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 271) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step109wc128s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 314 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 29 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 29 (by decide)
    have hact : actionA (codeMat 273) (codeMat 271) (codeMat 29) = codeMat 12 := by
      unfold actionA
      rw [step109wc128s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 29 * (codeMat 314 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 271) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step109wc128s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 314 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 273) (codeMat 271) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step109wc128s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 3 * (codeMat 314 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact

theorem step109wc128s6Dispatch :
    QuotientRankAtLeast (o128SourceU_wc ⟨6, by omega⟩) 12 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 271 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 271) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 271) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc128s6_contain hAct


private theorem step109wc128s7_QtInv :
    (codeMat 314 : Mat3).transpose⁻¹ = (codeMat 271 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 314 : Mat3).transpose * (codeMat 271 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc128s7_contain :
    (o128SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 142) (codeMat 314) orbit10W := by
  change spanCodes [272, 144, 68, 36, 12, 2, 1] ≤ actionW (codeMat 142) (codeMat 314) orbit10W
  apply step109wc128_spanCodes_le_of_gens [272, 144, 68, 36, 12, 2, 1]
    (actionW (codeMat 142) (codeMat 314) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 326 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 326 (by decide)
    have hact : actionA (codeMat 142) (codeMat 314) (codeMat 326) = codeMat 272 := by
      unfold actionA
      rw [step109wc128s7_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 326 * (codeMat 271 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 3 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 142) (codeMat 314) (codeMat 3) = codeMat 144 := by
      unfold actionA
      rw [step109wc128s7_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 3 * (codeMat 271 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 178 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 178 (by decide)
    have hact : actionA (codeMat 142) (codeMat 314) (codeMat 178) = codeMat 68 := by
      unfold actionA
      rw [step109wc128s7_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 178 * (codeMat 271 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 432 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide)
    have hact : actionA (codeMat 142) (codeMat 314) (codeMat 432) = codeMat 36 := by
      unfold actionA
      rw [step109wc128s7_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 432 * (codeMat 271 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 176 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 176 (by decide)
    have hact : actionA (codeMat 142) (codeMat 314) (codeMat 176) = codeMat 12 := by
      unfold actionA
      rw [step109wc128s7_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 176 * (codeMat 271 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 142) (codeMat 314) (codeMat 24) = codeMat 2 := by
      unfold actionA
      rw [step109wc128s7_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 24 * (codeMat 271 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 142) (codeMat 314) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc128s7_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 16 * (codeMat 271 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact

theorem step109wc128s7Dispatch :
    QuotientRankAtLeast (o128SourceU_wc ⟨7, by omega⟩) 12 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 314 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 314) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 314) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc128s7_contain hAct


private theorem step109wc128s8_QtInv :
    (codeMat 286 : Mat3).transpose⁻¹ = (codeMat 303 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 286 : Mat3).transpose * (codeMat 303 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc128s8_contain :
    (o128SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 305) (codeMat 286) orbit14W := by
  change spanCodes [276, 148, 64, 32, 12, 2, 1] ≤ actionW (codeMat 305) (codeMat 286) orbit14W
  apply step109wc128_spanCodes_le_of_gens [276, 148, 64, 32, 12, 2, 1]
    (actionW (codeMat 305) (codeMat 286) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 413 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 413 (by decide)
    have hact : actionA (codeMat 305) (codeMat 286) (codeMat 413) = codeMat 276 := by
      unfold actionA
      rw [step109wc128s8_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 413 * (codeMat 303 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 29 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 29 (by decide)
    have hact : actionA (codeMat 305) (codeMat 286) (codeMat 29) = codeMat 148 := by
      unfold actionA
      rw [step109wc128s8_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 29 * (codeMat 303 : Mat3).transpose = codeMat 148
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 305) (codeMat 286) (codeMat 128) = codeMat 64 := by
      unfold actionA
      rw [step109wc128s8_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 128 * (codeMat 303 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 305) (codeMat 286) (codeMat 360) = codeMat 32 := by
      unfold actionA
      rw [step109wc128s8_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 360 * (codeMat 303 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 149 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 149 (by decide)
    have hact : actionA (codeMat 305) (codeMat 286) (codeMat 149) = codeMat 12 := by
      unfold actionA
      rw [step109wc128s8_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 149 * (codeMat 303 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 305) (codeMat 286) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc128s8_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 3 * (codeMat 303 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 305) (codeMat 286) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc128s8_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 2 * (codeMat 303 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact

theorem step109wc128s8Dispatch :
    QuotientRankAtLeast (o128SourceU_wc ⟨8, by omega⟩) 12 := by
  have hP : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 286 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 305) (codeMat 286) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 305) (codeMat 286) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc128s8_contain hAct


private theorem step109wc128s9_QtInv :
    (codeMat 177 : Mat3).transpose⁻¹ = (codeMat 417 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 177 : Mat3).transpose * (codeMat 417 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc128s9_contain :
    (o128SourceU_wc ⟨9, by omega⟩) ≤ actionW (codeMat 273) (codeMat 177) o25W_wc := by
  change spanCodes [384, 96, 8, 4, 2, 1] ≤ actionW (codeMat 273) (codeMat 177) o25W_wc
  apply step109wc128_spanCodes_le_of_gens [384, 96, 8, 4, 2, 1]
    (actionW (codeMat 273) (codeMat 177) o25W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 256 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 177) (codeMat 256) = codeMat 384 := by
      unfold actionA
      rw [step109wc128s9_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 417 : Mat3).transpose = codeMat 384
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 80 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 273) (codeMat 177) (codeMat 80) = codeMat 96 := by
      unfold actionA
      rw [step109wc128s9_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 80 * (codeMat 417 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 177) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc128s9_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 417 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 177) (codeMat 2) = codeMat 4 := by
      unfold actionA
      rw [step109wc128s9_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 417 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 6 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 6 (by decide)
    have hact : actionA (codeMat 273) (codeMat 177) (codeMat 6) = codeMat 2 := by
      unfold actionA
      rw [step109wc128s9_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 6 * (codeMat 417 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o25W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 177) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc128s9_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 417 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact

theorem step109wc128s9Dispatch :
    QuotientRankAtLeast (o128SourceU_wc ⟨9, by omega⟩) 11 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 177) o25W_wc) 11 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 177) hP hQ o25W_wc 11
      step109_orbit25_lb11_wc
  exact quotientRankAtLeast_mono step109wc128s9_contain hAct


private theorem step109wc128s10_QtInv :
    (codeMat 394 : Mat3).transpose⁻¹ = (codeMat 330 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 394 : Mat3).transpose * (codeMat 330 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc128s10_contain :
    (o128SourceU_wc ⟨10, by omega⟩) ≤ actionW (codeMat 273) (codeMat 394) orbit5W := by
  change spanCodes [384, 80, 48, 8, 4, 2, 1] ≤ actionW (codeMat 273) (codeMat 394) orbit5W
  apply step109wc128_spanCodes_le_of_gens [384, 80, 48, 8, 4, 2, 1]
    (actionW (codeMat 273) (codeMat 394) orbit5W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 64 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 64 (by decide)
    have hact : actionA (codeMat 273) (codeMat 394) (codeMat 64) = codeMat 384 := by
      unfold actionA
      rw [step109wc128s10_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 64 * (codeMat 330 : Mat3).transpose = codeMat 384
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 168 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 168 (by decide)
    have hact : actionA (codeMat 273) (codeMat 394) (codeMat 168) = codeMat 80 := by
      unfold actionA
      rw [step109wc128s10_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 168 * (codeMat 330 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 394) (codeMat 8) = codeMat 48 := by
      unfold actionA
      rw [step109wc128s10_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 330 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 16 (by decide)
    have hact : actionA (codeMat 273) (codeMat 394) (codeMat 16) = codeMat 8 := by
      unfold actionA
      rw [step109wc128s10_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 16 * (codeMat 330 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 4 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 4 (by decide)
    have hact : actionA (codeMat 273) (codeMat 394) (codeMat 4) = codeMat 4 := by
      unfold actionA
      rw [step109wc128s10_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 4 * (codeMat 330 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 5 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 5 (by decide)
    have hact : actionA (codeMat 273) (codeMat 394) (codeMat 5) = codeMat 2 := by
      unfold actionA
      rw [step109wc128s10_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 5 * (codeMat 330 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit5W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 16, 64, 160] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 394) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc128s10_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 330 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact

theorem step109wc128s10Dispatch :
    QuotientRankAtLeast (o128SourceU_wc ⟨10, by omega⟩) 9 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 394 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 394) orbit5W) 9 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 394) hP hQ orbit5W 9
      orbit5_lb9
  exact quotientRankAtLeast_mono step109wc128s10_contain hAct


private theorem step109wc128s11_QtInv :
    (codeMat 394 : Mat3).transpose⁻¹ = (codeMat 330 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 394 : Mat3).transpose * (codeMat 330 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc128s11_contain :
    (o128SourceU_wc ⟨11, by omega⟩) ≤ actionW (codeMat 266) (codeMat 394) flatW_1 := by
  change spanCodes [384, 64, 32, 16, 8, 4, 2, 1] ≤ actionW (codeMat 266) (codeMat 394) flatW_1
  apply step109wc128_spanCodes_le_of_gens [384, 64, 32, 16, 8, 4, 2, 1]
    (actionW (codeMat 266) (codeMat 394) flatW_1)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 64 ∈ flatW_1 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 64, 32, 16, 8, 4, 2, 1] 64 (by decide)
    have hact : actionA (codeMat 266) (codeMat 394) (codeMat 64) = codeMat 384 := by
      unfold actionA
      rw [step109wc128s11_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 64 * (codeMat 330 : Mat3).transpose = codeMat 384
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 128 ∈ flatW_1 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 64, 32, 16, 8, 4, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 266) (codeMat 394) (codeMat 128) = codeMat 64 := by
      unfold actionA
      rw [step109wc128s11_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 128 * (codeMat 330 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 4 ∈ flatW_1 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 64, 32, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 266) (codeMat 394) (codeMat 4) = codeMat 32 := by
      unfold actionA
      rw [step109wc128s11_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 4 * (codeMat 330 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 5 ∈ flatW_1 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 64, 32, 16, 8, 4, 2, 1] 5 (by decide)
    have hact : actionA (codeMat 266) (codeMat 394) (codeMat 5) = codeMat 16 := by
      unfold actionA
      rw [step109wc128s11_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 5 * (codeMat 330 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ flatW_1 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 64, 32, 16, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 394) (codeMat 2) = codeMat 8 := by
      unfold actionA
      rw [step109wc128s11_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 330 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ flatW_1 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 64, 32, 16, 8, 4, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 394) (codeMat 32) = codeMat 4 := by
      unfold actionA
      rw [step109wc128s11_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 330 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 40 ∈ flatW_1 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 64, 32, 16, 8, 4, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 266) (codeMat 394) (codeMat 40) = codeMat 2 := by
      unfold actionA
      rw [step109wc128s11_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 40 * (codeMat 330 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 16 ∈ flatW_1 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 64, 32, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 394) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc128s11_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 330 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc128_codeMat_mem_actionW_of_witness hw hact

theorem step109wc128s11Dispatch :
    QuotientRankAtLeast (o128SourceU_wc ⟨11, by omega⟩) 3 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 394 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 394) flatW_1) 3 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 394) hP hQ flatW_1 3
      flatSeed_1
  exact quotientRankAtLeast_mono step109wc128s11_contain hAct

theorem step109wc128_all_dispatch (i : Fin 12) :
    QuotientRankAtLeast (o128SourceU_wc i) (o128SourceLb_wc i) := by
  fin_cases i
  · exact step109wc128s0Dispatch
  · exact step109wc128s1Dispatch
  · exact step109wc128s2Dispatch
  · exact step109wc128s3Dispatch
  · exact step109wc128s4Dispatch
  · exact step109wc128s5Dispatch
  · exact step109wc128s6Dispatch
  · exact step109wc128s7Dispatch
  · exact step109wc128s8Dispatch
  · exact step109wc128s9Dispatch
  · exact step109wc128s10Dispatch
  · exact step109wc128s11Dispatch

theorem step109_orbit128_lb15_wc : QuotientRankAtLeast o128W_wc 15 :=
  o128Lb15_wc step109wc128_all_dispatch

end QiushiMatmul
