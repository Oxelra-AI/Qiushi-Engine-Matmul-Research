import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit194Consumer
import QiushiWcOrbit72Dispatch
import QiushiStep99Orbit76Dispatch
import QiushiStep99Orbit34Dispatch
import QiushiWcOrbit51Dispatch
import QiushiStep99Orbit55Dispatch
import QiushiMonoOrbit71From17
import QiushiStep99Orbit82Dispatch
import QiushiMonoOrbit43From14
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc194_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc194_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc194s0_QtInv :
    (codeMat 459 : Mat3).transpose⁻¹ = (codeMat 346 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 459 : Mat3).transpose * (codeMat 346 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc194s0_contain :
    (o194SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 403) (codeMat 459) o72W_wc := by
  change spanCodes [262, 132, 32, 22, 10, 1] ≤ actionW (codeMat 403) (codeMat 459) o72W_wc
  apply step109wc194_spanCodes_le_of_gens [262, 132, 32, 22, 10, 1]
    (actionW (codeMat 403) (codeMat 459) o72W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 297 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 297 (by decide)
    have hact : actionA (codeMat 403) (codeMat 459) (codeMat 297) = codeMat 262 := by
      unfold actionA
      rw [step109wc194s0_QtInv]
      show (codeMat 403 : Mat3).transpose * codeMat 297 * (codeMat 346 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 332 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 332 (by decide)
    have hact : actionA (codeMat 403) (codeMat 459) (codeMat 332) = codeMat 132 := by
      unfold actionA
      rw [step109wc194s0_QtInv]
      show (codeMat 403 : Mat3).transpose * codeMat 332 * (codeMat 346 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 403) (codeMat 459) (codeMat 32) = codeMat 32 := by
      unfold actionA
      rw [step109wc194s0_QtInv]
      show (codeMat 403 : Mat3).transpose * codeMat 32 * (codeMat 346 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 33 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 33 (by decide)
    have hact : actionA (codeMat 403) (codeMat 459) (codeMat 33) = codeMat 22 := by
      unfold actionA
      rw [step109wc194s0_QtInv]
      show (codeMat 403 : Mat3).transpose * codeMat 33 * (codeMat 346 : Mat3).transpose = codeMat 22
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 21 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 21 (by decide)
    have hact : actionA (codeMat 403) (codeMat 459) (codeMat 21) = codeMat 10 := by
      unfold actionA
      rw [step109wc194s0_QtInv]
      show (codeMat 403 : Mat3).transpose * codeMat 21 * (codeMat 346 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 63 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 63 (by decide)
    have hact : actionA (codeMat 403) (codeMat 459) (codeMat 63) = codeMat 1 := by
      unfold actionA
      rw [step109wc194s0_QtInv]
      show (codeMat 403 : Mat3).transpose * codeMat 63 * (codeMat 346 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact

theorem step109wc194s0Dispatch :
    QuotientRankAtLeast (o194SourceU_wc ⟨0, by omega⟩) 15 := by
  have hP : Invertible (codeMat 403 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 459 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 403) (codeMat 459) o72W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 403) (codeMat 459) hP hQ o72W_wc 15
      step109_orbit72_lb15_wc
  exact quotientRankAtLeast_mono step109wc194s0_contain hAct


private theorem step109wc194s1_QtInv :
    (codeMat 346 : Mat3).transpose⁻¹ = (codeMat 459 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 346 : Mat3).transpose * (codeMat 459 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc194s1_contain :
    (o194SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 94) (codeMat 346) o76W := by
  change spanCodes [262, 132, 80, 32, 10, 1] ≤ actionW (codeMat 94) (codeMat 346) o76W
  apply step109wc194_spanCodes_le_of_gens [262, 132, 80, 32, 10, 1]
    (actionW (codeMat 94) (codeMat 346) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 228 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 228 (by decide)
    have hact : actionA (codeMat 94) (codeMat 346) (codeMat 228) = codeMat 262 := by
      unfold actionA
      rw [step109wc194s1_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 228 * (codeMat 459 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 475 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 475 (by decide)
    have hact : actionA (codeMat 94) (codeMat 346) (codeMat 475) = codeMat 132 := by
      unfold actionA
      rw [step109wc194s1_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 475 * (codeMat 459 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 366 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 366 (by decide)
    have hact : actionA (codeMat 94) (codeMat 346) (codeMat 366) = codeMat 80 := by
      unfold actionA
      rw [step109wc194s1_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 366 * (codeMat 459 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 288 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 94) (codeMat 346) (codeMat 288) = codeMat 32 := by
      unfold actionA
      rw [step109wc194s1_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 288 * (codeMat 459 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 368 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 368 (by decide)
    have hact : actionA (codeMat 94) (codeMat 346) (codeMat 368) = codeMat 10 := by
      unfold actionA
      rw [step109wc194s1_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 368 * (codeMat 459 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 384 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 384 (by decide)
    have hact : actionA (codeMat 94) (codeMat 346) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step109wc194s1_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 384 * (codeMat 459 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact

theorem step109wc194s1Dispatch :
    QuotientRankAtLeast (o194SourceU_wc ⟨1, by omega⟩) 15 := by
  have hP : Invertible (codeMat 94 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 346 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 94) (codeMat 346) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 94) (codeMat 346) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc194s1_contain hAct


private theorem step109wc194s2_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc194s2_contain :
    (o194SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 273) (codeMat 140) o34W := by
  change spanCodes [258, 128, 32, 10, 4, 1] ≤ actionW (codeMat 273) (codeMat 140) o34W
  apply step109wc194_spanCodes_le_of_gens [258, 128, 32, 10, 4, 1]
    (actionW (codeMat 273) (codeMat 140) o34W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 68 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 68 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 68) = codeMat 258 := by
      unfold actionA
      rw [step109wc194s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 68 * (codeMat 98 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 256) = codeMat 128 := by
      unfold actionA
      rw [step109wc194s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 98 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc194s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 20 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 20) = codeMat 10 := by
      unfold actionA
      rw [step109wc194s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * (codeMat 98 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step109wc194s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc194s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact

theorem step109wc194s2Dispatch :
    QuotientRankAtLeast (o194SourceU_wc ⟨2, by omega⟩) 14 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 140) o34W) 14 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 140) hP hQ o34W 14
      step99_orbit34_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc194s2_contain hAct


private theorem step109wc194s3_QtInv :
    (codeMat 98 : Mat3).transpose⁻¹ = (codeMat 140 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 98 : Mat3).transpose * (codeMat 140 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc194s3_contain :
    (o194SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 266) (codeMat 98) o51W_wc := by
  change spanCodes [262, 132, 32, 16, 10, 1] ≤ actionW (codeMat 266) (codeMat 98) o51W_wc
  apply step109wc194_spanCodes_le_of_gens [262, 132, 32, 16, 10, 1]
    (actionW (codeMat 266) (codeMat 98) o51W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 152 ∈ o51W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [148, 80, 32, 12, 2, 1] 152 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 152) = codeMat 262 := by
      unfold actionA
      rw [step109wc194s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 152 * (codeMat 140 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 80 ∈ o51W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [148, 80, 32, 12, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 80) = codeMat 132 := by
      unfold actionA
      rw [step109wc194s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 80 * (codeMat 140 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ o51W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [148, 80, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [step109wc194s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 140 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o51W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [148, 80, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc194s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 140 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 12 ∈ o51W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [148, 80, 32, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 12) = codeMat 10 := by
      unfold actionA
      rw [step109wc194s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 12 * (codeMat 140 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o51W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [148, 80, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc194s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 140 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact

theorem step109wc194s3Dispatch :
    QuotientRankAtLeast (o194SourceU_wc ⟨3, by omega⟩) 14 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 98) o51W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 98) hP hQ o51W_wc 14
      step109_orbit51_lb14_wc
  exact quotientRankAtLeast_mono step109wc194s3_contain hAct

private def step109wc194s4SrcT : Submodule F2 Mat3 := spanCodes [272, 128, 66, 34, 8, 1]

private theorem step109wc194s4SrcT_lb : QuotientRankAtLeast step109wc194s4SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step99_orbit55_lb14_unconditional
  have hle : step109wc194s4SrcT ≤ transposeW o55W := by
    unfold step109wc194s4SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4 | h5
    · subst h0
      show codeMat 272 ∈ Submodule.map transposeLinearMap o55W
      exact ⟨codeMat 272, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 272 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 128 ∈ Submodule.map transposeLinearMap o55W
      exact ⟨codeMat 32, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 32 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 66 ∈ Submodule.map transposeLinearMap o55W
      exact ⟨codeMat 12, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 12 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 34 ∈ Submodule.map transposeLinearMap o55W
      exact ⟨codeMat 136, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 136 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 8 ∈ Submodule.map transposeLinearMap o55W
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h5
      show codeMat 1 ∈ Submodule.map transposeLinearMap o55W
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc194s4_QtInv :
    (codeMat 167 : Mat3).transpose⁻¹ = (codeMat 167 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 167 : Mat3).transpose * (codeMat 167 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc194s4_contain :
    (o194SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 335) (codeMat 167) step109wc194s4SrcT := by
  change spanCodes [262, 132, 66, 32, 10, 1] ≤ actionW (codeMat 335) (codeMat 167) step109wc194s4SrcT
  apply step109wc194_spanCodes_le_of_gens [262, 132, 66, 32, 10, 1]
    (actionW (codeMat 335) (codeMat 167) step109wc194s4SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 232 ∈ step109wc194s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 232 (by decide)
    have hact : actionA (codeMat 335) (codeMat 167) (codeMat 232) = codeMat 262 := by
      unfold actionA
      rw [step109wc194s4_QtInv]
      show (codeMat 335 : Mat3).transpose * codeMat 232 * (codeMat 167 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 368 ∈ step109wc194s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 368 (by decide)
    have hact : actionA (codeMat 335) (codeMat 167) (codeMat 368) = codeMat 132 := by
      unfold actionA
      rw [step109wc194s4_QtInv]
      show (codeMat 335 : Mat3).transpose * codeMat 368 * (codeMat 167 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 96 ∈ step109wc194s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 96 (by decide)
    have hact : actionA (codeMat 335) (codeMat 167) (codeMat 96) = codeMat 66 := by
      unfold actionA
      rw [step109wc194s4_QtInv]
      show (codeMat 335 : Mat3).transpose * codeMat 96 * (codeMat 167 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 195 ∈ step109wc194s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 195 (by decide)
    have hact : actionA (codeMat 335) (codeMat 167) (codeMat 195) = codeMat 32 := by
      unfold actionA
      rw [step109wc194s4_QtInv]
      show (codeMat 335 : Mat3).transpose * codeMat 195 * (codeMat 167 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 105 ∈ step109wc194s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 105 (by decide)
    have hact : actionA (codeMat 335) (codeMat 167) (codeMat 105) = codeMat 10 := by
      unfold actionA
      rw [step109wc194s4_QtInv]
      show (codeMat 335 : Mat3).transpose * codeMat 105 * (codeMat 167 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ step109wc194s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 8 (by decide)
    have hact : actionA (codeMat 335) (codeMat 167) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc194s4_QtInv]
      show (codeMat 335 : Mat3).transpose * codeMat 8 * (codeMat 167 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact

theorem step109wc194s4Dispatch :
    QuotientRankAtLeast (o194SourceU_wc ⟨4, by omega⟩) 14 := by
  have hP : Invertible (codeMat 335 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 167 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 335) (codeMat 167) step109wc194s4SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 335) (codeMat 167) hP hQ step109wc194s4SrcT 14
      step109wc194s4SrcT_lb
  exact quotientRankAtLeast_mono step109wc194s4_contain hAct


private theorem step109wc194s5_QtInv :
    (codeMat 181 : Mat3).transpose⁻¹ = (codeMat 423 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 181 : Mat3).transpose * (codeMat 423 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc194s5_contain :
    (o194SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 425) (codeMat 181) o71W_mono := by
  change spanCodes [262, 132, 68, 32, 10, 1] ≤ actionW (codeMat 425) (codeMat 181) o71W_mono
  apply step109wc194_spanCodes_le_of_gens [262, 132, 68, 32, 10, 1]
    (actionW (codeMat 425) (codeMat 181) o71W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 30 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 30 (by decide)
    have hact : actionA (codeMat 425) (codeMat 181) (codeMat 30) = codeMat 262 := by
      unfold actionA
      rw [step109wc194s5_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 30 * (codeMat 423 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 53 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 53 (by decide)
    have hact : actionA (codeMat 425) (codeMat 181) (codeMat 53) = codeMat 132 := by
      unfold actionA
      rw [step109wc194s5_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 53 * (codeMat 423 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 10 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 425) (codeMat 181) (codeMat 10) = codeMat 68 := by
      unfold actionA
      rw [step109wc194s5_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 10 * (codeMat 423 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 219 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 219 (by decide)
    have hact : actionA (codeMat 425) (codeMat 181) (codeMat 219) = codeMat 32 := by
      unfold actionA
      rw [step109wc194s5_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 219 * (codeMat 423 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 79 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 79 (by decide)
    have hact : actionA (codeMat 425) (codeMat 181) (codeMat 79) = codeMat 10 := by
      unfold actionA
      rw [step109wc194s5_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 79 * (codeMat 423 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 425) (codeMat 181) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc194s5_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 1 * (codeMat 423 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact

theorem step109wc194s5Dispatch :
    QuotientRankAtLeast (o194SourceU_wc ⟨5, by omega⟩) 14 := by
  have hP : Invertible (codeMat 425 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 181 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 425) (codeMat 181) o71W_mono) 14 :=
    @quotientRankAtLeast_action (codeMat 425) (codeMat 181) hP hQ o71W_mono 14
      orbit71_lb14_mono
  exact quotientRankAtLeast_mono step109wc194s5_contain hAct


private theorem step109wc194s6_QtInv :
    (codeMat 409 : Mat3).transpose⁻¹ = (codeMat 473 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 409 : Mat3).transpose * (codeMat 473 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc194s6_contain :
    (o194SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 103) (codeMat 409) o82W := by
  change spanCodes [262, 132, 86, 32, 10, 1] ≤ actionW (codeMat 103) (codeMat 409) o82W
  apply step109wc194_spanCodes_le_of_gens [262, 132, 86, 32, 10, 1]
    (actionW (codeMat 103) (codeMat 409) o82W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 160 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 103) (codeMat 409) (codeMat 160) = codeMat 262 := by
      unfold actionA
      rw [step109wc194s6_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 160 * (codeMat 473 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 304 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 304 (by decide)
    have hact : actionA (codeMat 103) (codeMat 409) (codeMat 304) = codeMat 132 := by
      unfold actionA
      rw [step109wc194s6_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 304 * (codeMat 473 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 302 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 302 (by decide)
    have hact : actionA (codeMat 103) (codeMat 409) (codeMat 302) = codeMat 86 := by
      unfold actionA
      rw [step109wc194s6_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 302 * (codeMat 473 : Mat3).transpose = codeMat 86
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 292 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 292 (by decide)
    have hact : actionA (codeMat 103) (codeMat 409) (codeMat 292) = codeMat 32 := by
      unfold actionA
      rw [step109wc194s6_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 292 * (codeMat 473 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 347 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 347 (by decide)
    have hact : actionA (codeMat 103) (codeMat 409) (codeMat 347) = codeMat 10 := by
      unfold actionA
      rw [step109wc194s6_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 347 * (codeMat 473 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 192 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 192 (by decide)
    have hact : actionA (codeMat 103) (codeMat 409) (codeMat 192) = codeMat 1 := by
      unfold actionA
      rw [step109wc194s6_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 192 * (codeMat 473 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact

theorem step109wc194s6Dispatch :
    QuotientRankAtLeast (o194SourceU_wc ⟨6, by omega⟩) 14 := by
  have hP : Invertible (codeMat 103 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 409 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 103) (codeMat 409) o82W) 14 :=
    @quotientRankAtLeast_action (codeMat 103) (codeMat 409) hP hQ o82W 14
      step99_orbit82_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc194s6_contain hAct


private theorem step109wc194s7_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc194s7_contain :
    (o194SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 330) (codeMat 161) o43W_mono := by
  change spanCodes [260, 132, 32, 8, 2, 1] ≤ actionW (codeMat 330) (codeMat 161) o43W_mono
  apply step109wc194_spanCodes_le_of_gens [260, 132, 32, 8, 2, 1]
    (actionW (codeMat 330) (codeMat 161) o43W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 128 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 330) (codeMat 161) (codeMat 128) = codeMat 260 := by
      unfold actionA
      rw [step109wc194s7_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 128 * (codeMat 161 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 304 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 304 (by decide)
    have hact : actionA (codeMat 330) (codeMat 161) (codeMat 304) = codeMat 132 := by
      unfold actionA
      rw [step109wc194s7_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 304 * (codeMat 161 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 330) (codeMat 161) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [step109wc194s7_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 330) (codeMat 161) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step109wc194s7_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 330) (codeMat 161) (codeMat 32) = codeMat 2 := by
      unfold actionA
      rw [step109wc194s7_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 32 * (codeMat 161 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 330) (codeMat 161) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc194s7_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact

theorem step109wc194s7Dispatch :
    QuotientRankAtLeast (o194SourceU_wc ⟨7, by omega⟩) 12 := by
  have hP : Invertible (codeMat 330 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 330) (codeMat 161) o43W_mono) 12 :=
    @quotientRankAtLeast_action (codeMat 330) (codeMat 161) hP hQ o43W_mono 12
      orbit43_lb12_mono
  exact quotientRankAtLeast_mono step109wc194s7_contain hAct


private theorem step109wc194s8_QtInv :
    (codeMat 158 : Mat3).transpose⁻¹ = (codeMat 358 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 158 : Mat3).transpose * (codeMat 358 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc194s8_contain :
    (o194SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 84) (codeMat 158) flatW_3 := by
  change spanCodes [256, 130, 64, 32, 18, 10, 6, 1] ≤ actionW (codeMat 84) (codeMat 158) flatW_3
  apply step109wc194_spanCodes_le_of_gens [256, 130, 64, 32, 18, 10, 6, 1]
    (actionW (codeMat 84) (codeMat 158) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 158) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc194s8_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 358 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 455 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 455 (by decide)
    have hact : actionA (codeMat 84) (codeMat 158) (codeMat 455) = codeMat 130 := by
      unfold actionA
      rw [step109wc194s8_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 455 * (codeMat 358 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 158) (codeMat 2) = codeMat 64 := by
      unfold actionA
      rw [step109wc194s8_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 358 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 158) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc194s8_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 358 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 504 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 504 (by decide)
    have hact : actionA (codeMat 84) (codeMat 158) (codeMat 504) = codeMat 18 := by
      unfold actionA
      rw [step109wc194s8_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 504 * (codeMat 358 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 464 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 464 (by decide)
    have hact : actionA (codeMat 84) (codeMat 158) (codeMat 464) = codeMat 10 := by
      unfold actionA
      rw [step109wc194s8_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 464 * (codeMat 358 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 158) (codeMat 384) = codeMat 6 := by
      unfold actionA
      rw [step109wc194s8_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 358 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 158) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc194s8_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 358 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc194_codeMat_mem_actionW_of_witness hw hact

theorem step109wc194s8Dispatch :
    QuotientRankAtLeast (o194SourceU_wc ⟨8, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 158 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 158) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 158) hP hQ flatW_3 9
      flatSeed_3
  exact quotientRankAtLeast_mono step109wc194s8_contain hAct

theorem step109wc194_all_dispatch (i : Fin 9) :
    QuotientRankAtLeast (o194SourceU_wc i) (o194SourceLb_wc i) := by
  fin_cases i
  · exact step109wc194s0Dispatch
  · exact step109wc194s1Dispatch
  · exact step109wc194s2Dispatch
  · exact step109wc194s3Dispatch
  · exact step109wc194s4Dispatch
  · exact step109wc194s5Dispatch
  · exact step109wc194s6Dispatch
  · exact step109wc194s7Dispatch
  · exact step109wc194s8Dispatch

theorem step109_orbit194_lb16_wc : QuotientRankAtLeast o194W_wc 16 :=
  o194Lb16_wc step109wc194_all_dispatch

end QiushiMatmul
