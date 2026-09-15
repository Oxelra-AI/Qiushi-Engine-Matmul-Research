import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit235Consumer
import QiushiWcOrbit72Dispatch
import QiushiStep99Orbit77Dispatch
import QiushiStep99Orbit76Dispatch
import QiushiWcOrbit81Dispatch
import QiushiStep99Orbit55Dispatch
import QiushiMonoOrbit71From17
import QiushiStep99Orbit56Dispatch
import QiushiOrbit14FP
import QiushiWcOrbit16Dispatch

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc235_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc235_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc235s0_QtInv :
    (codeMat 491 : Mat3).transpose⁻¹ = (codeMat 375 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 491 : Mat3).transpose * (codeMat 375 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc235s0_contain :
    (o235SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 275) (codeMat 491) o72W_wc := by
  change spanCodes [326, 130, 38, 20, 10, 1] ≤ actionW (codeMat 275) (codeMat 491) o72W_wc
  apply step109wc235_spanCodes_le_of_gens [326, 130, 38, 20, 10, 1]
    (actionW (codeMat 275) (codeMat 491) o72W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 91 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 91 (by decide)
    have hact : actionA (codeMat 275) (codeMat 491) (codeMat 91) = codeMat 326 := by
      unfold actionA
      rw [step109wc235s0_QtInv]
      show (codeMat 275 : Mat3).transpose * codeMat 91 * (codeMat 375 : Mat3).transpose = codeMat 326
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 365 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 365 (by decide)
    have hact : actionA (codeMat 275) (codeMat 491) (codeMat 365) = codeMat 130 := by
      unfold actionA
      rw [step109wc235s0_QtInv]
      show (codeMat 275 : Mat3).transpose * codeMat 365 * (codeMat 375 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 43 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 43 (by decide)
    have hact : actionA (codeMat 275) (codeMat 491) (codeMat 43) = codeMat 38 := by
      unfold actionA
      rw [step109wc235s0_QtInv]
      show (codeMat 275 : Mat3).transpose * codeMat 43 * (codeMat 375 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 30 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 30 (by decide)
    have hact : actionA (codeMat 275) (codeMat 491) (codeMat 30) = codeMat 20 := by
      unfold actionA
      rw [step109wc235s0_QtInv]
      show (codeMat 275 : Mat3).transpose * codeMat 30 * (codeMat 375 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 21 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 21 (by decide)
    have hact : actionA (codeMat 275) (codeMat 491) (codeMat 21) = codeMat 10 := by
      unfold actionA
      rw [step109wc235s0_QtInv]
      show (codeMat 275 : Mat3).transpose * codeMat 21 * (codeMat 375 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 63 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 63 (by decide)
    have hact : actionA (codeMat 275) (codeMat 491) (codeMat 63) = codeMat 1 := by
      unfold actionA
      rw [step109wc235s0_QtInv]
      show (codeMat 275 : Mat3).transpose * codeMat 63 * (codeMat 375 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact

theorem step109wc235s0Dispatch :
    QuotientRankAtLeast (o235SourceU_wc ⟨0, by omega⟩) 15 := by
  have hP : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 491 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 275) (codeMat 491) o72W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 275) (codeMat 491) hP hQ o72W_wc 15
      step109_orbit72_lb15_wc
  exact quotientRankAtLeast_mono step109wc235s0_contain hAct


private theorem step109wc235s1_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = (codeMat 267 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * (codeMat 267 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc235s1_contain :
    (o235SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 102) (codeMat 282) o77W := by
  change spanCodes [258, 136, 68, 38, 20, 1] ≤ actionW (codeMat 102) (codeMat 282) o77W
  apply step109wc235_spanCodes_le_of_gens [258, 136, 68, 38, 20, 1]
    (actionW (codeMat 102) (codeMat 282) o77W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 224 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 224 (by decide)
    have hact : actionA (codeMat 102) (codeMat 282) (codeMat 224) = codeMat 258 := by
      unfold actionA
      rw [step109wc235s1_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 224 * (codeMat 267 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 10 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 102) (codeMat 282) (codeMat 10) = codeMat 136 := by
      unfold actionA
      rw [step109wc235s1_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 10 * (codeMat 267 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 272 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 272 (by decide)
    have hact : actionA (codeMat 102) (codeMat 282) (codeMat 272) = codeMat 68 := by
      unfold actionA
      rw [step109wc235s1_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 272 * (codeMat 267 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 484 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 484 (by decide)
    have hact : actionA (codeMat 102) (codeMat 282) (codeMat 484) = codeMat 38 := by
      unfold actionA
      rw [step109wc235s1_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 484 * (codeMat 267 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 283 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 283 (by decide)
    have hact : actionA (codeMat 102) (codeMat 282) (codeMat 283) = codeMat 20 := by
      unfold actionA
      rw [step109wc235s1_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 283 * (codeMat 267 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 102) (codeMat 282) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc235s1_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 128 * (codeMat 267 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact

theorem step109wc235s1Dispatch :
    QuotientRankAtLeast (o235SourceU_wc ⟨1, by omega⟩) 15 := by
  have hP : Invertible (codeMat 102 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 102) (codeMat 282) o77W) 15 :=
    @quotientRankAtLeast_action (codeMat 102) (codeMat 282) hP hQ o77W 15
      step99_orbit77_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc235s1_contain hAct


private theorem step109wc235s2_QtInv :
    (codeMat 474 : Mat3).transpose⁻¹ = (codeMat 395 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 474 : Mat3).transpose * (codeMat 395 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc235s2_contain :
    (o235SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 111) (codeMat 474) o76W := by
  change spanCodes [256, 136, 70, 38, 20, 1] ≤ actionW (codeMat 111) (codeMat 474) o76W
  apply step109wc235_spanCodes_le_of_gens [256, 136, 70, 38, 20, 1]
    (actionW (codeMat 111) (codeMat 474) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 288 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 111) (codeMat 474) (codeMat 288) = codeMat 256 := by
      unfold actionA
      rw [step109wc235s2_QtInv]
      show (codeMat 111 : Mat3).transpose * codeMat 288 * (codeMat 395 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 462 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 462 (by decide)
    have hact : actionA (codeMat 111) (codeMat 474) (codeMat 462) = codeMat 136 := by
      unfold actionA
      rw [step109wc235s2_QtInv]
      show (codeMat 111 : Mat3).transpose * codeMat 462 * (codeMat 395 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 368 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 368 (by decide)
    have hact : actionA (codeMat 111) (codeMat 474) (codeMat 368) = codeMat 70 := by
      unfold actionA
      rw [step109wc235s2_QtInv]
      show (codeMat 111 : Mat3).transpose * codeMat 368 * (codeMat 395 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 228 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 228 (by decide)
    have hact : actionA (codeMat 111) (codeMat 474) (codeMat 228) = codeMat 38 := by
      unfold actionA
      rw [step109wc235s2_QtInv]
      show (codeMat 111 : Mat3).transpose * codeMat 228 * (codeMat 395 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 319 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 319 (by decide)
    have hact : actionA (codeMat 111) (codeMat 474) (codeMat 319) = codeMat 20 := by
      unfold actionA
      rw [step109wc235s2_QtInv]
      show (codeMat 111 : Mat3).transpose * codeMat 319 * (codeMat 395 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 384 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 384 (by decide)
    have hact : actionA (codeMat 111) (codeMat 474) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step109wc235s2_QtInv]
      show (codeMat 111 : Mat3).transpose * codeMat 384 * (codeMat 395 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact

theorem step109wc235s2Dispatch :
    QuotientRankAtLeast (o235SourceU_wc ⟨2, by omega⟩) 15 := by
  have hP : Invertible (codeMat 111 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 474 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 111) (codeMat 474) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 111) (codeMat 474) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc235s2_contain hAct


private theorem step109wc235s3_QtInv :
    (codeMat 397 : Mat3).transpose⁻¹ = (codeMat 250 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 397 : Mat3).transpose * (codeMat 250 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc235s3_contain :
    (o235SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 94) (codeMat 397) o81W_wc := by
  change spanCodes [266, 136, 76, 38, 20, 1] ≤ actionW (codeMat 94) (codeMat 397) o81W_wc
  apply step109wc235_spanCodes_le_of_gens [266, 136, 76, 38, 20, 1]
    (actionW (codeMat 94) (codeMat 397) o81W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 181 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 181 (by decide)
    have hact : actionA (codeMat 94) (codeMat 397) (codeMat 181) = codeMat 266 := by
      unfold actionA
      rw [step109wc235s3_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 181 * (codeMat 250 : Mat3).transpose = codeMat 266
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 508 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 508 (by decide)
    have hact : actionA (codeMat 94) (codeMat 397) (codeMat 508) = codeMat 136 := by
      unfold actionA
      rw [step109wc235s3_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 508 * (codeMat 250 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 323 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 323 (by decide)
    have hact : actionA (codeMat 94) (codeMat 397) (codeMat 323) = codeMat 76 := by
      unfold actionA
      rw [step109wc235s3_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 323 * (codeMat 250 : Mat3).transpose = codeMat 76
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 296 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 296 (by decide)
    have hact : actionA (codeMat 94) (codeMat 397) (codeMat 296) = codeMat 38 := by
      unfold actionA
      rw [step109wc235s3_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 296 * (codeMat 250 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 96 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 96 (by decide)
    have hact : actionA (codeMat 94) (codeMat 397) (codeMat 96) = codeMat 20 := by
      unfold actionA
      rw [step109wc235s3_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 96 * (codeMat 250 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 192 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 192 (by decide)
    have hact : actionA (codeMat 94) (codeMat 397) (codeMat 192) = codeMat 1 := by
      unfold actionA
      rw [step109wc235s3_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 192 * (codeMat 250 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact

theorem step109wc235s3Dispatch :
    QuotientRankAtLeast (o235SourceU_wc ⟨3, by omega⟩) 15 := by
  have hP : Invertible (codeMat 94 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 397 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 94) (codeMat 397) o81W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 94) (codeMat 397) hP hQ o81W_wc 15
      step109_orbit81_lb15_wc
  exact quotientRankAtLeast_mono step109wc235s3_contain hAct


private theorem step109wc235s4_QtInv :
    (codeMat 403 : Mat3).transpose⁻¹ = (codeMat 403 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 403 : Mat3).transpose * (codeMat 403 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc235s4_contain :
    (o235SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 305) (codeMat 403) o81W_wc := by
  change spanCodes [264, 136, 78, 38, 20, 1] ≤ actionW (codeMat 305) (codeMat 403) o81W_wc
  apply step109wc235_spanCodes_le_of_gens [264, 136, 78, 38, 20, 1]
    (actionW (codeMat 305) (codeMat 403) o81W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 328 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 328 (by decide)
    have hact : actionA (codeMat 305) (codeMat 403) (codeMat 328) = codeMat 264 := by
      unfold actionA
      rw [step109wc235s4_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 328 * (codeMat 403 : Mat3).transpose = codeMat 264
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 392 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 392 (by decide)
    have hact : actionA (codeMat 305) (codeMat 403) (codeMat 392) = codeMat 136 := by
      unfold actionA
      rw [step109wc235s4_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 392 * (codeMat 403 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 11 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 305) (codeMat 403) (codeMat 11) = codeMat 78 := by
      unfold actionA
      rw [step109wc235s4_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 11 * (codeMat 403 : Mat3).transpose = codeMat 78
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 291 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 291 (by decide)
    have hact : actionA (codeMat 305) (codeMat 403) (codeMat 291) = codeMat 38 := by
      unfold actionA
      rw [step109wc235s4_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 291 * (codeMat 403 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 508 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 508 (by decide)
    have hact : actionA (codeMat 305) (codeMat 403) (codeMat 508) = codeMat 20 := by
      unfold actionA
      rw [step109wc235s4_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 508 * (codeMat 403 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 305) (codeMat 403) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc235s4_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 1 * (codeMat 403 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact

theorem step109wc235s4Dispatch :
    QuotientRankAtLeast (o235SourceU_wc ⟨4, by omega⟩) 15 := by
  have hP : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 403 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 305) (codeMat 403) o81W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 305) (codeMat 403) hP hQ o81W_wc 15
      step109_orbit81_lb15_wc
  exact quotientRankAtLeast_mono step109wc235s4_contain hAct


private theorem step109wc235s5_QtInv :
    (codeMat 141 : Mat3).transpose⁻¹ = (codeMat 226 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 141 : Mat3).transpose * (codeMat 226 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc235s5_contain :
    (o235SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 337) (codeMat 141) o55W := by
  change spanCodes [322, 136, 34, 16, 4, 1] ≤ actionW (codeMat 337) (codeMat 141) o55W
  apply step109wc235_spanCodes_le_of_gens [322, 136, 34, 16, 4, 1]
    (actionW (codeMat 337) (codeMat 141) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 134 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 134 (by decide)
    have hact : actionA (codeMat 337) (codeMat 141) (codeMat 134) = codeMat 322 := by
      unfold actionA
      rw [step109wc235s5_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 134 * (codeMat 226 : Mat3).transpose = codeMat 322
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 284 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 284 (by decide)
    have hact : actionA (codeMat 337) (codeMat 141) (codeMat 284) = codeMat 136 := by
      unfold actionA
      rw [step109wc235s5_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 284 * (codeMat 226 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 12 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 337) (codeMat 141) (codeMat 12) = codeMat 34 := by
      unfold actionA
      rw [step109wc235s5_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 12 * (codeMat 226 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 337) (codeMat 141) (codeMat 32) = codeMat 16 := by
      unfold actionA
      rw [step109wc235s5_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 32 * (codeMat 226 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 337) (codeMat 141) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step109wc235s5_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 1 * (codeMat 226 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 337) (codeMat 141) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step109wc235s5_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 3 * (codeMat 226 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact

theorem step109wc235s5Dispatch :
    QuotientRankAtLeast (o235SourceU_wc ⟨5, by omega⟩) 14 := by
  have hP : Invertible (codeMat 337 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 141 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 337) (codeMat 141) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 337) (codeMat 141) hP hQ o55W 14
      step99_orbit55_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc235s5_contain hAct


private theorem step109wc235s6_QtInv :
    (codeMat 397 : Mat3).transpose⁻¹ = (codeMat 250 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 397 : Mat3).transpose * (codeMat 250 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc235s6_contain :
    (o235SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 409) (codeMat 397) o55W := by
  change spanCodes [320, 136, 32, 18, 6, 1] ≤ actionW (codeMat 409) (codeMat 397) o55W
  apply step109wc235_spanCodes_le_of_gens [320, 136, 32, 18, 6, 1]
    (actionW (codeMat 409) (codeMat 397) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 438 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 438 (by decide)
    have hact : actionA (codeMat 409) (codeMat 397) (codeMat 438) = codeMat 320 := by
      unfold actionA
      rw [step109wc235s6_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 438 * (codeMat 250 : Mat3).transpose = codeMat 320
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 319 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 319 (by decide)
    have hact : actionA (codeMat 409) (codeMat 397) (codeMat 319) = codeMat 136 := by
      unfold actionA
      rw [step109wc235s6_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 319 * (codeMat 250 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 45 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 45 (by decide)
    have hact : actionA (codeMat 409) (codeMat 397) (codeMat 45) = codeMat 32 := by
      unfold actionA
      rw [step109wc235s6_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 45 * (codeMat 250 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 409) (codeMat 397) (codeMat 32) = codeMat 18 := by
      unfold actionA
      rw [step109wc235s6_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 32 * (codeMat 250 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 409) (codeMat 397) (codeMat 1) = codeMat 6 := by
      unfold actionA
      rw [step109wc235s6_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 1 * (codeMat 250 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 409) (codeMat 397) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step109wc235s6_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 3 * (codeMat 250 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact

theorem step109wc235s6Dispatch :
    QuotientRankAtLeast (o235SourceU_wc ⟨6, by omega⟩) 14 := by
  have hP : Invertible (codeMat 409 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 397 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 409) (codeMat 397) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 409) (codeMat 397) hP hQ o55W 14
      step99_orbit55_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc235s6_contain hAct


private theorem step109wc235s7_QtInv :
    (codeMat 351 : Mat3).transpose⁻¹ = (codeMat 239 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 351 : Mat3).transpose * (codeMat 239 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc235s7_contain :
    (o235SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 467) (codeMat 351) o71W_mono := by
  change spanCodes [326, 132, 38, 20, 12, 1] ≤ actionW (codeMat 467) (codeMat 351) o71W_mono
  apply step109wc235_spanCodes_le_of_gens [326, 132, 38, 20, 12, 1]
    (actionW (codeMat 467) (codeMat 351) o71W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 180 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 180 (by decide)
    have hact : actionA (codeMat 467) (codeMat 351) (codeMat 180) = codeMat 326 := by
      unfold actionA
      rw [step109wc235s7_QtInv]
      show (codeMat 467 : Mat3).transpose * codeMat 180 * (codeMat 239 : Mat3).transpose = codeMat 326
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 238 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 238 (by decide)
    have hact : actionA (codeMat 467) (codeMat 351) (codeMat 238) = codeMat 132 := by
      unfold actionA
      rw [step109wc235s7_QtInv]
      show (codeMat 467 : Mat3).transpose * codeMat 238 * (codeMat 239 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 30 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 30 (by decide)
    have hact : actionA (codeMat 467) (codeMat 351) (codeMat 30) = codeMat 38 := by
      unfold actionA
      rw [step109wc235s7_QtInv]
      show (codeMat 467 : Mat3).transpose * codeMat 30 * (codeMat 239 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 53 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 53 (by decide)
    have hact : actionA (codeMat 467) (codeMat 351) (codeMat 53) = codeMat 20 := by
      unfold actionA
      rw [step109wc235s7_QtInv]
      show (codeMat 467 : Mat3).transpose * codeMat 53 * (codeMat 239 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 21 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 21 (by decide)
    have hact : actionA (codeMat 467) (codeMat 351) (codeMat 21) = codeMat 12 := by
      unfold actionA
      rw [step109wc235s7_QtInv]
      show (codeMat 467 : Mat3).transpose * codeMat 21 * (codeMat 239 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 63 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 63 (by decide)
    have hact : actionA (codeMat 467) (codeMat 351) (codeMat 63) = codeMat 1 := by
      unfold actionA
      rw [step109wc235s7_QtInv]
      show (codeMat 467 : Mat3).transpose * codeMat 63 * (codeMat 239 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact

theorem step109wc235s7Dispatch :
    QuotientRankAtLeast (o235SourceU_wc ⟨7, by omega⟩) 14 := by
  have hP : Invertible (codeMat 467 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 351 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 467) (codeMat 351) o71W_mono) 14 :=
    @quotientRankAtLeast_action (codeMat 467) (codeMat 351) hP hQ o71W_mono 14
      orbit71_lb14_mono
  exact quotientRankAtLeast_mono step109wc235s7_contain hAct


private theorem step109wc235s8_QtInv :
    (codeMat 342 : Mat3).transpose⁻¹ = (codeMat 215 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 342 : Mat3).transpose * (codeMat 215 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc235s8_contain :
    (o235SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 266) (codeMat 342) o71W_mono := by
  change spanCodes [326, 134, 38, 20, 14, 1] ≤ actionW (codeMat 266) (codeMat 342) o71W_mono
  apply step109wc235_spanCodes_le_of_gens [326, 134, 38, 20, 14, 1]
    (actionW (codeMat 266) (codeMat 342) o71W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 112 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 112 (by decide)
    have hact : actionA (codeMat 266) (codeMat 342) (codeMat 112) = codeMat 326 := by
      unfold actionA
      rw [step109wc235s8_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 112 * (codeMat 215 : Mat3).transpose = codeMat 326
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 240 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 240 (by decide)
    have hact : actionA (codeMat 266) (codeMat 342) (codeMat 240) = codeMat 134 := by
      unfold actionA
      rw [step109wc235s8_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 240 * (codeMat 215 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 53 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 53 (by decide)
    have hact : actionA (codeMat 266) (codeMat 342) (codeMat 53) = codeMat 38 := by
      unfold actionA
      rw [step109wc235s8_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 53 * (codeMat 215 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 43 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 43 (by decide)
    have hact : actionA (codeMat 266) (codeMat 342) (codeMat 43) = codeMat 20 := by
      unfold actionA
      rw [step109wc235s8_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 43 * (codeMat 215 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 52 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 52 (by decide)
    have hact : actionA (codeMat 266) (codeMat 342) (codeMat 52) = codeMat 14 := by
      unfold actionA
      rw [step109wc235s8_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 52 * (codeMat 215 : Mat3).transpose = codeMat 14
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 342) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc235s8_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 215 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact

theorem step109wc235s8Dispatch :
    QuotientRankAtLeast (o235SourceU_wc ⟨8, by omega⟩) 14 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 342 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 342) o71W_mono) 14 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 342) hP hQ o71W_mono 14
      orbit71_lb14_mono
  exact quotientRankAtLeast_mono step109wc235s8_contain hAct

private def step109wc235s9SrcT : Submodule F2 Mat3 := spanCodes [256, 160, 66, 20, 8, 1]

private theorem step109wc235s9SrcT_lb : QuotientRankAtLeast step109wc235s9SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step99_orbit56_lb14_unconditional
  have hle : step109wc235s9SrcT ≤ transposeW o56W := by
    unfold step109wc235s9SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4 | h5
    · subst h0
      show codeMat 256 ∈ Submodule.map transposeLinearMap o56W
      exact ⟨codeMat 256, spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 256 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 160 ∈ Submodule.map transposeLinearMap o56W
      exact ⟨codeMat 160, spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 160 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 66 ∈ Submodule.map transposeLinearMap o56W
      exact ⟨codeMat 12, spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 12 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 20 ∈ Submodule.map transposeLinearMap o56W
      exact ⟨codeMat 80, spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 80 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 8 ∈ Submodule.map transposeLinearMap o56W
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h5
      show codeMat 1 ∈ Submodule.map transposeLinearMap o56W
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc235s9_QtInv :
    (codeMat 163 : Mat3).transpose⁻¹ = (codeMat 165 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 163 : Mat3).transpose * (codeMat 165 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc235s9_contain :
    (o235SourceU_wc ⟨9, by omega⟩) ≤ actionW (codeMat 318) (codeMat 163) step109wc235s9SrcT := by
  change spanCodes [270, 136, 72, 38, 20, 1] ≤ actionW (codeMat 318) (codeMat 163) step109wc235s9SrcT
  apply step109wc235_spanCodes_le_of_gens [270, 136, 72, 38, 20, 1]
    (actionW (codeMat 318) (codeMat 163) step109wc235s9SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 254 ∈ step109wc235s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 254 (by decide)
    have hact : actionA (codeMat 318) (codeMat 163) (codeMat 254) = codeMat 270 := by
      unfold actionA
      rw [step109wc235s9_QtInv]
      show (codeMat 318 : Mat3).transpose * codeMat 254 * (codeMat 165 : Mat3).transpose = codeMat 270
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 257 ∈ step109wc235s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 257 (by decide)
    have hact : actionA (codeMat 318) (codeMat 163) (codeMat 257) = codeMat 136 := by
      unfold actionA
      rw [step109wc235s9_QtInv]
      show (codeMat 318 : Mat3).transpose * codeMat 257 * (codeMat 165 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ step109wc235s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 1 (by decide)
    have hact : actionA (codeMat 318) (codeMat 163) (codeMat 1) = codeMat 72 := by
      unfold actionA
      rw [step109wc235s9_QtInv]
      show (codeMat 318 : Mat3).transpose * codeMat 1 * (codeMat 165 : Mat3).transpose = codeMat 72
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 189 ∈ step109wc235s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 189 (by decide)
    have hact : actionA (codeMat 318) (codeMat 163) (codeMat 189) = codeMat 38 := by
      unfold actionA
      rw [step109wc235s9_QtInv]
      show (codeMat 318 : Mat3).transpose * codeMat 189 * (codeMat 165 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 343 ∈ step109wc235s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 343 (by decide)
    have hact : actionA (codeMat 318) (codeMat 163) (codeMat 343) = codeMat 20 := by
      unfold actionA
      rw [step109wc235s9_QtInv]
      show (codeMat 318 : Mat3).transpose * codeMat 343 * (codeMat 165 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 9 ∈ step109wc235s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 9 (by decide)
    have hact : actionA (codeMat 318) (codeMat 163) (codeMat 9) = codeMat 1 := by
      unfold actionA
      rw [step109wc235s9_QtInv]
      show (codeMat 318 : Mat3).transpose * codeMat 9 * (codeMat 165 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact

theorem step109wc235s9Dispatch :
    QuotientRankAtLeast (o235SourceU_wc ⟨9, by omega⟩) 14 := by
  have hP : Invertible (codeMat 318 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 163 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 318) (codeMat 163) step109wc235s9SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 318) (codeMat 163) hP hQ step109wc235s9SrcT 14
      step109wc235s9SrcT_lb
  exact quotientRankAtLeast_mono step109wc235s9_contain hAct


private theorem step109wc235s10_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc235s10_contain :
    (o235SourceU_wc ⟨10, by omega⟩) ≤ actionW (codeMat 93) (codeMat 140) orbit14W := by
  change spanCodes [260, 136, 64, 36, 20, 2, 1] ≤ actionW (codeMat 93) (codeMat 140) orbit14W
  apply step109wc235_spanCodes_le_of_gens [260, 136, 64, 36, 20, 2, 1]
    (actionW (codeMat 93) (codeMat 140) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 93) (codeMat 140) (codeMat 1) = codeMat 260 := by
      unfold actionA
      rw [step109wc235s10_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 404 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 404 (by decide)
    have hact : actionA (codeMat 93) (codeMat 140) (codeMat 404) = codeMat 136 := by
      unfold actionA
      rw [step109wc235s10_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 404 * (codeMat 98 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 130 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 130 (by decide)
    have hact : actionA (codeMat 93) (codeMat 140) (codeMat 130) = codeMat 64 := by
      unfold actionA
      rw [step109wc235s10_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 130 * (codeMat 98 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 93) (codeMat 140) (codeMat 8) = codeMat 36 := by
      unfold actionA
      rw [step109wc235s10_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 352 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 352 (by decide)
    have hact : actionA (codeMat 93) (codeMat 140) (codeMat 352) = codeMat 20 := by
      unfold actionA
      rw [step109wc235s10_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 352 * (codeMat 98 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 93) (codeMat 140) (codeMat 256) = codeMat 2 := by
      unfold actionA
      rw [step109wc235s10_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 256 * (codeMat 98 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 93) (codeMat 140) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc235s10_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 128 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact

theorem step109wc235s10Dispatch :
    QuotientRankAtLeast (o235SourceU_wc ⟨10, by omega⟩) 12 := by
  have hP : Invertible (codeMat 93 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 93) (codeMat 140) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 93) (codeMat 140) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc235s10_contain hAct


private theorem step109wc235s11_QtInv :
    (codeMat 242 : Mat3).transpose⁻¹ = (codeMat 205 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 242 : Mat3).transpose * (codeMat 205 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc235s11_contain :
    (o235SourceU_wc ⟨11, by omega⟩) ≤ actionW (codeMat 85) (codeMat 242) o16W_wc := by
  change spanCodes [260, 128, 66, 38, 20, 8, 1] ≤ actionW (codeMat 85) (codeMat 242) o16W_wc
  apply step109wc235_spanCodes_le_of_gens [260, 128, 66, 38, 20, 8, 1]
    (actionW (codeMat 85) (codeMat 242) o16W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 2 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 85) (codeMat 242) (codeMat 2) = codeMat 260 := by
      unfold actionA
      rw [step109wc235s11_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 2 * (codeMat 205 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 455 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 455 (by decide)
    have hact : actionA (codeMat 85) (codeMat 242) (codeMat 455) = codeMat 128 := by
      unfold actionA
      rw [step109wc235s11_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 455 * (codeMat 205 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 196 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 196 (by decide)
    have hact : actionA (codeMat 85) (codeMat 242) (codeMat 196) = codeMat 66 := by
      unfold actionA
      rw [step109wc235s11_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 196 * (codeMat 205 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 336 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 336 (by decide)
    have hact : actionA (codeMat 85) (codeMat 242) (codeMat 336) = codeMat 38 := by
      unfold actionA
      rw [step109wc235s11_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 336 * (codeMat 205 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 184 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 184 (by decide)
    have hact : actionA (codeMat 85) (codeMat 242) (codeMat 184) = codeMat 20 := by
      unfold actionA
      rw [step109wc235s11_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 184 * (codeMat 205 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 85) (codeMat 242) (codeMat 32) = codeMat 8 := by
      unfold actionA
      rw [step109wc235s11_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 32 * (codeMat 205 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 85) (codeMat 242) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc235s11_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 256 * (codeMat 205 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc235_codeMat_mem_actionW_of_witness hw hact

theorem step109wc235s11Dispatch :
    QuotientRankAtLeast (o235SourceU_wc ⟨11, by omega⟩) 12 := by
  have hP : Invertible (codeMat 85 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 242 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 85) (codeMat 242) o16W_wc) 12 :=
    @quotientRankAtLeast_action (codeMat 85) (codeMat 242) hP hQ o16W_wc 12
      step109_orbit16_lb12_wc
  exact quotientRankAtLeast_mono step109wc235s11_contain hAct

theorem step109wc235_all_dispatch (i : Fin 12) :
    QuotientRankAtLeast (o235SourceU_wc i) (o235SourceLb_wc i) := by
  fin_cases i
  · exact step109wc235s0Dispatch
  · exact step109wc235s1Dispatch
  · exact step109wc235s2Dispatch
  · exact step109wc235s3Dispatch
  · exact step109wc235s4Dispatch
  · exact step109wc235s5Dispatch
  · exact step109wc235s6Dispatch
  · exact step109wc235s7Dispatch
  · exact step109wc235s8Dispatch
  · exact step109wc235s9Dispatch
  · exact step109wc235s10Dispatch
  · exact step109wc235s11Dispatch

theorem step109_orbit235_lb16_wc : QuotientRankAtLeast o235W_wc 16 :=
  o235Lb16_wc step109wc235_all_dispatch

end QiushiMatmul
