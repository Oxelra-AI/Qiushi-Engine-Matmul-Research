import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit218Consumer
import QiushiStep99Orbit76Dispatch
import QiushiStep99Orbit56Dispatch
import QiushiWcOrbit57Dispatch
import QiushiStep99Orbit82Dispatch
import QiushiWcOrbit83Dispatch
import QiushiWcOrbit78Dispatch
import QiushiOrbit10FP

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc218_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc218_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc218s0_QtInv :
    (codeMat 244 : Mat3).transpose⁻¹ = (codeMat 95 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 244 : Mat3).transpose * (codeMat 95 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc218s0_contain :
    (o218SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 445) (codeMat 244) o76W := by
  change spanCodes [290, 132, 96, 20, 10, 1] ≤ actionW (codeMat 445) (codeMat 244) o76W
  apply step109wc218_spanCodes_le_of_gens [290, 132, 96, 20, 10, 1]
    (actionW (codeMat 445) (codeMat 244) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 368 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 368 (by decide)
    have hact : actionA (codeMat 445) (codeMat 244) (codeMat 368) = codeMat 290 := by
      unfold actionA
      rw [step109wc218s0_QtInv]
      show (codeMat 445 : Mat3).transpose * codeMat 368 * (codeMat 95 : Mat3).transpose = codeMat 290
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 366 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 366 (by decide)
    have hact : actionA (codeMat 445) (codeMat 244) (codeMat 366) = codeMat 132 := by
      unfold actionA
      rw [step109wc218s0_QtInv]
      show (codeMat 445 : Mat3).transpose * codeMat 366 * (codeMat 95 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 319 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 319 (by decide)
    have hact : actionA (codeMat 445) (codeMat 244) (codeMat 319) = codeMat 96 := by
      unfold actionA
      rw [step109wc218s0_QtInv]
      show (codeMat 445 : Mat3).transpose * codeMat 319 * (codeMat 95 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 238 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 238 (by decide)
    have hact : actionA (codeMat 445) (codeMat 244) (codeMat 238) = codeMat 20 := by
      unfold actionA
      rw [step109wc218s0_QtInv]
      show (codeMat 445 : Mat3).transpose * codeMat 238 * (codeMat 95 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 404 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 404 (by decide)
    have hact : actionA (codeMat 445) (codeMat 244) (codeMat 404) = codeMat 10 := by
      unfold actionA
      rw [step109wc218s0_QtInv]
      show (codeMat 445 : Mat3).transpose * codeMat 404 * (codeMat 95 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 288 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 445) (codeMat 244) (codeMat 288) = codeMat 1 := by
      unfold actionA
      rw [step109wc218s0_QtInv]
      show (codeMat 445 : Mat3).transpose * codeMat 288 * (codeMat 95 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact

theorem step109wc218s0Dispatch :
    QuotientRankAtLeast (o218SourceU_wc ⟨0, by omega⟩) 15 := by
  have hP : Invertible (codeMat 445 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 244 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 445) (codeMat 244) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 445) (codeMat 244) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc218s0_contain hAct


private theorem step109wc218s1_QtInv :
    (codeMat 419 : Mat3).transpose⁻¹ = (codeMat 183 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 419 : Mat3).transpose * (codeMat 183 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc218s1_contain :
    (o218SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 249) (codeMat 419) o76W := by
  change spanCodes [274, 132, 68, 36, 10, 1] ≤ actionW (codeMat 249) (codeMat 419) o76W
  apply step109wc218_spanCodes_le_of_gens [274, 132, 68, 36, 10, 1]
    (actionW (codeMat 249) (codeMat 419) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 240 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 240 (by decide)
    have hact : actionA (codeMat 249) (codeMat 419) (codeMat 240) = codeMat 274 := by
      unfold actionA
      rw [step109wc218s1_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 240 * (codeMat 183 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 366 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 366 (by decide)
    have hact : actionA (codeMat 249) (codeMat 419) (codeMat 366) = codeMat 132 := by
      unfold actionA
      rw [step109wc218s1_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 366 * (codeMat 183 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 78 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 249) (codeMat 419) (codeMat 78) = codeMat 68 := by
      unfold actionA
      rw [step109wc218s1_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 78 * (codeMat 183 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 384 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 384 (by decide)
    have hact : actionA (codeMat 249) (codeMat 419) (codeMat 384) = codeMat 36 := by
      unfold actionA
      rw [step109wc218s1_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 384 * (codeMat 183 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 68 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 249) (codeMat 419) (codeMat 68) = codeMat 10 := by
      unfold actionA
      rw [step109wc218s1_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 68 * (codeMat 183 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 249) (codeMat 419) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc218s1_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 1 * (codeMat 183 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact

theorem step109wc218s1Dispatch :
    QuotientRankAtLeast (o218SourceU_wc ⟨1, by omega⟩) 15 := by
  have hP : Invertible (codeMat 249 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 419 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 249) (codeMat 419) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 249) (codeMat 419) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc218s1_contain hAct


private theorem step109wc218s2_QtInv :
    (codeMat 382 : Mat3).transpose⁻¹ = (codeMat 499 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 382 : Mat3).transpose * (codeMat 499 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc218s2_contain :
    (o218SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 95) (codeMat 382) o76W := by
  change spanCodes [262, 132, 80, 48, 10, 1] ≤ actionW (codeMat 95) (codeMat 382) o76W
  apply step109wc218_spanCodes_le_of_gens [262, 132, 80, 48, 10, 1]
    (actionW (codeMat 95) (codeMat 382) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 319 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 319 (by decide)
    have hact : actionA (codeMat 95) (codeMat 382) (codeMat 319) = codeMat 262 := by
      unfold actionA
      rw [step109wc218s2_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 319 * (codeMat 499 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 475 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 475 (by decide)
    have hact : actionA (codeMat 95) (codeMat 382) (codeMat 475) = codeMat 132 := by
      unfold actionA
      rw [step109wc218s2_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 475 * (codeMat 499 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 238 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 238 (by decide)
    have hact : actionA (codeMat 95) (codeMat 382) (codeMat 238) = codeMat 80 := by
      unfold actionA
      rw [step109wc218s2_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 238 * (codeMat 499 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 288 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 95) (codeMat 382) (codeMat 288) = codeMat 48 := by
      unfold actionA
      rw [step109wc218s2_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 288 * (codeMat 499 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 368 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 368 (by decide)
    have hact : actionA (codeMat 95) (codeMat 382) (codeMat 368) = codeMat 10 := by
      unfold actionA
      rw [step109wc218s2_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 368 * (codeMat 499 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 384 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 384 (by decide)
    have hact : actionA (codeMat 95) (codeMat 382) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step109wc218s2_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 384 * (codeMat 499 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact

theorem step109wc218s2Dispatch :
    QuotientRankAtLeast (o218SourceU_wc ⟨2, by omega⟩) 15 := by
  have hP : Invertible (codeMat 95 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 382 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 95) (codeMat 382) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 95) (codeMat 382) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc218s2_contain hAct


private theorem step109wc218s3_QtInv :
    (codeMat 183 : Mat3).transpose⁻¹ = (codeMat 419 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 183 : Mat3).transpose * (codeMat 419 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc218s3_contain :
    (o218SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 465) (codeMat 183) o56W := by
  change spanCodes [306, 128, 96, 10, 4, 1] ≤ actionW (codeMat 465) (codeMat 183) o56W
  apply step109wc218_spanCodes_le_of_gens [306, 128, 96, 10, 4, 1]
    (actionW (codeMat 465) (codeMat 183) o56W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 252 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 252 (by decide)
    have hact : actionA (codeMat 465) (codeMat 183) (codeMat 252) = codeMat 306 := by
      unfold actionA
      rw [step109wc218s3_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 252 * (codeMat 419 : Mat3).transpose = codeMat 306
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 511 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 511 (by decide)
    have hact : actionA (codeMat 465) (codeMat 183) (codeMat 511) = codeMat 128 := by
      unfold actionA
      rw [step109wc218s3_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 511 * (codeMat 419 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 81 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 81 (by decide)
    have hact : actionA (codeMat 465) (codeMat 183) (codeMat 81) = codeMat 96 := by
      unfold actionA
      rw [step109wc218s3_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 81 * (codeMat 419 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 15 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 15 (by decide)
    have hact : actionA (codeMat 465) (codeMat 183) (codeMat 15) = codeMat 10 := by
      unfold actionA
      rw [step109wc218s3_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 15 * (codeMat 419 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 465) (codeMat 183) (codeMat 3) = codeMat 4 := by
      unfold actionA
      rw [step109wc218s3_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 3 * (codeMat 419 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 465) (codeMat 183) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc218s3_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 1 * (codeMat 419 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact

theorem step109wc218s3Dispatch :
    QuotientRankAtLeast (o218SourceU_wc ⟨3, by omega⟩) 14 := by
  have hP : Invertible (codeMat 465 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 183 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 465) (codeMat 183) o56W) 14 :=
    @quotientRankAtLeast_action (codeMat 465) (codeMat 183) hP hQ o56W 14
      step99_orbit56_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc218s3_contain hAct


private theorem step109wc218s4_QtInv :
    (codeMat 442 : Mat3).transpose⁻¹ = (codeMat 334 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 442 : Mat3).transpose * (codeMat 334 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc218s4_contain :
    (o218SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 185) (codeMat 442) o57W_wc := by
  change spanCodes [304, 130, 96, 10, 6, 1] ≤ actionW (codeMat 185) (codeMat 442) o57W_wc
  apply step109wc218_spanCodes_le_of_gens [304, 130, 96, 10, 6, 1]
    (actionW (codeMat 185) (codeMat 442) o57W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 502 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 502 (by decide)
    have hact : actionA (codeMat 185) (codeMat 442) (codeMat 502) = codeMat 304 := by
      unfold actionA
      rw [step109wc218s4_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 502 * (codeMat 334 : Mat3).transpose = codeMat 304
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 504 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 504 (by decide)
    have hact : actionA (codeMat 185) (codeMat 442) (codeMat 504) = codeMat 130 := by
      unfold actionA
      rw [step109wc218s4_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 504 * (codeMat 334 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 274 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 274 (by decide)
    have hact : actionA (codeMat 185) (codeMat 442) (codeMat 274) = codeMat 96 := by
      unfold actionA
      rw [step109wc218s4_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 274 * (codeMat 334 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 135 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 135 (by decide)
    have hact : actionA (codeMat 185) (codeMat 442) (codeMat 135) = codeMat 10 := by
      unfold actionA
      rw [step109wc218s4_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 135 * (codeMat 334 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 185) (codeMat 442) (codeMat 1) = codeMat 6 := by
      unfold actionA
      rw [step109wc218s4_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 1 * (codeMat 334 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 185) (codeMat 442) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc218s4_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 2 * (codeMat 334 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact

theorem step109wc218s4Dispatch :
    QuotientRankAtLeast (o218SourceU_wc ⟨4, by omega⟩) 14 := by
  have hP : Invertible (codeMat 185 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 442 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 185) (codeMat 442) o57W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 185) (codeMat 442) hP hQ o57W_wc 14
      step109_orbit57_lb14_wc
  exact quotientRankAtLeast_mono step109wc218s4_contain hAct


private theorem step109wc218s5_QtInv :
    (codeMat 279 : Mat3).transpose⁻¹ = (codeMat 279 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 279 : Mat3).transpose * (codeMat 279 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc218s5_contain :
    (o218SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 465) (codeMat 279) o82W := by
  change spanCodes [288, 132, 96, 22, 10, 1] ≤ actionW (codeMat 465) (codeMat 279) o82W
  apply step109wc218_spanCodes_le_of_gens [288, 132, 96, 22, 10, 1]
    (actionW (codeMat 465) (codeMat 279) o82W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 325 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 325 (by decide)
    have hact : actionA (codeMat 465) (codeMat 279) (codeMat 325) = codeMat 288 := by
      unfold actionA
      rw [step109wc218s5_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 325 * (codeMat 279 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 222 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 222 (by decide)
    have hact : actionA (codeMat 465) (codeMat 279) (codeMat 222) = codeMat 132 := by
      unfold actionA
      rw [step109wc218s5_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 222 * (codeMat 279 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 97 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 97 (by decide)
    have hact : actionA (codeMat 465) (codeMat 279) (codeMat 97) = codeMat 96 := by
      unfold actionA
      rw [step109wc218s5_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 97 * (codeMat 279 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 30 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 30 (by decide)
    have hact : actionA (codeMat 465) (codeMat 279) (codeMat 30) = codeMat 22 := by
      unfold actionA
      rw [step109wc218s5_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 30 * (codeMat 279 : Mat3).transpose = codeMat 22
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 11 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 465) (codeMat 279) (codeMat 11) = codeMat 10 := by
      unfold actionA
      rw [step109wc218s5_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 11 * (codeMat 279 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 465) (codeMat 279) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc218s5_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 1 * (codeMat 279 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact

theorem step109wc218s5Dispatch :
    QuotientRankAtLeast (o218SourceU_wc ⟨5, by omega⟩) 14 := by
  have hP : Invertible (codeMat 465 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 279 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 465) (codeMat 279) o82W) 14 :=
    @quotientRankAtLeast_action (codeMat 465) (codeMat 279) hP hQ o82W 14
      step99_orbit82_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc218s5_contain hAct

private def step109wc218s6SrcT : Submodule F2 Mat3 := spanCodes [256, 160, 66, 20, 8, 1]

private theorem step109wc218s6SrcT_lb : QuotientRankAtLeast step109wc218s6SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step99_orbit56_lb14_unconditional
  have hle : step109wc218s6SrcT ≤ transposeW o56W := by
    unfold step109wc218s6SrcT transposeW
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

private theorem step109wc218s6_QtInv :
    (codeMat 309 : Mat3).transpose⁻¹ = (codeMat 309 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 309 : Mat3).transpose * (codeMat 309 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc218s6_contain :
    (o218SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 425) (codeMat 309) step109wc218s6SrcT := by
  change spanCodes [278, 132, 64, 32, 10, 1] ≤ actionW (codeMat 425) (codeMat 309) step109wc218s6SrcT
  apply step109wc218_spanCodes_le_of_gens [278, 132, 64, 32, 10, 1]
    (actionW (codeMat 425) (codeMat 309) step109wc218s6SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 168 ∈ step109wc218s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 168 (by decide)
    have hact : actionA (codeMat 425) (codeMat 309) (codeMat 168) = codeMat 278 := by
      unfold actionA
      rw [step109wc218s6_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 168 * (codeMat 309 : Mat3).transpose = codeMat 278
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 21 ∈ step109wc218s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 21 (by decide)
    have hact : actionA (codeMat 425) (codeMat 309) (codeMat 21) = codeMat 132 := by
      unfold actionA
      rw [step109wc218s6_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 21 * (codeMat 309 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 9 ∈ step109wc218s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 9 (by decide)
    have hact : actionA (codeMat 425) (codeMat 309) (codeMat 9) = codeMat 64 := by
      unfold actionA
      rw [step109wc218s6_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 9 * (codeMat 309 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 511 ∈ step109wc218s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 511 (by decide)
    have hact : actionA (codeMat 425) (codeMat 309) (codeMat 511) = codeMat 32 := by
      unfold actionA
      rw [step109wc218s6_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 511 * (codeMat 309 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 75 ∈ step109wc218s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 75 (by decide)
    have hact : actionA (codeMat 425) (codeMat 309) (codeMat 75) = codeMat 10 := by
      unfold actionA
      rw [step109wc218s6_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 75 * (codeMat 309 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ step109wc218s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 1 (by decide)
    have hact : actionA (codeMat 425) (codeMat 309) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc218s6_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 1 * (codeMat 309 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact

theorem step109wc218s6Dispatch :
    QuotientRankAtLeast (o218SourceU_wc ⟨6, by omega⟩) 14 := by
  have hP : Invertible (codeMat 425 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 309 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 425) (codeMat 309) step109wc218s6SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 425) (codeMat 309) hP hQ step109wc218s6SrcT 14
      step109wc218s6SrcT_lb
  exact quotientRankAtLeast_mono step109wc218s6_contain hAct

private def step109wc218s7SrcT : Submodule F2 Mat3 := spanCodes [272, 132, 66, 34, 8, 1]

private theorem step109wc218s7SrcT_lb : QuotientRankAtLeast step109wc218s7SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step109_orbit57_lb14_wc
  have hle : step109wc218s7SrcT ≤ transposeW o57W_wc := by
    unfold step109wc218s7SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4 | h5
    · subst h0
      show codeMat 272 ∈ Submodule.map transposeLinearMap o57W_wc
      exact ⟨codeMat 272, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 272 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 132 ∈ Submodule.map transposeLinearMap o57W_wc
      exact ⟨codeMat 96, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 96 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 66 ∈ Submodule.map transposeLinearMap o57W_wc
      exact ⟨codeMat 12, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 12 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 34 ∈ Submodule.map transposeLinearMap o57W_wc
      exact ⟨codeMat 136, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 136 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 8 ∈ Submodule.map transposeLinearMap o57W_wc
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h5
      show codeMat 1 ∈ Submodule.map transposeLinearMap o57W_wc
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc218s7_QtInv :
    (codeMat 421 : Mat3).transpose⁻¹ = (codeMat 179 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 421 : Mat3).transpose * (codeMat 179 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc218s7_contain :
    (o218SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 334) (codeMat 421) step109wc218s7SrcT := by
  change spanCodes [276, 132, 66, 34, 10, 1] ≤ actionW (codeMat 334) (codeMat 421) step109wc218s7SrcT
  apply step109wc218_spanCodes_le_of_gens [276, 132, 66, 34, 10, 1]
    (actionW (codeMat 334) (codeMat 421) step109wc218s7SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 228 ∈ step109wc218s7SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 66, 34, 8, 1] 228 (by decide)
    have hact : actionA (codeMat 334) (codeMat 421) (codeMat 228) = codeMat 276 := by
      unfold actionA
      rw [step109wc218s7_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 228 * (codeMat 179 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 280 ∈ step109wc218s7SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 66, 34, 8, 1] 280 (by decide)
    have hact : actionA (codeMat 334) (codeMat 421) (codeMat 280) = codeMat 132 := by
      unfold actionA
      rw [step109wc218s7_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 280 * (codeMat 179 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 104 ∈ step109wc218s7SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 66, 34, 8, 1] 104 (by decide)
    have hact : actionA (codeMat 334) (codeMat 421) (codeMat 104) = codeMat 66 := by
      unfold actionA
      rw [step109wc218s7_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 104 * (codeMat 179 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 479 ∈ step109wc218s7SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 66, 34, 8, 1] 479 (by decide)
    have hact : actionA (codeMat 334) (codeMat 421) (codeMat 479) = codeMat 34 := by
      unfold actionA
      rw [step109wc218s7_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 479 * (codeMat 179 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 105 ∈ step109wc218s7SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 66, 34, 8, 1] 105 (by decide)
    have hact : actionA (codeMat 334) (codeMat 421) (codeMat 105) = codeMat 10 := by
      unfold actionA
      rw [step109wc218s7_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 105 * (codeMat 179 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ step109wc218s7SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 66, 34, 8, 1] 8 (by decide)
    have hact : actionA (codeMat 334) (codeMat 421) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc218s7_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 8 * (codeMat 179 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact

theorem step109wc218s7Dispatch :
    QuotientRankAtLeast (o218SourceU_wc ⟨7, by omega⟩) 14 := by
  have hP : Invertible (codeMat 334 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 421 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 334) (codeMat 421) step109wc218s7SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 334) (codeMat 421) hP hQ step109wc218s7SrcT 14
      step109wc218s7SrcT_lb
  exact quotientRankAtLeast_mono step109wc218s7_contain hAct


private theorem step109wc218s8_QtInv :
    (codeMat 419 : Mat3).transpose⁻¹ = (codeMat 183 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 419 : Mat3).transpose * (codeMat 183 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc218s8_contain :
    (o218SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 169) (codeMat 419) o83W_wc := by
  change spanCodes [272, 132, 70, 38, 10, 1] ≤ actionW (codeMat 169) (codeMat 419) o83W_wc
  apply step109wc218_spanCodes_le_of_gens [272, 132, 70, 38, 10, 1]
    (actionW (codeMat 169) (codeMat 419) o83W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 374 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 374 (by decide)
    have hact : actionA (codeMat 169) (codeMat 419) (codeMat 374) = codeMat 272 := by
      unfold actionA
      rw [step109wc218s8_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 374 * (codeMat 183 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 43 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 43 (by decide)
    have hact : actionA (codeMat 169) (codeMat 419) (codeMat 43) = codeMat 132 := by
      unfold actionA
      rw [step109wc218s8_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 43 * (codeMat 183 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 10 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 169) (codeMat 419) (codeMat 10) = codeMat 70 := by
      unfold actionA
      rw [step109wc218s8_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 10 * (codeMat 183 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 387 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 387 (by decide)
    have hact : actionA (codeMat 169) (codeMat 419) (codeMat 387) = codeMat 38 := by
      unfold actionA
      rw [step109wc218s8_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 387 * (codeMat 183 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 69 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 169) (codeMat 419) (codeMat 69) = codeMat 10 := by
      unfold actionA
      rw [step109wc218s8_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 69 * (codeMat 183 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 419) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc218s8_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * (codeMat 183 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact

theorem step109wc218s8Dispatch :
    QuotientRankAtLeast (o218SourceU_wc ⟨8, by omega⟩) 14 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 419 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 419) o83W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 419) hP hQ o83W_wc 14
      step109_orbit83_lb14_wc
  exact quotientRankAtLeast_mono step109wc218s8_contain hAct


private theorem step109wc218s9_QtInv :
    (codeMat 117 : Mat3).transpose⁻¹ = (codeMat 380 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 117 : Mat3).transpose * (codeMat 380 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc218s9_contain :
    (o218SourceU_wc ⟨9, by omega⟩) ≤ actionW (codeMat 348) (codeMat 117) o82W := by
  change spanCodes [260, 132, 82, 50, 10, 1] ≤ actionW (codeMat 348) (codeMat 117) o82W
  apply step109wc218_spanCodes_le_of_gens [260, 132, 82, 50, 10, 1]
    (actionW (codeMat 348) (codeMat 117) o82W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 192 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 192 (by decide)
    have hact : actionA (codeMat 348) (codeMat 117) (codeMat 192) = codeMat 260 := by
      unfold actionA
      rw [step109wc218s9_QtInv]
      show (codeMat 348 : Mat3).transpose * codeMat 192 * (codeMat 380 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 193 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 193 (by decide)
    have hact : actionA (codeMat 348) (codeMat 117) (codeMat 193) = codeMat 132 := by
      unfold actionA
      rw [step109wc218s9_QtInv]
      show (codeMat 348 : Mat3).transpose * codeMat 193 * (codeMat 380 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 21 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 21 (by decide)
    have hact : actionA (codeMat 348) (codeMat 117) (codeMat 21) = codeMat 82 := by
      unfold actionA
      rw [step109wc218s9_QtInv]
      show (codeMat 348 : Mat3).transpose * codeMat 21 * (codeMat 380 : Mat3).transpose = codeMat 82
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 203 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 203 (by decide)
    have hact : actionA (codeMat 348) (codeMat 117) (codeMat 203) = codeMat 50 := by
      unfold actionA
      rw [step109wc218s9_QtInv]
      show (codeMat 348 : Mat3).transpose * codeMat 203 * (codeMat 380 : Mat3).transpose = codeMat 50
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 495 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 495 (by decide)
    have hact : actionA (codeMat 348) (codeMat 117) (codeMat 495) = codeMat 10 := by
      unfold actionA
      rw [step109wc218s9_QtInv]
      show (codeMat 348 : Mat3).transpose * codeMat 495 * (codeMat 380 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 325 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 325 (by decide)
    have hact : actionA (codeMat 348) (codeMat 117) (codeMat 325) = codeMat 1 := by
      unfold actionA
      rw [step109wc218s9_QtInv]
      show (codeMat 348 : Mat3).transpose * codeMat 325 * (codeMat 380 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact

theorem step109wc218s9Dispatch :
    QuotientRankAtLeast (o218SourceU_wc ⟨9, by omega⟩) 14 := by
  have hP : Invertible (codeMat 348 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 117 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 348) (codeMat 117) o82W) 14 :=
    @quotientRankAtLeast_action (codeMat 348) (codeMat 117) hP hQ o82W 14
      step99_orbit82_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc218s9_contain hAct


private theorem step109wc218s10_QtInv :
    (codeMat 172 : Mat3).transpose⁻¹ = (codeMat 99 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 172 : Mat3).transpose * (codeMat 99 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc218s10_contain :
    (o218SourceU_wc ⟨10, by omega⟩) ≤ actionW (codeMat 102) (codeMat 172) o78W_wc := by
  change spanCodes [258, 132, 84, 52, 10, 1] ≤ actionW (codeMat 102) (codeMat 172) o78W_wc
  apply step109wc218_spanCodes_le_of_gens [258, 132, 84, 52, 10, 1]
    (actionW (codeMat 102) (codeMat 172) o78W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 280 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 280 (by decide)
    have hact : actionA (codeMat 102) (codeMat 172) (codeMat 280) = codeMat 258 := by
      unfold actionA
      rw [step109wc218s10_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 280 * (codeMat 99 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 224 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 224 (by decide)
    have hact : actionA (codeMat 102) (codeMat 172) (codeMat 224) = codeMat 132 := by
      unfold actionA
      rw [step109wc218s10_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 224 * (codeMat 99 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 244 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 244 (by decide)
    have hact : actionA (codeMat 102) (codeMat 172) (codeMat 244) = codeMat 84 := by
      unfold actionA
      rw [step109wc218s10_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 244 * (codeMat 99 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 255 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 255 (by decide)
    have hact : actionA (codeMat 102) (codeMat 172) (codeMat 255) = codeMat 52 := by
      unfold actionA
      rw [step109wc218s10_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 255 * (codeMat 99 : Mat3).transpose = codeMat 52
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 274 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 274 (by decide)
    have hact : actionA (codeMat 102) (codeMat 172) (codeMat 274) = codeMat 10 := by
      unfold actionA
      rw [step109wc218s10_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 274 * (codeMat 99 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 102) (codeMat 172) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc218s10_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 128 * (codeMat 99 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact

theorem step109wc218s10Dispatch :
    QuotientRankAtLeast (o218SourceU_wc ⟨10, by omega⟩) 14 := by
  have hP : Invertible (codeMat 102 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 172 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 102) (codeMat 172) o78W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 102) (codeMat 172) hP hQ o78W_wc 14
      step109_orbit78_lb14_wc
  exact quotientRankAtLeast_mono step109wc218s10_contain hAct


private theorem step109wc218s11_QtInv :
    (codeMat 86 : Mat3).transpose⁻¹ = (codeMat 212 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 86 : Mat3).transpose * (codeMat 212 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc218s11_contain :
    (o218SourceU_wc ⟨11, by omega⟩) ≤ actionW (codeMat 140) (codeMat 86) o83W_wc := by
  change spanCodes [256, 132, 86, 54, 10, 1] ≤ actionW (codeMat 140) (codeMat 86) o83W_wc
  apply step109wc218_spanCodes_le_of_gens [256, 132, 86, 54, 10, 1]
    (actionW (codeMat 140) (codeMat 86) o83W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 1 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 86) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc218s11_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * (codeMat 212 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 11 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 140) (codeMat 86) (codeMat 11) = codeMat 132 := by
      unfold actionA
      rw [step109wc218s11_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 11 * (codeMat 212 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 212 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 212 (by decide)
    have hact : actionA (codeMat 140) (codeMat 86) (codeMat 212) = codeMat 86 := by
      unfold actionA
      rw [step109wc218s11_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 212 * (codeMat 212 : Mat3).transpose = codeMat 86
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 144 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 144 (by decide)
    have hact : actionA (codeMat 140) (codeMat 86) (codeMat 144) = codeMat 54 := by
      unfold actionA
      rw [step109wc218s11_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 144 * (codeMat 212 : Mat3).transpose = codeMat 54
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 280 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 280 (by decide)
    have hact : actionA (codeMat 140) (codeMat 86) (codeMat 280) = codeMat 10 := by
      unfold actionA
      rw [step109wc218s11_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 280 * (codeMat 212 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 140) (codeMat 86) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc218s11_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 32 * (codeMat 212 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact

theorem step109wc218s11Dispatch :
    QuotientRankAtLeast (o218SourceU_wc ⟨11, by omega⟩) 14 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 86) o83W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 86) hP hQ o83W_wc 14
      step109_orbit83_lb14_wc
  exact quotientRankAtLeast_mono step109wc218s11_contain hAct


private theorem step109wc218s12_QtInv :
    (codeMat 309 : Mat3).transpose⁻¹ = (codeMat 309 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 309 : Mat3).transpose * (codeMat 309 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc218s12_contain :
    (o218SourceU_wc ⟨12, by omega⟩) ≤ actionW (codeMat 266) (codeMat 309) orbit10W := by
  change spanCodes [292, 132, 96, 16, 8, 2, 1] ≤ actionW (codeMat 266) (codeMat 309) orbit10W
  apply step109wc218_spanCodes_le_of_gens [292, 132, 96, 16, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 309) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 511 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 511 (by decide)
    have hact : actionA (codeMat 266) (codeMat 309) (codeMat 511) = codeMat 292 := by
      unfold actionA
      rw [step109wc218s12_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 511 * (codeMat 309 : Mat3).transpose = codeMat 292
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 184 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 184 (by decide)
    have hact : actionA (codeMat 266) (codeMat 309) (codeMat 184) = codeMat 132 := by
      unfold actionA
      rw [step109wc218s12_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 184 * (codeMat 309 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 71 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 71 (by decide)
    have hact : actionA (codeMat 266) (codeMat 309) (codeMat 71) = codeMat 96 := by
      unfold actionA
      rw [step109wc218s12_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 71 * (codeMat 309 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 309) (codeMat 2) = codeMat 16 := by
      unfold actionA
      rw [step109wc218s12_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 309 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 309) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step109wc218s12_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 309 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 309) (codeMat 16) = codeMat 2 := by
      unfold actionA
      rw [step109wc218s12_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 309 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 309) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc218s12_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 309 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc218_codeMat_mem_actionW_of_witness hw hact

theorem step109wc218s12Dispatch :
    QuotientRankAtLeast (o218SourceU_wc ⟨12, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 309 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 309) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 309) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc218s12_contain hAct

theorem step109wc218_all_dispatch (i : Fin 13) :
    QuotientRankAtLeast (o218SourceU_wc i) (o218SourceLb_wc i) := by
  fin_cases i
  · exact step109wc218s0Dispatch
  · exact step109wc218s1Dispatch
  · exact step109wc218s2Dispatch
  · exact step109wc218s3Dispatch
  · exact step109wc218s4Dispatch
  · exact step109wc218s5Dispatch
  · exact step109wc218s6Dispatch
  · exact step109wc218s7Dispatch
  · exact step109wc218s8Dispatch
  · exact step109wc218s9Dispatch
  · exact step109wc218s10Dispatch
  · exact step109wc218s11Dispatch
  · exact step109wc218s12Dispatch

theorem step109_orbit218_lb16_wc : QuotientRankAtLeast o218W_wc 16 :=
  o218Lb16_wc step109wc218_all_dispatch

end QiushiMatmul
