import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit201Consumer
import QiushiStep99Orbit76Dispatch
import QiushiStep99Orbit55Dispatch
import QiushiMonoOrbit74From17
import QiushiStep99Orbit56Dispatch
import QiushiOrbit14FP
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc201_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc201_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc201s0_QtInv :
    (codeMat 419 : Mat3).transpose⁻¹ = (codeMat 183 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 419 : Mat3).transpose * (codeMat 183 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc201s0_contain :
    (o201SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 177) (codeMat 419) o76W := by
  change spanCodes [272, 132, 68, 32, 10, 1] ≤ actionW (codeMat 177) (codeMat 419) o76W
  apply step109wc201_spanCodes_le_of_gens [272, 132, 68, 32, 10, 1]
    (actionW (codeMat 177) (codeMat 419) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 240 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 240 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 240) = codeMat 272 := by
      unfold actionA
      rw [step109wc201s0_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 240 * (codeMat 183 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 366 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 366 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 366) = codeMat 132 := by
      unfold actionA
      rw [step109wc201s0_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 366 * (codeMat 183 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 78 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 78) = codeMat 68 := by
      unfold actionA
      rw [step109wc201s0_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 78 * (codeMat 183 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 384 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 384 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 384) = codeMat 32 := by
      unfold actionA
      rw [step109wc201s0_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 384 * (codeMat 183 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 69 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 69) = codeMat 10 := by
      unfold actionA
      rw [step109wc201s0_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 69 * (codeMat 183 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc201s0_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * (codeMat 183 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact

theorem step109wc201s0Dispatch :
    QuotientRankAtLeast (o201SourceU_wc ⟨0, by omega⟩) 15 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 419 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 419) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 419) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc201s0_contain hAct


private theorem step109wc201s1_QtInv :
    (codeMat 405 : Mat3).transpose⁻¹ = (codeMat 407 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 405 : Mat3).transpose * (codeMat 407 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc201s1_contain :
    (o201SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 473) (codeMat 405) o55W := by
  change spanCodes [338, 130, 32, 10, 6, 1] ≤ actionW (codeMat 473) (codeMat 405) o55W
  apply step109wc201_spanCodes_le_of_gens [338, 130, 32, 10, 6, 1]
    (actionW (codeMat 473) (codeMat 405) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 272 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 272 (by decide)
    have hact : actionA (codeMat 473) (codeMat 405) (codeMat 272) = codeMat 338 := by
      unfold actionA
      rw [step109wc201s1_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 272 * (codeMat 407 : Mat3).transpose = codeMat 338
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 438 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 438 (by decide)
    have hact : actionA (codeMat 473) (codeMat 405) (codeMat 438) = codeMat 130 := by
      unfold actionA
      rw [step109wc201s1_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 438 * (codeMat 407 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 45 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 45 (by decide)
    have hact : actionA (codeMat 473) (codeMat 405) (codeMat 45) = codeMat 32 := by
      unfold actionA
      rw [step109wc201s1_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 45 * (codeMat 407 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 15 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 15 (by decide)
    have hact : actionA (codeMat 473) (codeMat 405) (codeMat 15) = codeMat 10 := by
      unfold actionA
      rw [step109wc201s1_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 15 * (codeMat 407 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 473) (codeMat 405) (codeMat 3) = codeMat 6 := by
      unfold actionA
      rw [step109wc201s1_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 3 * (codeMat 407 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 473) (codeMat 405) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc201s1_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 1 * (codeMat 407 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact

theorem step109wc201s1Dispatch :
    QuotientRankAtLeast (o201SourceU_wc ⟨1, by omega⟩) 14 := by
  have hP : Invertible (codeMat 473 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 405 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 473) (codeMat 405) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 473) (codeMat 405) hP hQ o55W 14
      step99_orbit55_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc201s1_contain hAct


private theorem step109wc201s2_QtInv :
    (codeMat 229 : Mat3).transpose⁻¹ = (codeMat 187 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 229 : Mat3).transpose * (codeMat 187 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc201s2_contain :
    (o201SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 410) (codeMat 229) o55W := by
  change spanCodes [326, 132, 32, 18, 10, 1] ≤ actionW (codeMat 410) (codeMat 229) o55W
  apply step109wc201_spanCodes_le_of_gens [326, 132, 32, 18, 10, 1]
    (actionW (codeMat 410) (codeMat 229) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 441 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 441 (by decide)
    have hact : actionA (codeMat 410) (codeMat 229) (codeMat 441) = codeMat 326 := by
      unfold actionA
      rw [step109wc201s2_QtInv]
      show (codeMat 410 : Mat3).transpose * codeMat 441 * (codeMat 187 : Mat3).transpose = codeMat 326
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 287 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 287 (by decide)
    have hact : actionA (codeMat 410) (codeMat 229) (codeMat 287) = codeMat 132 := by
      unfold actionA
      rw [step109wc201s2_QtInv]
      show (codeMat 410 : Mat3).transpose * codeMat 287 * (codeMat 187 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 3 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 410) (codeMat 229) (codeMat 3) = codeMat 32 := by
      unfold actionA
      rw [step109wc201s2_QtInv]
      show (codeMat 410 : Mat3).transpose * codeMat 3 * (codeMat 187 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 410) (codeMat 229) (codeMat 32) = codeMat 18 := by
      unfold actionA
      rw [step109wc201s2_QtInv]
      show (codeMat 410 : Mat3).transpose * codeMat 32 * (codeMat 187 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 33 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 33 (by decide)
    have hact : actionA (codeMat 410) (codeMat 229) (codeMat 33) = codeMat 10 := by
      unfold actionA
      rw [step109wc201s2_QtInv]
      show (codeMat 410 : Mat3).transpose * codeMat 33 * (codeMat 187 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 45 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 45 (by decide)
    have hact : actionA (codeMat 410) (codeMat 229) (codeMat 45) = codeMat 1 := by
      unfold actionA
      rw [step109wc201s2_QtInv]
      show (codeMat 410 : Mat3).transpose * codeMat 45 * (codeMat 187 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact

theorem step109wc201s2Dispatch :
    QuotientRankAtLeast (o201SourceU_wc ⟨2, by omega⟩) 14 := by
  have hP : Invertible (codeMat 410 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 229 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 410) (codeMat 229) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 410) (codeMat 229) hP hQ o55W 14
      step99_orbit55_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc201s2_contain hAct


private theorem step109wc201s3_QtInv :
    (codeMat 207 : Mat3).transpose⁻¹ = (codeMat 370 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 207 : Mat3).transpose * (codeMat 370 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc201s3_contain :
    (o201SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 346) (codeMat 207) o74W_mono := by
  change spanCodes [322, 132, 32, 22, 10, 1] ≤ actionW (codeMat 346) (codeMat 207) o74W_mono
  apply step109wc201_spanCodes_le_of_gens [322, 132, 32, 22, 10, 1]
    (actionW (codeMat 346) (codeMat 207) o74W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 411 ∈ o74W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [324, 192, 32, 20, 10, 1] 411 (by decide)
    have hact : actionA (codeMat 346) (codeMat 207) (codeMat 411) = codeMat 322 := by
      unfold actionA
      rw [step109wc201s3_QtInv]
      show (codeMat 346 : Mat3).transpose * codeMat 411 * (codeMat 370 : Mat3).transpose = codeMat 322
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 356 ∈ o74W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [324, 192, 32, 20, 10, 1] 356 (by decide)
    have hact : actionA (codeMat 346) (codeMat 207) (codeMat 356) = codeMat 132 := by
      unfold actionA
      rw [step109wc201s3_QtInv]
      show (codeMat 346 : Mat3).transpose * codeMat 356 * (codeMat 370 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ o74W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [324, 192, 32, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 346) (codeMat 207) (codeMat 1) = codeMat 32 := by
      unfold actionA
      rw [step109wc201s3_QtInv]
      show (codeMat 346 : Mat3).transpose * codeMat 1 * (codeMat 370 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 33 ∈ o74W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [324, 192, 32, 20, 10, 1] 33 (by decide)
    have hact : actionA (codeMat 346) (codeMat 207) (codeMat 33) = codeMat 22 := by
      unfold actionA
      rw [step109wc201s3_QtInv]
      show (codeMat 346 : Mat3).transpose * codeMat 33 * (codeMat 370 : Mat3).transpose = codeMat 22
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 42 ∈ o74W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [324, 192, 32, 20, 10, 1] 42 (by decide)
    have hact : actionA (codeMat 346) (codeMat 207) (codeMat 42) = codeMat 10 := by
      unfold actionA
      rw [step109wc201s3_QtInv]
      show (codeMat 346 : Mat3).transpose * codeMat 42 * (codeMat 370 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 63 ∈ o74W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [324, 192, 32, 20, 10, 1] 63 (by decide)
    have hact : actionA (codeMat 346) (codeMat 207) (codeMat 63) = codeMat 1 := by
      unfold actionA
      rw [step109wc201s3_QtInv]
      show (codeMat 346 : Mat3).transpose * codeMat 63 * (codeMat 370 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact

theorem step109wc201s3Dispatch :
    QuotientRankAtLeast (o201SourceU_wc ⟨3, by omega⟩) 14 := by
  have hP : Invertible (codeMat 346 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 207 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 346) (codeMat 207) o74W_mono) 14 :=
    @quotientRankAtLeast_action (codeMat 346) (codeMat 207) hP hQ o74W_mono 14
      orbit74_lb14_mono
  exact quotientRankAtLeast_mono step109wc201s3_contain hAct

private def step109wc201s4SrcT : Submodule F2 Mat3 := spanCodes [256, 160, 66, 20, 8, 1]

private theorem step109wc201s4SrcT_lb : QuotientRankAtLeast step109wc201s4SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step99_orbit56_lb14_unconditional
  have hle : step109wc201s4SrcT ≤ transposeW o56W := by
    unfold step109wc201s4SrcT transposeW
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

private theorem step109wc201s4_QtInv :
    (codeMat 311 : Mat3).transpose⁻¹ = (codeMat 307 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 311 : Mat3).transpose * (codeMat 307 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc201s4_contain :
    (o201SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 425) (codeMat 311) step109wc201s4SrcT := by
  change spanCodes [276, 132, 64, 32, 10, 1] ≤ actionW (codeMat 425) (codeMat 311) step109wc201s4SrcT
  apply step109wc201_spanCodes_le_of_gens [276, 132, 64, 32, 10, 1]
    (actionW (codeMat 425) (codeMat 311) step109wc201s4SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 227 ∈ step109wc201s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 227 (by decide)
    have hact : actionA (codeMat 425) (codeMat 311) (codeMat 227) = codeMat 276 := by
      unfold actionA
      rw [step109wc201s4_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 227 * (codeMat 307 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 28 ∈ step109wc201s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 28 (by decide)
    have hact : actionA (codeMat 425) (codeMat 311) (codeMat 28) = codeMat 132 := by
      unfold actionA
      rw [step109wc201s4_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 28 * (codeMat 307 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 9 ∈ step109wc201s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 9 (by decide)
    have hact : actionA (codeMat 425) (codeMat 311) (codeMat 9) = codeMat 64 := by
      unfold actionA
      rw [step109wc201s4_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 9 * (codeMat 307 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 511 ∈ step109wc201s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 511 (by decide)
    have hact : actionA (codeMat 425) (codeMat 311) (codeMat 511) = codeMat 32 := by
      unfold actionA
      rw [step109wc201s4_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 511 * (codeMat 307 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 74 ∈ step109wc201s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 74 (by decide)
    have hact : actionA (codeMat 425) (codeMat 311) (codeMat 74) = codeMat 10 := by
      unfold actionA
      rw [step109wc201s4_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 74 * (codeMat 307 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ step109wc201s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 1 (by decide)
    have hact : actionA (codeMat 425) (codeMat 311) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc201s4_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 1 * (codeMat 307 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact

theorem step109wc201s4Dispatch :
    QuotientRankAtLeast (o201SourceU_wc ⟨4, by omega⟩) 14 := by
  have hP : Invertible (codeMat 425 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 311 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 425) (codeMat 311) step109wc201s4SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 425) (codeMat 311) hP hQ step109wc201s4SrcT 14
      step109wc201s4SrcT_lb
  exact quotientRankAtLeast_mono step109wc201s4_contain hAct

private def step109wc201s5SrcT : Submodule F2 Mat3 := spanCodes [256, 160, 66, 20, 8, 1]

private theorem step109wc201s5SrcT_lb : QuotientRankAtLeast step109wc201s5SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step99_orbit56_lb14_unconditional
  have hle : step109wc201s5SrcT ≤ transposeW o56W := by
    unfold step109wc201s5SrcT transposeW
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

private theorem step109wc201s5_QtInv :
    (codeMat 95 : Mat3).transpose⁻¹ = (codeMat 244 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 95 : Mat3).transpose * (codeMat 244 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc201s5_contain :
    (o201SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 468) (codeMat 95) step109wc201s5SrcT := by
  change spanCodes [256, 132, 84, 32, 10, 1] ≤ actionW (codeMat 468) (codeMat 95) step109wc201s5SrcT
  apply step109wc201_spanCodes_le_of_gens [256, 132, 84, 32, 10, 1]
    (actionW (codeMat 468) (codeMat 95) step109wc201s5SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 1 ∈ step109wc201s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 1 (by decide)
    have hact : actionA (codeMat 468) (codeMat 95) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc201s5_QtInv]
      show (codeMat 468 : Mat3).transpose * codeMat 1 * (codeMat 244 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 74 ∈ step109wc201s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 74 (by decide)
    have hact : actionA (codeMat 468) (codeMat 95) (codeMat 74) = codeMat 132 := by
      unfold actionA
      rw [step109wc201s5_QtInv]
      show (codeMat 468 : Mat3).transpose * codeMat 74 * (codeMat 244 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 86 ∈ step109wc201s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 86 (by decide)
    have hact : actionA (codeMat 468) (codeMat 95) (codeMat 86) = codeMat 84 := by
      unfold actionA
      rw [step109wc201s5_QtInv]
      show (codeMat 468 : Mat3).transpose * codeMat 86 * (codeMat 244 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ step109wc201s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 8 (by decide)
    have hact : actionA (codeMat 468) (codeMat 95) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc201s5_QtInv]
      show (codeMat 468 : Mat3).transpose * codeMat 8 * (codeMat 244 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 227 ∈ step109wc201s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 227 (by decide)
    have hact : actionA (codeMat 468) (codeMat 95) (codeMat 227) = codeMat 10 := by
      unfold actionA
      rw [step109wc201s5_QtInv]
      show (codeMat 468 : Mat3).transpose * codeMat 227 * (codeMat 244 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 511 ∈ step109wc201s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 511 (by decide)
    have hact : actionA (codeMat 468) (codeMat 95) (codeMat 511) = codeMat 1 := by
      unfold actionA
      rw [step109wc201s5_QtInv]
      show (codeMat 468 : Mat3).transpose * codeMat 511 * (codeMat 244 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact

theorem step109wc201s5Dispatch :
    QuotientRankAtLeast (o201SourceU_wc ⟨5, by omega⟩) 14 := by
  have hP : Invertible (codeMat 468 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 95 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 468) (codeMat 95) step109wc201s5SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 468) (codeMat 95) hP hQ step109wc201s5SrcT 14
      step109wc201s5SrcT_lb
  exact quotientRankAtLeast_mono step109wc201s5_contain hAct


private theorem step109wc201s6_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc201s6_contain :
    (o201SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 106) (codeMat 140) orbit14W := by
  change spanCodes [260, 132, 80, 32, 8, 2, 1] ≤ actionW (codeMat 106) (codeMat 140) orbit14W
  apply step109wc201_spanCodes_le_of_gens [260, 132, 80, 32, 8, 2, 1]
    (actionW (codeMat 106) (codeMat 140) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 106) (codeMat 140) (codeMat 8) = codeMat 260 := by
      unfold actionA
      rw [step109wc201s6_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 352 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 352 (by decide)
    have hact : actionA (codeMat 106) (codeMat 140) (codeMat 352) = codeMat 132 := by
      unfold actionA
      rw [step109wc201s6_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 352 * (codeMat 98 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 148 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 148 (by decide)
    have hact : actionA (codeMat 106) (codeMat 140) (codeMat 148) = codeMat 80 := by
      unfold actionA
      rw [step109wc201s6_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 148 * (codeMat 98 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 106) (codeMat 140) (codeMat 1) = codeMat 32 := by
      unfold actionA
      rw [step109wc201s6_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 106) (codeMat 140) (codeMat 2) = codeMat 8 := by
      unfold actionA
      rw [step109wc201s6_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 106) (codeMat 140) (codeMat 256) = codeMat 2 := by
      unfold actionA
      rw [step109wc201s6_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 256 * (codeMat 98 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 106) (codeMat 140) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc201s6_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 128 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact

theorem step109wc201s6Dispatch :
    QuotientRankAtLeast (o201SourceU_wc ⟨6, by omega⟩) 12 := by
  have hP : Invertible (codeMat 106 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 106) (codeMat 140) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 106) (codeMat 140) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc201s6_contain hAct


private theorem step109wc201s7_QtInv :
    (codeMat 330 : Mat3).transpose⁻¹ = (codeMat 394 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 330 : Mat3).transpose * (codeMat 394 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc201s7_contain :
    (o201SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 84) (codeMat 330) flatW_3 := by
  change spanCodes [258, 128, 66, 32, 16, 10, 4, 1] ≤ actionW (codeMat 84) (codeMat 330) flatW_3
  apply step109wc201_spanCodes_le_of_gens [258, 128, 66, 32, 16, 10, 4, 1]
    (actionW (codeMat 84) (codeMat 330) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 68 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 68 (by decide)
    have hact : actionA (codeMat 84) (codeMat 330) (codeMat 68) = codeMat 258 := by
      unfold actionA
      rw [step109wc201s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 68 * (codeMat 394 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 330) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step109wc201s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 394 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 70 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 70 (by decide)
    have hact : actionA (codeMat 84) (codeMat 330) (codeMat 70) = codeMat 66 := by
      unfold actionA
      rw [step109wc201s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 70 * (codeMat 394 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 84) (codeMat 330) (codeMat 32) = codeMat 32 := by
      unfold actionA
      rw [step109wc201s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 32 * (codeMat 394 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 330) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step109wc201s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 394 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 112 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 112 (by decide)
    have hact : actionA (codeMat 84) (codeMat 330) (codeMat 112) = codeMat 10 := by
      unfold actionA
      rw [step109wc201s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 112 * (codeMat 394 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 330) (codeMat 256) = codeMat 4 := by
      unfold actionA
      rw [step109wc201s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 394 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 330) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step109wc201s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 394 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc201_codeMat_mem_actionW_of_witness hw hact

theorem step109wc201s7Dispatch :
    QuotientRankAtLeast (o201SourceU_wc ⟨7, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 330 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 330) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 330) hP hQ flatW_3 9
      flatSeed_3
  exact quotientRankAtLeast_mono step109wc201s7_contain hAct

theorem step109wc201_all_dispatch (i : Fin 8) :
    QuotientRankAtLeast (o201SourceU_wc i) (o201SourceLb_wc i) := by
  fin_cases i
  · exact step109wc201s0Dispatch
  · exact step109wc201s1Dispatch
  · exact step109wc201s2Dispatch
  · exact step109wc201s3Dispatch
  · exact step109wc201s4Dispatch
  · exact step109wc201s5Dispatch
  · exact step109wc201s6Dispatch
  · exact step109wc201s7Dispatch

theorem step109_orbit201_lb16_wc : QuotientRankAtLeast o201W_wc 16 :=
  o201Lb16_wc step109wc201_all_dispatch

end QiushiMatmul
