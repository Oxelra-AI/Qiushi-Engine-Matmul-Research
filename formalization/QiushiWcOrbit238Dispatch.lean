import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit238Consumer
import QiushiStep99Orbit76Dispatch
import QiushiStep99Orbit77Dispatch
import QiushiStep99Orbit56Dispatch
import QiushiWcOrbit57Dispatch
import QiushiStep99Orbit82Dispatch
import QiushiWcOrbit78Dispatch
import QiushiWcOrbit83Dispatch
import QiushiWcOrbit84Dispatch
import QiushiOrbit14FP

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc238_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc238_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc238s0_QtInv :
    (codeMat 474 : Mat3).transpose⁻¹ = (codeMat 395 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 474 : Mat3).transpose * (codeMat 395 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc238s0_contain :
    (o238SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 111) (codeMat 474) o76W := by
  change spanCodes [256, 136, 70, 38, 20, 1] ≤ actionW (codeMat 111) (codeMat 474) o76W
  apply step109wc238_spanCodes_le_of_gens [256, 136, 70, 38, 20, 1]
    (actionW (codeMat 111) (codeMat 474) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 288 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 111) (codeMat 474) (codeMat 288) = codeMat 256 := by
      unfold actionA
      rw [step109wc238s0_QtInv]
      show (codeMat 111 : Mat3).transpose * codeMat 288 * (codeMat 395 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 462 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 462 (by decide)
    have hact : actionA (codeMat 111) (codeMat 474) (codeMat 462) = codeMat 136 := by
      unfold actionA
      rw [step109wc238s0_QtInv]
      show (codeMat 111 : Mat3).transpose * codeMat 462 * (codeMat 395 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 368 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 368 (by decide)
    have hact : actionA (codeMat 111) (codeMat 474) (codeMat 368) = codeMat 70 := by
      unfold actionA
      rw [step109wc238s0_QtInv]
      show (codeMat 111 : Mat3).transpose * codeMat 368 * (codeMat 395 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 228 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 228 (by decide)
    have hact : actionA (codeMat 111) (codeMat 474) (codeMat 228) = codeMat 38 := by
      unfold actionA
      rw [step109wc238s0_QtInv]
      show (codeMat 111 : Mat3).transpose * codeMat 228 * (codeMat 395 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 319 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 319 (by decide)
    have hact : actionA (codeMat 111) (codeMat 474) (codeMat 319) = codeMat 20 := by
      unfold actionA
      rw [step109wc238s0_QtInv]
      show (codeMat 111 : Mat3).transpose * codeMat 319 * (codeMat 395 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 384 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 384 (by decide)
    have hact : actionA (codeMat 111) (codeMat 474) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step109wc238s0_QtInv]
      show (codeMat 111 : Mat3).transpose * codeMat 384 * (codeMat 395 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact

theorem step109wc238s0Dispatch :
    QuotientRankAtLeast (o238SourceU_wc ⟨0, by omega⟩) 15 := by
  have hP : Invertible (codeMat 111 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 474 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 111) (codeMat 474) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 111) (codeMat 474) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc238s0_contain hAct


private theorem step109wc238s1_QtInv :
    (codeMat 426 : Mat3).transpose⁻¹ = (codeMat 335 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 426 : Mat3).transpose * (codeMat 335 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc238s1_contain :
    (o238SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 122) (codeMat 426) o77W := by
  change spanCodes [266, 136, 76, 44, 20, 1] ≤ actionW (codeMat 122) (codeMat 426) o77W
  apply step109wc238_spanCodes_le_of_gens [266, 136, 76, 44, 20, 1]
    (actionW (codeMat 122) (codeMat 426) o77W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 244 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 244 (by decide)
    have hact : actionA (codeMat 122) (codeMat 426) (codeMat 244) = codeMat 266 := by
      unfold actionA
      rw [step109wc238s1_QtInv]
      show (codeMat 122 : Mat3).transpose * codeMat 244 * (codeMat 335 : Mat3).transpose = codeMat 266
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 367 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 367 (by decide)
    have hact : actionA (codeMat 122) (codeMat 426) (codeMat 367) = codeMat 136 := by
      unfold actionA
      rw [step109wc238s1_QtInv]
      show (codeMat 122 : Mat3).transpose * codeMat 367 * (codeMat 335 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 272 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 272 (by decide)
    have hact : actionA (codeMat 122) (codeMat 426) (codeMat 272) = codeMat 76 := by
      unfold actionA
      rw [step109wc238s1_QtInv]
      show (codeMat 122 : Mat3).transpose * codeMat 272 * (codeMat 335 : Mat3).transpose = codeMat 76
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 388 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 388 (by decide)
    have hact : actionA (codeMat 122) (codeMat 426) (codeMat 388) = codeMat 44 := by
      unfold actionA
      rw [step109wc238s1_QtInv]
      show (codeMat 122 : Mat3).transpose * codeMat 388 * (codeMat 335 : Mat3).transpose = codeMat 44
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 389 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 389 (by decide)
    have hact : actionA (codeMat 122) (codeMat 426) (codeMat 389) = codeMat 20 := by
      unfold actionA
      rw [step109wc238s1_QtInv]
      show (codeMat 122 : Mat3).transpose * codeMat 389 * (codeMat 335 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 122) (codeMat 426) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc238s1_QtInv]
      show (codeMat 122 : Mat3).transpose * codeMat 128 * (codeMat 335 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact

theorem step109wc238s1Dispatch :
    QuotientRankAtLeast (o238SourceU_wc ⟨1, by omega⟩) 15 := by
  have hP : Invertible (codeMat 122 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 426 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 122) (codeMat 426) o77W) 15 :=
    @quotientRankAtLeast_action (codeMat 122) (codeMat 426) hP hQ o77W 15
      step99_orbit77_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc238s1_contain hAct


private theorem step109wc238s2_QtInv :
    (codeMat 267 : Mat3).transpose⁻¹ = (codeMat 282 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 267 : Mat3).transpose * (codeMat 282 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc238s2_contain :
    (o238SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 473) (codeMat 267) o56W := by
  change spanCodes [292, 136, 96, 20, 2, 1] ≤ actionW (codeMat 473) (codeMat 267) o56W
  apply step109wc238_spanCodes_le_of_gens [292, 136, 96, 20, 2, 1]
    (actionW (codeMat 473) (codeMat 267) o56W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 256 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 473) (codeMat 267) (codeMat 256) = codeMat 292 := by
      unfold actionA
      rw [step109wc238s2_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 256 * (codeMat 282 : Mat3).transpose = codeMat 292
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 83 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 83 (by decide)
    have hact : actionA (codeMat 473) (codeMat 267) (codeMat 83) = codeMat 136 := by
      unfold actionA
      rw [step109wc238s2_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 83 * (codeMat 282 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 252 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 252 (by decide)
    have hact : actionA (codeMat 473) (codeMat 267) (codeMat 252) = codeMat 96 := by
      unfold actionA
      rw [step109wc238s2_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 252 * (codeMat 282 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 13 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 13 (by decide)
    have hact : actionA (codeMat 473) (codeMat 267) (codeMat 13) = codeMat 20 := by
      unfold actionA
      rw [step109wc238s2_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 13 * (codeMat 282 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 473) (codeMat 267) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step109wc238s2_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 1 * (codeMat 282 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 473) (codeMat 267) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step109wc238s2_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 3 * (codeMat 282 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact

theorem step109wc238s2Dispatch :
    QuotientRankAtLeast (o238SourceU_wc ⟨2, by omega⟩) 14 := by
  have hP : Invertible (codeMat 473 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 473) (codeMat 267) o56W) 14 :=
    @quotientRankAtLeast_action (codeMat 473) (codeMat 267) hP hQ o56W 14
      step99_orbit56_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc238s2_contain hAct


private theorem step109wc238s3_QtInv :
    (codeMat 159 : Mat3).transpose⁻¹ = (codeMat 230 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 159 : Mat3).transpose * (codeMat 230 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc238s3_contain :
    (o238SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 377) (codeMat 159) o57W_wc := by
  change spanCodes [290, 136, 96, 16, 4, 1] ≤ actionW (codeMat 377) (codeMat 159) o57W_wc
  apply step109wc238_spanCodes_le_of_gens [290, 136, 96, 16, 4, 1]
    (actionW (codeMat 377) (codeMat 159) o57W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 14 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 14 (by decide)
    have hact : actionA (codeMat 377) (codeMat 159) (codeMat 14) = codeMat 290 := by
      unfold actionA
      rw [step109wc238s3_QtInv]
      show (codeMat 377 : Mat3).transpose * codeMat 14 * (codeMat 230 : Mat3).transpose = codeMat 290
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 287 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 287 (by decide)
    have hact : actionA (codeMat 377) (codeMat 159) (codeMat 287) = codeMat 136 := by
      unfold actionA
      rw [step109wc238s3_QtInv]
      show (codeMat 377 : Mat3).transpose * codeMat 287 * (codeMat 230 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 139 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 139 (by decide)
    have hact : actionA (codeMat 377) (codeMat 159) (codeMat 139) = codeMat 96 := by
      unfold actionA
      rw [step109wc238s3_QtInv]
      show (codeMat 377 : Mat3).transpose * codeMat 139 * (codeMat 230 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 504 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 504 (by decide)
    have hact : actionA (codeMat 377) (codeMat 159) (codeMat 504) = codeMat 16 := by
      unfold actionA
      rw [step109wc238s3_QtInv]
      show (codeMat 377 : Mat3).transpose * codeMat 504 * (codeMat 230 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 377) (codeMat 159) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step109wc238s3_QtInv]
      show (codeMat 377 : Mat3).transpose * codeMat 1 * (codeMat 230 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 377) (codeMat 159) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step109wc238s3_QtInv]
      show (codeMat 377 : Mat3).transpose * codeMat 3 * (codeMat 230 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact

theorem step109wc238s3Dispatch :
    QuotientRankAtLeast (o238SourceU_wc ⟨3, by omega⟩) 14 := by
  have hP : Invertible (codeMat 377 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 159 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 377) (codeMat 159) o57W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 377) (codeMat 159) hP hQ o57W_wc 14
      step109_orbit57_lb14_wc
  exact quotientRankAtLeast_mono step109wc238s3_contain hAct

private def step109wc238s4SrcT : Submodule F2 Mat3 := spanCodes [256, 160, 66, 20, 8, 1]

private theorem step109wc238s4SrcT_lb : QuotientRankAtLeast step109wc238s4SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step99_orbit56_lb14_unconditional
  have hle : step109wc238s4SrcT ≤ transposeW o56W := by
    unfold step109wc238s4SrcT transposeW
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

private theorem step109wc238s4_QtInv :
    (codeMat 179 : Mat3).transpose⁻¹ = (codeMat 421 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 179 : Mat3).transpose * (codeMat 421 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc238s4_contain :
    (o238SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 346) (codeMat 179) step109wc238s4SrcT := by
  change spanCodes [294, 128, 96, 20, 8, 1] ≤ actionW (codeMat 346) (codeMat 179) step109wc238s4SrcT
  apply step109wc238_spanCodes_le_of_gens [294, 128, 96, 20, 8, 1]
    (actionW (codeMat 346) (codeMat 179) step109wc238s4SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 189 ∈ step109wc238s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 189 (by decide)
    have hact : actionA (codeMat 346) (codeMat 179) (codeMat 189) = codeMat 294 := by
      unfold actionA
      rw [step109wc238s4_QtInv]
      show (codeMat 346 : Mat3).transpose * codeMat 189 * (codeMat 421 : Mat3).transpose = codeMat 294
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 511 ∈ step109wc238s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 511 (by decide)
    have hact : actionA (codeMat 346) (codeMat 179) (codeMat 511) = codeMat 128 := by
      unfold actionA
      rw [step109wc238s4_QtInv]
      show (codeMat 346 : Mat3).transpose * codeMat 511 * (codeMat 421 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 75 ∈ step109wc238s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 75 (by decide)
    have hact : actionA (codeMat 346) (codeMat 179) (codeMat 75) = codeMat 96 := by
      unfold actionA
      rw [step109wc238s4_QtInv]
      show (codeMat 346 : Mat3).transpose * codeMat 75 * (codeMat 421 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 21 ∈ step109wc238s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 21 (by decide)
    have hact : actionA (codeMat 346) (codeMat 179) (codeMat 21) = codeMat 20 := by
      unfold actionA
      rw [step109wc238s4_QtInv]
      show (codeMat 346 : Mat3).transpose * codeMat 21 * (codeMat 421 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ step109wc238s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 1 (by decide)
    have hact : actionA (codeMat 346) (codeMat 179) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step109wc238s4_QtInv]
      show (codeMat 346 : Mat3).transpose * codeMat 1 * (codeMat 421 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 9 ∈ step109wc238s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 9 (by decide)
    have hact : actionA (codeMat 346) (codeMat 179) (codeMat 9) = codeMat 1 := by
      unfold actionA
      rw [step109wc238s4_QtInv]
      show (codeMat 346 : Mat3).transpose * codeMat 9 * (codeMat 421 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact

theorem step109wc238s4Dispatch :
    QuotientRankAtLeast (o238SourceU_wc ⟨4, by omega⟩) 14 := by
  have hP : Invertible (codeMat 346 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 179 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 346) (codeMat 179) step109wc238s4SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 346) (codeMat 179) hP hQ step109wc238s4SrcT 14
      step109wc238s4SrcT_lb
  exact quotientRankAtLeast_mono step109wc238s4_contain hAct


private theorem step109wc238s5_QtInv :
    (codeMat 226 : Mat3).transpose⁻¹ = (codeMat 141 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 226 : Mat3).transpose * (codeMat 141 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc238s5_contain :
    (o238SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 307) (codeMat 226) o82W := by
  change spanCodes [294, 134, 96, 20, 14, 1] ≤ actionW (codeMat 307) (codeMat 226) o82W
  apply step109wc238_spanCodes_le_of_gens [294, 134, 96, 20, 14, 1]
    (actionW (codeMat 307) (codeMat 226) o82W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 495 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 495 (by decide)
    have hact : actionA (codeMat 307) (codeMat 226) (codeMat 495) = codeMat 294 := by
      unfold actionA
      rw [step109wc238s5_QtInv]
      show (codeMat 307 : Mat3).transpose * codeMat 495 * (codeMat 141 : Mat3).transpose = codeMat 294
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 191 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 191 (by decide)
    have hact : actionA (codeMat 307) (codeMat 226) (codeMat 191) = codeMat 134 := by
      unfold actionA
      rw [step109wc238s5_QtInv]
      show (codeMat 307 : Mat3).transpose * codeMat 191 * (codeMat 141 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 400 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 400 (by decide)
    have hact : actionA (codeMat 307) (codeMat 226) (codeMat 400) = codeMat 96 := by
      unfold actionA
      rw [step109wc238s5_QtInv]
      show (codeMat 307 : Mat3).transpose * codeMat 400 * (codeMat 141 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 506 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 506 (by decide)
    have hact : actionA (codeMat 307) (codeMat 226) (codeMat 506) = codeMat 20 := by
      unfold actionA
      rw [step109wc238s5_QtInv]
      show (codeMat 307 : Mat3).transpose * codeMat 506 * (codeMat 141 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 223 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 223 (by decide)
    have hact : actionA (codeMat 307) (codeMat 226) (codeMat 223) = codeMat 14 := by
      unfold actionA
      rw [step109wc238s5_QtInv]
      show (codeMat 307 : Mat3).transpose * codeMat 223 * (codeMat 141 : Mat3).transpose = codeMat 14
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 292 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 292 (by decide)
    have hact : actionA (codeMat 307) (codeMat 226) (codeMat 292) = codeMat 1 := by
      unfold actionA
      rw [step109wc238s5_QtInv]
      show (codeMat 307 : Mat3).transpose * codeMat 292 * (codeMat 141 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact

theorem step109wc238s5Dispatch :
    QuotientRankAtLeast (o238SourceU_wc ⟨5, by omega⟩) 14 := by
  have hP : Invertible (codeMat 307 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 226 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 307) (codeMat 226) o82W) 14 :=
    @quotientRankAtLeast_action (codeMat 307) (codeMat 226) hP hQ o82W 14
      step99_orbit82_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc238s5_contain hAct

private def step109wc238s6SrcT : Submodule F2 Mat3 := spanCodes [272, 132, 66, 34, 8, 1]

private theorem step109wc238s6SrcT_lb : QuotientRankAtLeast step109wc238s6SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step109_orbit57_lb14_wc
  have hle : step109wc238s6SrcT ≤ transposeW o57W_wc := by
    unfold step109wc238s6SrcT transposeW
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

private theorem step109wc238s6_QtInv :
    (codeMat 419 : Mat3).transpose⁻¹ = (codeMat 183 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 419 : Mat3).transpose * (codeMat 183 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc238s6_contain :
    (o238SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 229) (codeMat 419) step109wc238s6SrcT := by
  change spanCodes [262, 136, 64, 32, 20, 1] ≤ actionW (codeMat 229) (codeMat 419) step109wc238s6SrcT
  apply step109wc238_spanCodes_le_of_gens [262, 136, 64, 32, 20, 1]
    (actionW (codeMat 229) (codeMat 419) step109wc238s6SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 43 ∈ step109wc238s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 66, 34, 8, 1] 43 (by decide)
    have hact : actionA (codeMat 229) (codeMat 419) (codeMat 43) = codeMat 262 := by
      unfold actionA
      rw [step109wc238s6_QtInv]
      show (codeMat 229 : Mat3).transpose * codeMat 43 * (codeMat 183 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 97 ∈ step109wc238s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 66, 34, 8, 1] 97 (by decide)
    have hact : actionA (codeMat 229) (codeMat 419) (codeMat 97) = codeMat 136 := by
      unfold actionA
      rw [step109wc238s6_QtInv]
      show (codeMat 229 : Mat3).transpose * codeMat 97 * (codeMat 183 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ step109wc238s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 66, 34, 8, 1] 8 (by decide)
    have hact : actionA (codeMat 229) (codeMat 419) (codeMat 8) = codeMat 64 := by
      unfold actionA
      rw [step109wc238s6_QtInv]
      show (codeMat 229 : Mat3).transpose * codeMat 8 * (codeMat 183 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 438 ∈ step109wc238s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 66, 34, 8, 1] 438 (by decide)
    have hact : actionA (codeMat 229) (codeMat 419) (codeMat 438) = codeMat 32 := by
      unfold actionA
      rw [step109wc238s6_QtInv]
      show (codeMat 229 : Mat3).transpose * codeMat 438 * (codeMat 183 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 347 ∈ step109wc238s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 66, 34, 8, 1] 347 (by decide)
    have hact : actionA (codeMat 229) (codeMat 419) (codeMat 347) = codeMat 20 := by
      unfold actionA
      rw [step109wc238s6_QtInv]
      show (codeMat 229 : Mat3).transpose * codeMat 347 * (codeMat 183 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 9 ∈ step109wc238s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 66, 34, 8, 1] 9 (by decide)
    have hact : actionA (codeMat 229) (codeMat 419) (codeMat 9) = codeMat 1 := by
      unfold actionA
      rw [step109wc238s6_QtInv]
      show (codeMat 229 : Mat3).transpose * codeMat 9 * (codeMat 183 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact

theorem step109wc238s6Dispatch :
    QuotientRankAtLeast (o238SourceU_wc ⟨6, by omega⟩) 14 := by
  have hP : Invertible (codeMat 229 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 419 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 229) (codeMat 419) step109wc238s6SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 229) (codeMat 419) hP hQ step109wc238s6SrcT 14
      step109wc238s6SrcT_lb
  exact quotientRankAtLeast_mono step109wc238s6_contain hAct


private theorem step109wc238s7_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc238s7_contain :
    (o238SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 225) (codeMat 161) o78W_wc := by
  change spanCodes [258, 136, 68, 36, 20, 1] ≤ actionW (codeMat 225) (codeMat 161) o78W_wc
  apply step109wc238_spanCodes_le_of_gens [258, 136, 68, 36, 20, 1]
    (actionW (codeMat 225) (codeMat 161) o78W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 20 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 20 (by decide)
    have hact : actionA (codeMat 225) (codeMat 161) (codeMat 20) = codeMat 258 := by
      unfold actionA
      rw [step109wc238s7_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 20 * (codeMat 161 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 97 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 97 (by decide)
    have hact : actionA (codeMat 225) (codeMat 161) (codeMat 97) = codeMat 136 := by
      unfold actionA
      rw [step109wc238s7_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 97 * (codeMat 161 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 10 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 225) (codeMat 161) (codeMat 10) = codeMat 68 := by
      unfold actionA
      rw [step109wc238s7_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 10 * (codeMat 161 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 225) (codeMat 161) (codeMat 128) = codeMat 36 := by
      unfold actionA
      rw [step109wc238s7_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 128 * (codeMat 161 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 262 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 262 (by decide)
    have hact : actionA (codeMat 225) (codeMat 161) (codeMat 262) = codeMat 20 := by
      unfold actionA
      rw [step109wc238s7_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 262 * (codeMat 161 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc238s7_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact

theorem step109wc238s7Dispatch :
    QuotientRankAtLeast (o238SourceU_wc ⟨7, by omega⟩) 14 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 161) o78W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 161) hP hQ o78W_wc 14
      step109_orbit78_lb14_wc
  exact quotientRankAtLeast_mono step109wc238s7_contain hAct


private theorem step109wc238s8_QtInv :
    (codeMat 239 : Mat3).transpose⁻¹ = (codeMat 351 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 239 : Mat3).transpose * (codeMat 351 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc238s8_contain :
    (o238SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 187) (codeMat 239) o83W_wc := by
  change spanCodes [268, 136, 74, 42, 20, 1] ≤ actionW (codeMat 187) (codeMat 239) o83W_wc
  apply step109wc238_spanCodes_le_of_gens [268, 136, 74, 42, 20, 1]
    (actionW (codeMat 187) (codeMat 239) o83W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 280 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 280 (by decide)
    have hact : actionA (codeMat 187) (codeMat 239) (codeMat 280) = codeMat 268 := by
      unfold actionA
      rw [step109wc238s8_QtInv]
      show (codeMat 187 : Mat3).transpose * codeMat 280 * (codeMat 351 : Mat3).transpose = codeMat 268
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 493 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 493 (by decide)
    have hact : actionA (codeMat 187) (codeMat 239) (codeMat 493) = codeMat 136 := by
      unfold actionA
      rw [step109wc238s8_QtInv]
      show (codeMat 187 : Mat3).transpose * codeMat 493 * (codeMat 351 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 186 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 186 (by decide)
    have hact : actionA (codeMat 187) (codeMat 239) (codeMat 186) = codeMat 74 := by
      unfold actionA
      rw [step109wc238s8_QtInv]
      show (codeMat 187 : Mat3).transpose * codeMat 186 * (codeMat 351 : Mat3).transpose = codeMat 74
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 69 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 187) (codeMat 239) (codeMat 69) = codeMat 42 := by
      unfold actionA
      rw [step109wc238s8_QtInv]
      show (codeMat 187 : Mat3).transpose * codeMat 69 * (codeMat 351 : Mat3).transpose = codeMat 42
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 387 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 387 (by decide)
    have hact : actionA (codeMat 187) (codeMat 239) (codeMat 387) = codeMat 20 := by
      unfold actionA
      rw [step109wc238s8_QtInv]
      show (codeMat 187 : Mat3).transpose * codeMat 387 * (codeMat 351 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 455 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 455 (by decide)
    have hact : actionA (codeMat 187) (codeMat 239) (codeMat 455) = codeMat 1 := by
      unfold actionA
      rw [step109wc238s8_QtInv]
      show (codeMat 187 : Mat3).transpose * codeMat 455 * (codeMat 351 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact

theorem step109wc238s8Dispatch :
    QuotientRankAtLeast (o238SourceU_wc ⟨8, by omega⟩) 14 := by
  have hP : Invertible (codeMat 187 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 239 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 187) (codeMat 239) o83W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 187) (codeMat 239) hP hQ o83W_wc 14
      step109_orbit83_lb14_wc
  exact quotientRankAtLeast_mono step109wc238s8_contain hAct


private theorem step109wc238s9_QtInv :
    (codeMat 190 : Mat3).transpose⁻¹ = (codeMat 355 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 190 : Mat3).transpose * (codeMat 355 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc238s9_contain :
    (o238SourceU_wc ⟨9, by omega⟩) ≤ actionW (codeMat 102) (codeMat 190) o84W_wc := by
  change spanCodes [264, 136, 78, 46, 20, 1] ≤ actionW (codeMat 102) (codeMat 190) o84W_wc
  apply step109wc238_spanCodes_le_of_gens [264, 136, 78, 46, 20, 1]
    (actionW (codeMat 102) (codeMat 190) o84W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 10 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 102) (codeMat 190) (codeMat 10) = codeMat 264 := by
      unfold actionA
      rw [step109wc238s9_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 10 * (codeMat 355 : Mat3).transpose = codeMat 264
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 42 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 42 (by decide)
    have hact : actionA (codeMat 102) (codeMat 190) (codeMat 42) = codeMat 136 := by
      unfold actionA
      rw [step109wc238s9_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 42 * (codeMat 355 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 258 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 258 (by decide)
    have hact : actionA (codeMat 102) (codeMat 190) (codeMat 258) = codeMat 78 := by
      unfold actionA
      rw [step109wc238s9_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 258 * (codeMat 355 : Mat3).transpose = codeMat 78
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 265 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 265 (by decide)
    have hact : actionA (codeMat 102) (codeMat 190) (codeMat 265) = codeMat 46 := by
      unfold actionA
      rw [step109wc238s9_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 265 * (codeMat 355 : Mat3).transpose = codeMat 46
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 255 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 255 (by decide)
    have hact : actionA (codeMat 102) (codeMat 190) (codeMat 255) = codeMat 20 := by
      unfold actionA
      rw [step109wc238s9_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 255 * (codeMat 355 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 102) (codeMat 190) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc238s9_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 128 * (codeMat 355 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact

theorem step109wc238s9Dispatch :
    QuotientRankAtLeast (o238SourceU_wc ⟨9, by omega⟩) 14 := by
  have hP : Invertible (codeMat 102 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 190 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 102) (codeMat 190) o84W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 102) (codeMat 190) hP hQ o84W_wc 14
      step109_orbit84_lb14_wc
  exact quotientRankAtLeast_mono step109wc238s9_contain hAct


private theorem step109wc238s10_QtInv :
    (codeMat 102 : Mat3).transpose⁻¹ = (codeMat 156 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 102 : Mat3).transpose * (codeMat 156 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc238s10_contain :
    (o238SourceU_wc ⟨10, by omega⟩) ≤ actionW (codeMat 94) (codeMat 102) orbit14W := by
  change spanCodes [288, 130, 96, 18, 10, 6, 1] ≤ actionW (codeMat 94) (codeMat 102) orbit14W
  apply step109wc238_spanCodes_le_of_gens [288, 130, 96, 18, 10, 6, 1]
    (actionW (codeMat 94) (codeMat 102) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 94) (codeMat 102) (codeMat 3) = codeMat 288 := by
      unfold actionA
      rw [step109wc238s10_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 3 * (codeMat 156 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 9 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 9 (by decide)
    have hact : actionA (codeMat 94) (codeMat 102) (codeMat 9) = codeMat 130 := by
      unfold actionA
      rw [step109wc238s10_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 9 * (codeMat 156 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 508 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 508 (by decide)
    have hact : actionA (codeMat 94) (codeMat 102) (codeMat 508) = codeMat 96 := by
      unfold actionA
      rw [step109wc238s10_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 508 * (codeMat 156 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 94) (codeMat 102) (codeMat 8) = codeMat 18 := by
      unfold actionA
      rw [step109wc238s10_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 8 * (codeMat 156 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 352 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 352 (by decide)
    have hact : actionA (codeMat 94) (codeMat 102) (codeMat 352) = codeMat 10 := by
      unfold actionA
      rw [step109wc238s10_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 352 * (codeMat 156 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 94) (codeMat 102) (codeMat 128) = codeMat 6 := by
      unfold actionA
      rw [step109wc238s10_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 128 * (codeMat 156 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 94) (codeMat 102) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc238s10_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 256 * (codeMat 156 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact

theorem step109wc238s10Dispatch :
    QuotientRankAtLeast (o238SourceU_wc ⟨10, by omega⟩) 12 := by
  have hP : Invertible (codeMat 94 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 102 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 94) (codeMat 102) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 94) (codeMat 102) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc238s10_contain hAct


private theorem step109wc238s11_QtInv :
    (codeMat 417 : Mat3).transpose⁻¹ = (codeMat 177 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 417 : Mat3).transpose * (codeMat 177 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc238s11_contain :
    (o238SourceU_wc ⟨11, by omega⟩) ≤ actionW (codeMat 334) (codeMat 417) orbit14W := by
  change spanCodes [260, 130, 66, 34, 20, 10, 1] ≤ actionW (codeMat 334) (codeMat 417) orbit14W
  apply step109wc238_spanCodes_le_of_gens [260, 130, 66, 34, 20, 10, 1]
    (actionW (codeMat 334) (codeMat 417) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 334) (codeMat 417) (codeMat 384) = codeMat 260 := by
      unfold actionA
      rw [step109wc238s11_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 384 * (codeMat 177 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 334) (codeMat 417) (codeMat 256) = codeMat 130 := by
      unfold actionA
      rw [step109wc238s11_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 256 * (codeMat 177 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 104 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 104 (by decide)
    have hact : actionA (codeMat 334) (codeMat 417) (codeMat 104) = codeMat 66 := by
      unfold actionA
      rw [step109wc238s11_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 104 * (codeMat 177 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 406 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 406 (by decide)
    have hact : actionA (codeMat 334) (codeMat 417) (codeMat 406) = codeMat 34 := by
      unfold actionA
      rw [step109wc238s11_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 406 * (codeMat 177 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 276 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 276 (by decide)
    have hact : actionA (codeMat 334) (codeMat 417) (codeMat 276) = codeMat 20 := by
      unfold actionA
      rw [step109wc238s11_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 276 * (codeMat 177 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 105 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 105 (by decide)
    have hact : actionA (codeMat 334) (codeMat 417) (codeMat 105) = codeMat 10 := by
      unfold actionA
      rw [step109wc238s11_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 105 * (codeMat 177 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 334) (codeMat 417) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc238s11_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 8 * (codeMat 177 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc238_codeMat_mem_actionW_of_witness hw hact

theorem step109wc238s11Dispatch :
    QuotientRankAtLeast (o238SourceU_wc ⟨11, by omega⟩) 12 := by
  have hP : Invertible (codeMat 334 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 334) (codeMat 417) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 334) (codeMat 417) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc238s11_contain hAct

theorem step109wc238_all_dispatch (i : Fin 12) :
    QuotientRankAtLeast (o238SourceU_wc i) (o238SourceLb_wc i) := by
  fin_cases i
  · exact step109wc238s0Dispatch
  · exact step109wc238s1Dispatch
  · exact step109wc238s2Dispatch
  · exact step109wc238s3Dispatch
  · exact step109wc238s4Dispatch
  · exact step109wc238s5Dispatch
  · exact step109wc238s6Dispatch
  · exact step109wc238s7Dispatch
  · exact step109wc238s8Dispatch
  · exact step109wc238s9Dispatch
  · exact step109wc238s10Dispatch
  · exact step109wc238s11Dispatch

theorem step109_orbit238_lb16_wc : QuotientRankAtLeast o238W_wc 16 :=
  o238Lb16_wc step109wc238_all_dispatch

end QiushiMatmul
