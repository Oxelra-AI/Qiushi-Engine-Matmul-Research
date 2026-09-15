import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit164Consumer
import QiushiWcOrbit72Dispatch
import QiushiStep99Orbit77Dispatch
import QiushiStep99Orbit76Dispatch
import QiushiWcOrbit80Dispatch
import QiushiStep99Orbit55Dispatch
import QiushiStep99Orbit56Dispatch
import QiushiWcOrbit78Dispatch
import QiushiWcOrbit36Dispatch
import QiushiMonoOrbit44From14
import QiushiOrbit14FP

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc164_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc164_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc164s0_QtInv :
    (codeMat 468 : Mat3).transpose⁻¹ = (codeMat 87 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 468 : Mat3).transpose * (codeMat 87 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc164s0_contain :
    (o164SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 395) (codeMat 468) o72W_wc := by
  change spanCodes [256, 70, 38, 20, 10, 1] ≤ actionW (codeMat 395) (codeMat 468) o72W_wc
  apply step109wc164_spanCodes_le_of_gens [256, 70, 38, 20, 10, 1]
    (actionW (codeMat 395) (codeMat 468) o72W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 365 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 365 (by decide)
    have hact : actionA (codeMat 395) (codeMat 468) (codeMat 365) = codeMat 256 := by
      unfold actionA
      rw [step109wc164s0_QtInv]
      show (codeMat 395 : Mat3).transpose * codeMat 365 * (codeMat 87 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 316 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 316 (by decide)
    have hact : actionA (codeMat 395) (codeMat 468) (codeMat 316) = codeMat 70 := by
      unfold actionA
      rw [step109wc164s0_QtInv]
      show (codeMat 395 : Mat3).transpose * codeMat 316 * (codeMat 87 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 53 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 53 (by decide)
    have hact : actionA (codeMat 395) (codeMat 468) (codeMat 53) = codeMat 38 := by
      unfold actionA
      rw [step109wc164s0_QtInv]
      show (codeMat 395 : Mat3).transpose * codeMat 53 * (codeMat 87 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 30 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 30 (by decide)
    have hact : actionA (codeMat 395) (codeMat 468) (codeMat 30) = codeMat 20 := by
      unfold actionA
      rw [step109wc164s0_QtInv]
      show (codeMat 395 : Mat3).transpose * codeMat 30 * (codeMat 87 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 20 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 20 (by decide)
    have hact : actionA (codeMat 395) (codeMat 468) (codeMat 20) = codeMat 10 := by
      unfold actionA
      rw [step109wc164s0_QtInv]
      show (codeMat 395 : Mat3).transpose * codeMat 20 * (codeMat 87 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 395) (codeMat 468) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc164s0_QtInv]
      show (codeMat 395 : Mat3).transpose * codeMat 32 * (codeMat 87 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact

theorem step109wc164s0Dispatch :
    QuotientRankAtLeast (o164SourceU_wc ⟨0, by omega⟩) 15 := by
  have hP : Invertible (codeMat 395 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 468 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 395) (codeMat 468) o72W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 395) (codeMat 468) hP hQ o72W_wc 15
      step109_orbit72_lb15_wc
  exact quotientRankAtLeast_mono step109wc164s0_contain hAct


private theorem step109wc164s1_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc164s1_contain :
    (o164SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 84) (codeMat 140) o77W := by
  change spanCodes [256, 130, 96, 20, 10, 1] ≤ actionW (codeMat 84) (codeMat 140) o77W
  apply step109wc164_spanCodes_le_of_gens [256, 130, 96, 20, 10, 1]
    (actionW (codeMat 84) (codeMat 140) o77W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 1 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc164s1_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 260 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 260) = codeMat 130 := by
      unfold actionA
      rw [step109wc164s1_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 260 * (codeMat 98 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 10 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 10) = codeMat 96 := by
      unfold actionA
      rw [step109wc164s1_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 10 * (codeMat 98 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 96 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 96 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 96) = codeMat 20 := by
      unfold actionA
      rw [step109wc164s1_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 96 * (codeMat 98 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 272 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 272 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 272) = codeMat 10 := by
      unfold actionA
      rw [step109wc164s1_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 272 * (codeMat 98 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc164s1_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact

theorem step109wc164s1Dispatch :
    QuotientRankAtLeast (o164SourceU_wc ⟨1, by omega⟩) 15 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 140) o77W) 15 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 140) hP hQ o77W 15
      step99_orbit77_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc164s1_contain hAct


private theorem step109wc164s2_QtInv :
    (codeMat 212 : Mat3).transpose⁻¹ = (codeMat 86 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 212 : Mat3).transpose * (codeMat 86 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc164s2_contain :
    (o164SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 444) (codeMat 212) o76W := by
  change spanCodes [256, 132, 96, 20, 10, 1] ≤ actionW (codeMat 444) (codeMat 212) o76W
  apply step109wc164_spanCodes_le_of_gens [256, 132, 96, 20, 10, 1]
    (actionW (codeMat 444) (codeMat 212) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 1 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 444) (codeMat 212) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc164s2_QtInv]
      show (codeMat 444 : Mat3).transpose * codeMat 1 * (codeMat 86 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 78 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 444) (codeMat 212) (codeMat 78) = codeMat 132 := by
      unfold actionA
      rw [step109wc164s2_QtInv]
      show (codeMat 444 : Mat3).transpose * codeMat 78 * (codeMat 86 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 69 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 444) (codeMat 212) (codeMat 69) = codeMat 96 := by
      unfold actionA
      rw [step109wc164s2_QtInv]
      show (codeMat 444 : Mat3).transpose * codeMat 69 * (codeMat 86 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 462 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 462 (by decide)
    have hact : actionA (codeMat 444) (codeMat 212) (codeMat 462) = codeMat 20 := by
      unfold actionA
      rw [step109wc164s2_QtInv]
      show (codeMat 444 : Mat3).transpose * codeMat 462 * (codeMat 86 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 180 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 180 (by decide)
    have hact : actionA (codeMat 444) (codeMat 212) (codeMat 180) = codeMat 10 := by
      unfold actionA
      rw [step109wc164s2_QtInv]
      show (codeMat 444 : Mat3).transpose * codeMat 180 * (codeMat 86 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 288 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 444) (codeMat 212) (codeMat 288) = codeMat 1 := by
      unfold actionA
      rw [step109wc164s2_QtInv]
      show (codeMat 444 : Mat3).transpose * codeMat 288 * (codeMat 86 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact

theorem step109wc164s2Dispatch :
    QuotientRankAtLeast (o164SourceU_wc ⟨2, by omega⟩) 15 := by
  have hP : Invertible (codeMat 444 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 212 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 444) (codeMat 212) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 444) (codeMat 212) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc164s2_contain hAct


private theorem step109wc164s3_QtInv :
    (codeMat 159 : Mat3).transpose⁻¹ = (codeMat 230 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 159 : Mat3).transpose * (codeMat 230 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc164s3_contain :
    (o164SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 116) (codeMat 159) o80W_wc := by
  change spanCodes [256, 162, 96, 20, 10, 1] ≤ actionW (codeMat 116) (codeMat 159) o80W_wc
  apply step109wc164_spanCodes_le_of_gens [256, 162, 96, 20, 10, 1]
    (actionW (codeMat 116) (codeMat 159) o80W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 1 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 116) (codeMat 159) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc164s3_QtInv]
      show (codeMat 116 : Mat3).transpose * codeMat 1 * (codeMat 230 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 462 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 462 (by decide)
    have hact : actionA (codeMat 116) (codeMat 159) (codeMat 462) = codeMat 162 := by
      unfold actionA
      rw [step109wc164s3_QtInv]
      show (codeMat 116 : Mat3).transpose * codeMat 462 * (codeMat 230 : Mat3).transpose = codeMat 162
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 10 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 116) (codeMat 159) (codeMat 10) = codeMat 96 := by
      unfold actionA
      rw [step109wc164s3_QtInv]
      show (codeMat 116 : Mat3).transpose * codeMat 10 * (codeMat 230 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 127 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 127 (by decide)
    have hact : actionA (codeMat 116) (codeMat 159) (codeMat 127) = codeMat 20 := by
      unfold actionA
      rw [step109wc164s3_QtInv]
      show (codeMat 116 : Mat3).transpose * codeMat 127 * (codeMat 230 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 475 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 475 (by decide)
    have hact : actionA (codeMat 116) (codeMat 159) (codeMat 475) = codeMat 10 := by
      unfold actionA
      rw [step109wc164s3_QtInv]
      show (codeMat 116 : Mat3).transpose * codeMat 475 * (codeMat 230 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 192 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 192 (by decide)
    have hact : actionA (codeMat 116) (codeMat 159) (codeMat 192) = codeMat 1 := by
      unfold actionA
      rw [step109wc164s3_QtInv]
      show (codeMat 116 : Mat3).transpose * codeMat 192 * (codeMat 230 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact

theorem step109wc164s3Dispatch :
    QuotientRankAtLeast (o164SourceU_wc ⟨3, by omega⟩) 15 := by
  have hP : Invertible (codeMat 116 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 159 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 116) (codeMat 159) o80W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 116) (codeMat 159) hP hQ o80W_wc 15
      step109_orbit80_lb15_wc
  exact quotientRankAtLeast_mono step109wc164s3_contain hAct


private theorem step109wc164s4_QtInv :
    (codeMat 443 : Mat3).transpose⁻¹ = (codeMat 254 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 443 : Mat3).transpose * (codeMat 254 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc164s4_contain :
    (o164SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 110) (codeMat 443) o80W_wc := by
  change spanCodes [256, 164, 96, 20, 10, 1] ≤ actionW (codeMat 110) (codeMat 443) o80W_wc
  apply step109wc164_spanCodes_le_of_gens [256, 164, 96, 20, 10, 1]
    (actionW (codeMat 110) (codeMat 443) o80W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 432 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 432 (by decide)
    have hact : actionA (codeMat 110) (codeMat 443) (codeMat 432) = codeMat 256 := by
      unfold actionA
      rw [step109wc164s4_QtInv]
      show (codeMat 110 : Mat3).transpose * codeMat 432 * (codeMat 254 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 462 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 462 (by decide)
    have hact : actionA (codeMat 110) (codeMat 443) (codeMat 462) = codeMat 164 := by
      unfold actionA
      rw [step109wc164s4_QtInv]
      show (codeMat 110 : Mat3).transpose * codeMat 462 * (codeMat 254 : Mat3).transpose = codeMat 164
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 366 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 366 (by decide)
    have hact : actionA (codeMat 110) (codeMat 443) (codeMat 366) = codeMat 96 := by
      unfold actionA
      rw [step109wc164s4_QtInv]
      show (codeMat 110 : Mat3).transpose * codeMat 366 * (codeMat 254 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 127 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 127 (by decide)
    have hact : actionA (codeMat 110) (codeMat 443) (codeMat 127) = codeMat 20 := by
      unfold actionA
      rw [step109wc164s4_QtInv]
      show (codeMat 110 : Mat3).transpose * codeMat 127 * (codeMat 254 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 283 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 283 (by decide)
    have hact : actionA (codeMat 110) (codeMat 443) (codeMat 283) = codeMat 10 := by
      unfold actionA
      rw [step109wc164s4_QtInv]
      show (codeMat 110 : Mat3).transpose * codeMat 283 * (codeMat 254 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 192 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 192 (by decide)
    have hact : actionA (codeMat 110) (codeMat 443) (codeMat 192) = codeMat 1 := by
      unfold actionA
      rw [step109wc164s4_QtInv]
      show (codeMat 110 : Mat3).transpose * codeMat 192 * (codeMat 254 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact

theorem step109wc164s4Dispatch :
    QuotientRankAtLeast (o164SourceU_wc ⟨4, by omega⟩) 15 := by
  have hP : Invertible (codeMat 110 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 443 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 110) (codeMat 443) o80W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 110) (codeMat 443) hP hQ o80W_wc 15
      step109_orbit80_lb15_wc
  exact quotientRankAtLeast_mono step109wc164s4_contain hAct

private def step109wc164s5SrcT : Submodule F2 Mat3 := spanCodes [272, 128, 66, 34, 8, 1]

private theorem step109wc164s5SrcT_lb : QuotientRankAtLeast step109wc164s5SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step99_orbit55_lb14_unconditional
  have hle : step109wc164s5SrcT ≤ transposeW o55W := by
    unfold step109wc164s5SrcT transposeW
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

private theorem step109wc164s5_QtInv :
    (codeMat 165 : Mat3).transpose⁻¹ = (codeMat 163 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 165 : Mat3).transpose * (codeMat 163 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc164s5_contain :
    (o164SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 142) (codeMat 165) step109wc164s5SrcT := by
  change spanCodes [256, 66, 34, 20, 10, 1] ≤ actionW (codeMat 142) (codeMat 165) step109wc164s5SrcT
  apply step109wc164_spanCodes_le_of_gens [256, 66, 34, 20, 10, 1]
    (actionW (codeMat 142) (codeMat 165) step109wc164s5SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 195 ∈ step109wc164s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 195 (by decide)
    have hact : actionA (codeMat 142) (codeMat 165) (codeMat 195) = codeMat 256 := by
      unfold actionA
      rw [step109wc164s5_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 195 * (codeMat 163 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 97 ∈ step109wc164s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 97 (by decide)
    have hact : actionA (codeMat 142) (codeMat 165) (codeMat 97) = codeMat 66 := by
      unfold actionA
      rw [step109wc164s5_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 97 * (codeMat 163 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 224 ∈ step109wc164s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 224 (by decide)
    have hact : actionA (codeMat 142) (codeMat 165) (codeMat 224) = codeMat 34 := by
      unfold actionA
      rw [step109wc164s5_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 224 * (codeMat 163 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 280 ∈ step109wc164s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 280 (by decide)
    have hact : actionA (codeMat 142) (codeMat 165) (codeMat 280) = codeMat 20 := by
      unfold actionA
      rw [step109wc164s5_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 280 * (codeMat 163 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 96 ∈ step109wc164s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 96 (by decide)
    have hact : actionA (codeMat 142) (codeMat 165) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step109wc164s5_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 96 * (codeMat 163 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ step109wc164s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 8 (by decide)
    have hact : actionA (codeMat 142) (codeMat 165) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc164s5_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 8 * (codeMat 163 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact

theorem step109wc164s5Dispatch :
    QuotientRankAtLeast (o164SourceU_wc ⟨5, by omega⟩) 14 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 165 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 165) step109wc164s5SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 165) hP hQ step109wc164s5SrcT 14
      step109wc164s5SrcT_lb
  exact quotientRankAtLeast_mono step109wc164s5_contain hAct

private def step109wc164s6SrcT : Submodule F2 Mat3 := spanCodes [272, 128, 66, 34, 8, 1]

private theorem step109wc164s6SrcT_lb : QuotientRankAtLeast step109wc164s6SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step99_orbit55_lb14_unconditional
  have hle : step109wc164s6SrcT ≤ transposeW o55W := by
    unfold step109wc164s6SrcT transposeW
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

private theorem step109wc164s6_QtInv :
    (codeMat 156 : Mat3).transpose⁻¹ = (codeMat 102 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 156 : Mat3).transpose * (codeMat 102 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc164s6_contain :
    (o164SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 92) (codeMat 156) step109wc164s6SrcT := by
  change spanCodes [256, 68, 36, 20, 10, 1] ≤ actionW (codeMat 92) (codeMat 156) step109wc164s6SrcT
  apply step109wc164_spanCodes_le_of_gens [256, 68, 36, 20, 10, 1]
    (actionW (codeMat 92) (codeMat 156) step109wc164s6SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 1 ∈ step109wc164s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 1 (by decide)
    have hact : actionA (codeMat 92) (codeMat 156) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc164s6_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 1 * (codeMat 102 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 66 ∈ step109wc164s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 66 (by decide)
    have hact : actionA (codeMat 92) (codeMat 156) (codeMat 66) = codeMat 68 := by
      unfold actionA
      rw [step109wc164s6_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 66 * (codeMat 102 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ step109wc164s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 8 (by decide)
    have hact : actionA (codeMat 92) (codeMat 156) (codeMat 8) = codeMat 36 := by
      unfold actionA
      rw [step109wc164s6_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 8 * (codeMat 102 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 496 ∈ step109wc164s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 496 (by decide)
    have hact : actionA (codeMat 92) (codeMat 156) (codeMat 496) = codeMat 20 := by
      unfold actionA
      rw [step109wc164s6_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 496 * (codeMat 102 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 272 ∈ step109wc164s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 272 (by decide)
    have hact : actionA (codeMat 92) (codeMat 156) (codeMat 272) = codeMat 10 := by
      unfold actionA
      rw [step109wc164s6_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 272 * (codeMat 102 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ step109wc164s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 128 (by decide)
    have hact : actionA (codeMat 92) (codeMat 156) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc164s6_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 128 * (codeMat 102 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact

theorem step109wc164s6Dispatch :
    QuotientRankAtLeast (o164SourceU_wc ⟨6, by omega⟩) 14 := by
  have hP : Invertible (codeMat 92 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 156 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 92) (codeMat 156) step109wc164s6SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 92) (codeMat 156) hP hQ step109wc164s6SrcT 14
      step109wc164s6SrcT_lb
  exact quotientRankAtLeast_mono step109wc164s6_contain hAct


private theorem step109wc164s7_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc164s7_contain :
    (o164SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 84) (codeMat 84) o56W := by
  change spanCodes [256, 128, 96, 20, 10, 1] ≤ actionW (codeMat 84) (codeMat 84) o56W
  apply step109wc164_spanCodes_le_of_gens [256, 128, 96, 20, 10, 1]
    (actionW (codeMat 84) (codeMat 84) o56W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 1 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc164s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 2) = codeMat 128 := by
      unfold actionA
      rw [step109wc164s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 12 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 12) = codeMat 96 := by
      unfold actionA
      rw [step109wc164s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 12 * (codeMat 84 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 80 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 80) = codeMat 20 := by
      unfold actionA
      rw [step109wc164s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 80 * (codeMat 84 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc164s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 160 * (codeMat 84 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc164s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact

theorem step109wc164s7Dispatch :
    QuotientRankAtLeast (o164SourceU_wc ⟨7, by omega⟩) 14 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 84) o56W) 14 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 84) hP hQ o56W 14
      step99_orbit56_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc164s7_contain hAct


private theorem step109wc164s8_QtInv :
    (codeMat 277 : Mat3).transpose⁻¹ = (codeMat 277 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 277 : Mat3).transpose * (codeMat 277 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc164s8_contain :
    (o164SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 465) (codeMat 277) o78W_wc := by
  change spanCodes [256, 134, 96, 20, 10, 1] ≤ actionW (codeMat 465) (codeMat 277) o78W_wc
  apply step109wc164_spanCodes_le_of_gens [256, 134, 96, 20, 10, 1]
    (actionW (codeMat 465) (codeMat 277) o78W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 365 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 365 (by decide)
    have hact : actionA (codeMat 465) (codeMat 277) (codeMat 365) = codeMat 256 := by
      unfold actionA
      rw [step109wc164s8_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 365 * (codeMat 277 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 149 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 149 (by decide)
    have hact : actionA (codeMat 465) (codeMat 277) (codeMat 149) = codeMat 134 := by
      unfold actionA
      rw [step109wc164s8_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 149 * (codeMat 277 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 97 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 97 (by decide)
    have hact : actionA (codeMat 465) (codeMat 277) (codeMat 97) = codeMat 96 := by
      unfold actionA
      rw [step109wc164s8_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 97 * (codeMat 277 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 21 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 21 (by decide)
    have hact : actionA (codeMat 465) (codeMat 277) (codeMat 21) = codeMat 20 := by
      unfold actionA
      rw [step109wc164s8_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 21 * (codeMat 277 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 465) (codeMat 277) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step109wc164s8_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 10 * (codeMat 277 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 465) (codeMat 277) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc164s8_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 1 * (codeMat 277 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact

theorem step109wc164s8Dispatch :
    QuotientRankAtLeast (o164SourceU_wc ⟨8, by omega⟩) 14 := by
  have hP : Invertible (codeMat 465 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 277 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 465) (codeMat 277) o78W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 465) (codeMat 277) hP hQ o78W_wc 14
      step109_orbit78_lb14_wc
  exact quotientRankAtLeast_mono step109wc164s8_contain hAct


private theorem step109wc164s9_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc164s9_contain :
    (o164SourceU_wc ⟨9, by omega⟩) ≤ actionW (codeMat 273) (codeMat 273) o36W_wc := by
  change spanCodes [256, 96, 20, 8, 2, 1] ≤ actionW (codeMat 273) (codeMat 273) o36W_wc
  apply step109wc164_spanCodes_le_of_gens [256, 96, 20, 8, 2, 1]
    (actionW (codeMat 273) (codeMat 273) o36W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 256 ∈ o36W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step109wc164s9_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 273 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 96 ∈ o36W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 8, 2, 1] 96 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 96) = codeMat 96 := by
      unfold actionA
      rw [step109wc164s9_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 96 * (codeMat 273 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 20 ∈ o36W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 8, 2, 1] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 20) = codeMat 20 := by
      unfold actionA
      rw [step109wc164s9_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * (codeMat 273 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ o36W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc164s9_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o36W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc164s9_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o36W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc164s9_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact

theorem step109wc164s9Dispatch :
    QuotientRankAtLeast (o164SourceU_wc ⟨9, by omega⟩) 13 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 273) o36W_wc) 13 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 273) hP hQ o36W_wc 13
      step109_orbit36_lb13_wc
  exact quotientRankAtLeast_mono step109wc164s9_contain hAct

private def step109wc164s10SrcT : Submodule F2 Mat3 := spanCodes [256, 132, 80, 8, 2, 1]

private theorem step109wc164s10SrcT_lb : QuotientRankAtLeast step109wc164s10SrcT 13 := by
  have ht := quotientRankAtLeast_transpose step109_orbit36_lb13_wc
  have hle : step109wc164s10SrcT ≤ transposeW o36W_wc := by
    unfold step109wc164s10SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4 | h5
    · subst h0
      show codeMat 256 ∈ Submodule.map transposeLinearMap o36W_wc
      exact ⟨codeMat 256, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 8, 2, 1] 256 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 132 ∈ Submodule.map transposeLinearMap o36W_wc
      exact ⟨codeMat 96, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 8, 2, 1] 96 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 80 ∈ Submodule.map transposeLinearMap o36W_wc
      exact ⟨codeMat 20, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 8, 2, 1] 20 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 8 ∈ Submodule.map transposeLinearMap o36W_wc
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 8, 2, 1] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 2 ∈ Submodule.map transposeLinearMap o36W_wc
      exact ⟨codeMat 8, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 8, 2, 1] 8 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h5
      show codeMat 1 ∈ Submodule.map transposeLinearMap o36W_wc
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 8, 2, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc164s10_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc164s10_contain :
    (o164SourceU_wc ⟨10, by omega⟩) ≤ actionW (codeMat 161) (codeMat 140) step109wc164s10SrcT := by
  change spanCodes [256, 96, 16, 10, 4, 1] ≤ actionW (codeMat 161) (codeMat 140) step109wc164s10SrcT
  apply step109wc164_spanCodes_le_of_gens [256, 96, 16, 10, 4, 1]
    (actionW (codeMat 161) (codeMat 140) step109wc164s10SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 8 ∈ step109wc164s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 80, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 140) (codeMat 8) = codeMat 256 := by
      unfold actionA
      rw [step109wc164s10_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 80 ∈ step109wc164s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 80, 8, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 161) (codeMat 140) (codeMat 80) = codeMat 96 := by
      unfold actionA
      rw [step109wc164s10_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 80 * (codeMat 98 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 256 ∈ step109wc164s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 80, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 140) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step109wc164s10_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 98 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 132 ∈ step109wc164s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 80, 8, 2, 1] 132 (by decide)
    have hact : actionA (codeMat 161) (codeMat 140) (codeMat 132) = codeMat 10 := by
      unfold actionA
      rw [step109wc164s10_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 132 * (codeMat 98 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ step109wc164s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 80, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 140) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step109wc164s10_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ step109wc164s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 80, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 140) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc164s10_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact

theorem step109wc164s10Dispatch :
    QuotientRankAtLeast (o164SourceU_wc ⟨10, by omega⟩) 13 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 140) step109wc164s10SrcT) 13 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 140) hP hQ step109wc164s10SrcT 13
      step109wc164s10SrcT_lb
  exact quotientRankAtLeast_mono step109wc164s10_contain hAct

private def step109wc164s11SrcT : Submodule F2 Mat3 := spanCodes [272, 128, 96, 8, 2, 1]

private theorem step109wc164s11SrcT_lb : QuotientRankAtLeast step109wc164s11SrcT 12 := by
  have ht := quotientRankAtLeast_transpose orbit44_lb12_mono
  have hle : step109wc164s11SrcT ≤ transposeW o44W_mono := by
    unfold step109wc164s11SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4 | h5
    · subst h0
      show codeMat 272 ∈ Submodule.map transposeLinearMap o44W_mono
      exact ⟨codeMat 272, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 8, 2, 1] 272 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 128 ∈ Submodule.map transposeLinearMap o44W_mono
      exact ⟨codeMat 32, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 8, 2, 1] 32 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 96 ∈ Submodule.map transposeLinearMap o44W_mono
      exact ⟨codeMat 132, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 8, 2, 1] 132 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 8 ∈ Submodule.map transposeLinearMap o44W_mono
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 8, 2, 1] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 2 ∈ Submodule.map transposeLinearMap o44W_mono
      exact ⟨codeMat 8, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 8, 2, 1] 8 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h5
      show codeMat 1 ∈ Submodule.map transposeLinearMap o44W_mono
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 8, 2, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc164s11_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc164s11_contain :
    (o164SourceU_wc ⟨11, by omega⟩) ≤ actionW (codeMat 84) (codeMat 140) step109wc164s11SrcT := by
  change spanCodes [256, 64, 32, 20, 10, 1] ≤ actionW (codeMat 84) (codeMat 140) step109wc164s11SrcT
  apply step109wc164_spanCodes_le_of_gens [256, 64, 32, 20, 10, 1]
    (actionW (codeMat 84) (codeMat 140) step109wc164s11SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 1 ∈ step109wc164s11SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 96, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc164s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ step109wc164s11SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 96, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 2) = codeMat 64 := by
      unfold actionA
      rw [step109wc164s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ step109wc164s11SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 96, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc164s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 96 ∈ step109wc164s11SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 96, 8, 2, 1] 96 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 96) = codeMat 20 := by
      unfold actionA
      rw [step109wc164s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 96 * (codeMat 98 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 272 ∈ step109wc164s11SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 96, 8, 2, 1] 272 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 272) = codeMat 10 := by
      unfold actionA
      rw [step109wc164s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 272 * (codeMat 98 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ step109wc164s11SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 96, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc164s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact

theorem step109wc164s11Dispatch :
    QuotientRankAtLeast (o164SourceU_wc ⟨11, by omega⟩) 12 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 140) step109wc164s11SrcT) 12 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 140) hP hQ step109wc164s11SrcT 12
      step109wc164s11SrcT_lb
  exact quotientRankAtLeast_mono step109wc164s11_contain hAct


private theorem step109wc164s12_QtInv :
    (codeMat 230 : Mat3).transpose⁻¹ = (codeMat 159 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 230 : Mat3).transpose * (codeMat 159 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc164s12_contain :
    (o164SourceU_wc ⟨12, by omega⟩) ≤ actionW (codeMat 84) (codeMat 230) orbit14W := by
  change spanCodes [256, 160, 96, 18, 10, 6, 1] ≤ actionW (codeMat 84) (codeMat 230) orbit14W
  apply step109wc164_spanCodes_le_of_gens [256, 160, 96, 18, 10, 6, 1]
    (actionW (codeMat 84) (codeMat 230) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 84) (codeMat 230) (codeMat 3) = codeMat 256 := by
      unfold actionA
      rw [step109wc164s12_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 3 * (codeMat 159 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 29 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 29 (by decide)
    have hact : actionA (codeMat 84) (codeMat 230) (codeMat 29) = codeMat 160 := by
      unfold actionA
      rw [step109wc164s12_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 29 * (codeMat 159 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 28 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 28 (by decide)
    have hact : actionA (codeMat 84) (codeMat 230) (codeMat 28) = codeMat 96 := by
      unfold actionA
      rw [step109wc164s12_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 28 * (codeMat 159 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 84) (codeMat 230) (codeMat 360) = codeMat 18 := by
      unfold actionA
      rw [step109wc164s12_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 360 * (codeMat 159 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 352 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 352 (by decide)
    have hact : actionA (codeMat 84) (codeMat 230) (codeMat 352) = codeMat 10 := by
      unfold actionA
      rw [step109wc164s12_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 352 * (codeMat 159 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 230) (codeMat 384) = codeMat 6 := by
      unfold actionA
      rw [step109wc164s12_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 159 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 230) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc164s12_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 159 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc164_codeMat_mem_actionW_of_witness hw hact

theorem step109wc164s12Dispatch :
    QuotientRankAtLeast (o164SourceU_wc ⟨12, by omega⟩) 12 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 230 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 230) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 230) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc164s12_contain hAct

theorem step109wc164_all_dispatch (i : Fin 13) :
    QuotientRankAtLeast (o164SourceU_wc i) (o164SourceLb_wc i) := by
  fin_cases i
  · exact step109wc164s0Dispatch
  · exact step109wc164s1Dispatch
  · exact step109wc164s2Dispatch
  · exact step109wc164s3Dispatch
  · exact step109wc164s4Dispatch
  · exact step109wc164s5Dispatch
  · exact step109wc164s6Dispatch
  · exact step109wc164s7Dispatch
  · exact step109wc164s8Dispatch
  · exact step109wc164s9Dispatch
  · exact step109wc164s10Dispatch
  · exact step109wc164s11Dispatch
  · exact step109wc164s12Dispatch

theorem step109_orbit164_lb16_wc : QuotientRankAtLeast o164W_wc 16 :=
  o164Lb16_wc step109wc164_all_dispatch

end QiushiMatmul
