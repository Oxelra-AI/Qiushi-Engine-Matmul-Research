import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit213Consumer
import QiushiStep99Orbit69Dispatch
import QiushiStep99Orbit76Dispatch
import QiushiWcOrbit80Dispatch
import QiushiWcOrbit81Dispatch
import QiushiStep99Orbit56Dispatch
import QiushiWcOrbit57Dispatch
import QiushiStep99Orbit68Dispatch
import QiushiWcOrbit78Dispatch
import QiushiStep99Orbit82Dispatch
import QiushiWcOrbit50Dispatch

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc213_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc213_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc213s0_QtInv :
    (codeMat 298 : Mat3).transpose⁻¹ = (codeMat 270 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 298 : Mat3).transpose * (codeMat 270 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc213s0_contain :
    (o213SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 459) (codeMat 298) o69W := by
  change spanCodes [262, 132, 96, 18, 10, 1] ≤ actionW (codeMat 459) (codeMat 298) o69W
  apply step109wc213_spanCodes_le_of_gens [262, 132, 96, 18, 10, 1]
    (actionW (codeMat 459) (codeMat 298) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 446 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 446 (by decide)
    have hact : actionA (codeMat 459) (codeMat 298) (codeMat 446) = codeMat 262 := by
      unfold actionA
      rw [step109wc213s0_QtInv]
      show (codeMat 459 : Mat3).transpose * codeMat 446 * (codeMat 270 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 113 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 113 (by decide)
    have hact : actionA (codeMat 459) (codeMat 298) (codeMat 113) = codeMat 132 := by
      unfold actionA
      rw [step109wc213s0_QtInv]
      show (codeMat 459 : Mat3).transpose * codeMat 113 * (codeMat 270 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 180 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 180 (by decide)
    have hact : actionA (codeMat 459) (codeMat 298) (codeMat 180) = codeMat 96 := by
      unfold actionA
      rw [step109wc213s0_QtInv]
      show (codeMat 459 : Mat3).transpose * codeMat 180 * (codeMat 270 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 459) (codeMat 298) (codeMat 1) = codeMat 18 := by
      unfold actionA
      rw [step109wc213s0_QtInv]
      show (codeMat 459 : Mat3).transpose * codeMat 1 * (codeMat 270 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 26 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 26 (by decide)
    have hact : actionA (codeMat 459) (codeMat 298) (codeMat 26) = codeMat 10 := by
      unfold actionA
      rw [step109wc213s0_QtInv]
      show (codeMat 459 : Mat3).transpose * codeMat 26 * (codeMat 270 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 459) (codeMat 298) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc213s0_QtInv]
      show (codeMat 459 : Mat3).transpose * codeMat 16 * (codeMat 270 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact

theorem step109wc213s0Dispatch :
    QuotientRankAtLeast (o213SourceU_wc ⟨0, by omega⟩) 15 := by
  have hP : Invertible (codeMat 459 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 298 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 459) (codeMat 298) o69W) 15 :=
    @quotientRankAtLeast_action (codeMat 459) (codeMat 298) hP hQ o69W 15
      step99_orbit69_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc213s0_contain hAct


private theorem step109wc213s1_QtInv :
    (codeMat 212 : Mat3).transpose⁻¹ = (codeMat 86 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 212 : Mat3).transpose * (codeMat 86 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc213s1_contain :
    (o213SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 444) (codeMat 212) o76W := by
  change spanCodes [256, 132, 96, 20, 10, 1] ≤ actionW (codeMat 444) (codeMat 212) o76W
  apply step109wc213_spanCodes_le_of_gens [256, 132, 96, 20, 10, 1]
    (actionW (codeMat 444) (codeMat 212) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 1 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 444) (codeMat 212) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc213s1_QtInv]
      show (codeMat 444 : Mat3).transpose * codeMat 1 * (codeMat 86 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 78 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 444) (codeMat 212) (codeMat 78) = codeMat 132 := by
      unfold actionA
      rw [step109wc213s1_QtInv]
      show (codeMat 444 : Mat3).transpose * codeMat 78 * (codeMat 86 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 69 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 444) (codeMat 212) (codeMat 69) = codeMat 96 := by
      unfold actionA
      rw [step109wc213s1_QtInv]
      show (codeMat 444 : Mat3).transpose * codeMat 69 * (codeMat 86 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 462 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 462 (by decide)
    have hact : actionA (codeMat 444) (codeMat 212) (codeMat 462) = codeMat 20 := by
      unfold actionA
      rw [step109wc213s1_QtInv]
      show (codeMat 444 : Mat3).transpose * codeMat 462 * (codeMat 86 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 180 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 180 (by decide)
    have hact : actionA (codeMat 444) (codeMat 212) (codeMat 180) = codeMat 10 := by
      unfold actionA
      rw [step109wc213s1_QtInv]
      show (codeMat 444 : Mat3).transpose * codeMat 180 * (codeMat 86 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 288 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 444) (codeMat 212) (codeMat 288) = codeMat 1 := by
      unfold actionA
      rw [step109wc213s1_QtInv]
      show (codeMat 444 : Mat3).transpose * codeMat 288 * (codeMat 86 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact

theorem step109wc213s1Dispatch :
    QuotientRankAtLeast (o213SourceU_wc ⟨1, by omega⟩) 15 := by
  have hP : Invertible (codeMat 444 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 212 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 444) (codeMat 212) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 444) (codeMat 212) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc213s1_contain hAct


private theorem step109wc213s2_QtInv :
    (codeMat 169 : Mat3).transpose⁻¹ = (codeMat 225 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 169 : Mat3).transpose * (codeMat 225 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc213s2_contain :
    (o213SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 102) (codeMat 169) o80W_wc := by
  change spanCodes [258, 132, 96, 22, 10, 1] ≤ actionW (codeMat 102) (codeMat 169) o80W_wc
  apply step109wc213_spanCodes_le_of_gens [258, 132, 96, 22, 10, 1]
    (actionW (codeMat 102) (codeMat 169) o80W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 272 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 272 (by decide)
    have hact : actionA (codeMat 102) (codeMat 169) (codeMat 272) = codeMat 258 := by
      unfold actionA
      rw [step109wc213s2_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 272 * (codeMat 225 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 102) (codeMat 169) (codeMat 160) = codeMat 132 := by
      unfold actionA
      rw [step109wc213s2_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 160 * (codeMat 225 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 10 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 102) (codeMat 169) (codeMat 10) = codeMat 96 := by
      unfold actionA
      rw [step109wc213s2_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 10 * (codeMat 225 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 420 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 420 (by decide)
    have hact : actionA (codeMat 102) (codeMat 169) (codeMat 420) = codeMat 22 := by
      unfold actionA
      rw [step109wc213s2_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 420 * (codeMat 225 : Mat3).transpose = codeMat 22
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 283 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 283 (by decide)
    have hact : actionA (codeMat 102) (codeMat 169) (codeMat 283) = codeMat 10 := by
      unfold actionA
      rw [step109wc213s2_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 283 * (codeMat 225 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 192 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 192 (by decide)
    have hact : actionA (codeMat 102) (codeMat 169) (codeMat 192) = codeMat 1 := by
      unfold actionA
      rw [step109wc213s2_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 192 * (codeMat 225 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact

theorem step109wc213s2Dispatch :
    QuotientRankAtLeast (o213SourceU_wc ⟨2, by omega⟩) 15 := by
  have hP : Invertible (codeMat 102 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 102) (codeMat 169) o80W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 102) (codeMat 169) hP hQ o80W_wc 15
      step109_orbit80_lb15_wc
  exact quotientRankAtLeast_mono step109wc213s2_contain hAct


private theorem step109wc213s3_QtInv :
    (codeMat 403 : Mat3).transpose⁻¹ = (codeMat 403 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 403 : Mat3).transpose * (codeMat 403 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc213s3_contain :
    (o213SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 313) (codeMat 403) o76W := by
  change spanCodes [276, 132, 68, 36, 10, 1] ≤ actionW (codeMat 313) (codeMat 403) o76W
  apply step109wc213_spanCodes_le_of_gens [276, 132, 68, 36, 10, 1]
    (actionW (codeMat 313) (codeMat 403) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 251 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 251 (by decide)
    have hact : actionA (codeMat 313) (codeMat 403) (codeMat 251) = codeMat 276 := by
      unfold actionA
      rw [step109wc213s3_QtInv]
      show (codeMat 313 : Mat3).transpose * codeMat 251 * (codeMat 403 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 452 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 452 (by decide)
    have hact : actionA (codeMat 313) (codeMat 403) (codeMat 452) = codeMat 132 := by
      unfold actionA
      rw [step109wc213s3_QtInv]
      show (codeMat 313 : Mat3).transpose * codeMat 452 * (codeMat 403 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 313) (codeMat 403) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step109wc213s3_QtInv]
      show (codeMat 313 : Mat3).transpose * codeMat 68 * (codeMat 403 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 288 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 313) (codeMat 403) (codeMat 288) = codeMat 36 := by
      unfold actionA
      rw [step109wc213s3_QtInv]
      show (codeMat 313 : Mat3).transpose * codeMat 288 * (codeMat 403 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 78 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 313) (codeMat 403) (codeMat 78) = codeMat 10 := by
      unfold actionA
      rw [step109wc213s3_QtInv]
      show (codeMat 313 : Mat3).transpose * codeMat 78 * (codeMat 403 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 313) (codeMat 403) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc213s3_QtInv]
      show (codeMat 313 : Mat3).transpose * codeMat 1 * (codeMat 403 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact

theorem step109wc213s3Dispatch :
    QuotientRankAtLeast (o213SourceU_wc ⟨3, by omega⟩) 15 := by
  have hP : Invertible (codeMat 313 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 403 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 313) (codeMat 403) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 313) (codeMat 403) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc213s3_contain hAct

private def step109wc213s4SrcT : Submodule F2 Mat3 := spanCodes [272, 132, 80, 36, 10, 1]

private theorem step109wc213s4SrcT_lb : QuotientRankAtLeast step109wc213s4SrcT 15 := by
  have ht := quotientRankAtLeast_transpose step109_orbit80_lb15_wc
  have hle : step109wc213s4SrcT ≤ transposeW o80W_wc := by
    unfold step109wc213s4SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4 | h5
    · subst h0
      show codeMat 272 ∈ Submodule.map transposeLinearMap o80W_wc
      exact ⟨codeMat 272, spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 272 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 132 ∈ Submodule.map transposeLinearMap o80W_wc
      exact ⟨codeMat 96, spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 96 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 80 ∈ Submodule.map transposeLinearMap o80W_wc
      exact ⟨codeMat 20, spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 20 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 36 ∈ Submodule.map transposeLinearMap o80W_wc
      exact ⟨codeMat 192, spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 192 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 10 ∈ Submodule.map transposeLinearMap o80W_wc
      exact ⟨codeMat 10, spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 10 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h5
      show codeMat 1 ∈ Submodule.map transposeLinearMap o80W_wc
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc213s4_QtInv :
    (codeMat 124 : Mat3).transpose⁻¹ = (codeMat 124 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 124 : Mat3).transpose * (codeMat 124 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc213s4_contain :
    (o213SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 215) (codeMat 124) step109wc213s4SrcT := by
  change spanCodes [276, 132, 70, 38, 10, 1] ≤ actionW (codeMat 215) (codeMat 124) step109wc213s4SrcT
  apply step109wc213_spanCodes_le_of_gens [276, 132, 70, 38, 10, 1]
    (actionW (codeMat 215) (codeMat 124) step109wc213s4SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 11 ∈ step109wc213s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 36, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 215) (codeMat 124) (codeMat 11) = codeMat 276 := by
      unfold actionA
      rw [step109wc213s4_QtInv]
      show (codeMat 215 : Mat3).transpose * codeMat 11 * (codeMat 124 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 90 ∈ step109wc213s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 36, 10, 1] 90 (by decide)
    have hact : actionA (codeMat 215) (codeMat 124) (codeMat 90) = codeMat 132 := by
      unfold actionA
      rw [step109wc213s4_QtInv]
      show (codeMat 215 : Mat3).transpose * codeMat 90 * (codeMat 124 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 462 ∈ step109wc213s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 36, 10, 1] 462 (by decide)
    have hact : actionA (codeMat 215) (codeMat 124) (codeMat 462) = codeMat 70 := by
      unfold actionA
      rw [step109wc213s4_QtInv]
      show (codeMat 215 : Mat3).transpose * codeMat 462 * (codeMat 124 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 80 ∈ step109wc213s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 36, 10, 1] 80 (by decide)
    have hact : actionA (codeMat 215) (codeMat 124) (codeMat 80) = codeMat 38 := by
      unfold actionA
      rw [step109wc213s4_QtInv]
      show (codeMat 215 : Mat3).transpose * codeMat 80 * (codeMat 124 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ step109wc213s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 36, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 215) (codeMat 124) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc213s4_QtInv]
      show (codeMat 215 : Mat3).transpose * codeMat 160 * (codeMat 124 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 432 ∈ step109wc213s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 36, 10, 1] 432 (by decide)
    have hact : actionA (codeMat 215) (codeMat 124) (codeMat 432) = codeMat 1 := by
      unfold actionA
      rw [step109wc213s4_QtInv]
      show (codeMat 215 : Mat3).transpose * codeMat 432 * (codeMat 124 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact

theorem step109wc213s4Dispatch :
    QuotientRankAtLeast (o213SourceU_wc ⟨4, by omega⟩) 15 := by
  have hP : Invertible (codeMat 215 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 124 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 215) (codeMat 124) step109wc213s4SrcT) 15 :=
    @quotientRankAtLeast_action (codeMat 215) (codeMat 124) hP hQ step109wc213s4SrcT 15
      step109wc213s4SrcT_lb
  exact quotientRankAtLeast_mono step109wc213s4_contain hAct


private theorem step109wc213s5_QtInv :
    (codeMat 431 : Mat3).transpose⁻¹ = (codeMat 477 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 431 : Mat3).transpose * (codeMat 477 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc213s5_contain :
    (o213SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 98) (codeMat 431) o81W_wc := by
  change spanCodes [276, 132, 82, 50, 10, 1] ≤ actionW (codeMat 98) (codeMat 431) o81W_wc
  apply step109wc213_spanCodes_le_of_gens [276, 132, 82, 50, 10, 1]
    (actionW (codeMat 98) (codeMat 431) o81W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 509 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 509 (by decide)
    have hact : actionA (codeMat 98) (codeMat 431) (codeMat 509) = codeMat 276 := by
      unfold actionA
      rw [step109wc213s5_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 509 * (codeMat 477 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 488 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 488 (by decide)
    have hact : actionA (codeMat 98) (codeMat 431) (codeMat 488) = codeMat 132 := by
      unfold actionA
      rw [step109wc213s5_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 488 * (codeMat 477 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 349 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 349 (by decide)
    have hact : actionA (codeMat 98) (codeMat 431) (codeMat 349) = codeMat 82 := by
      unfold actionA
      rw [step109wc213s5_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 349 * (codeMat 477 : Mat3).transpose = codeMat 82
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 322 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 322 (by decide)
    have hact : actionA (codeMat 98) (codeMat 431) (codeMat 322) = codeMat 50 := by
      unfold actionA
      rw [step109wc213s5_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 322 * (codeMat 477 : Mat3).transpose = codeMat 50
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 323 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 323 (by decide)
    have hact : actionA (codeMat 98) (codeMat 431) (codeMat 323) = codeMat 10 := by
      unfold actionA
      rw [step109wc213s5_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 323 * (codeMat 477 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 192 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 192 (by decide)
    have hact : actionA (codeMat 98) (codeMat 431) (codeMat 192) = codeMat 1 := by
      unfold actionA
      rw [step109wc213s5_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 192 * (codeMat 477 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact

theorem step109wc213s5Dispatch :
    QuotientRankAtLeast (o213SourceU_wc ⟨5, by omega⟩) 15 := by
  have hP : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 431 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 98) (codeMat 431) o81W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 98) (codeMat 431) hP hQ o81W_wc 15
      step109_orbit81_lb15_wc
  exact quotientRankAtLeast_mono step109wc213s5_contain hAct


private theorem step109wc213s6_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc213s6_contain :
    (o213SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 273) (codeMat 161) o56W := by
  change spanCodes [272, 128, 96, 10, 4, 1] ≤ actionW (codeMat 273) (codeMat 161) o56W
  apply step109wc213_spanCodes_le_of_gens [272, 128, 96, 10, 4, 1]
    (actionW (codeMat 273) (codeMat 161) o56W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 160 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 160) = codeMat 272 := by
      unfold actionA
      rw [step109wc213s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 160 * (codeMat 161 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 256) = codeMat 128 := by
      unfold actionA
      rw [step109wc213s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 161 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 80 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 80) = codeMat 96 := by
      unfold actionA
      rw [step109wc213s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 80 * (codeMat 161 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 12 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 12) = codeMat 10 := by
      unfold actionA
      rw [step109wc213s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 12 * (codeMat 161 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 2) = codeMat 4 := by
      unfold actionA
      rw [step109wc213s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc213s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact

theorem step109wc213s6Dispatch :
    QuotientRankAtLeast (o213SourceU_wc ⟨6, by omega⟩) 14 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 161) o56W) 14 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 161) hP hQ o56W 14
      step99_orbit56_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc213s6_contain hAct


private theorem step109wc213s7_QtInv :
    (codeMat 410 : Mat3).transpose⁻¹ = (codeMat 331 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 410 : Mat3).transpose * (codeMat 331 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc213s7_contain :
    (o213SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 241) (codeMat 410) o57W_wc := by
  change spanCodes [274, 130, 96, 10, 6, 1] ≤ actionW (codeMat 241) (codeMat 410) o57W_wc
  apply step109wc213_spanCodes_le_of_gens [274, 130, 96, 10, 6, 1]
    (actionW (codeMat 241) (codeMat 410) o57W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 228 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 228 (by decide)
    have hact : actionA (codeMat 241) (codeMat 410) (codeMat 228) = codeMat 274 := by
      unfold actionA
      rw [step109wc213s7_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 228 * (codeMat 331 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 504 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 504 (by decide)
    have hact : actionA (codeMat 241) (codeMat 410) (codeMat 504) = codeMat 130 := by
      unfold actionA
      rw [step109wc213s7_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 504 * (codeMat 331 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 406 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 406 (by decide)
    have hact : actionA (codeMat 241) (codeMat 410) (codeMat 406) = codeMat 96 := by
      unfold actionA
      rw [step109wc213s7_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 406 * (codeMat 331 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 133 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 133 (by decide)
    have hact : actionA (codeMat 241) (codeMat 410) (codeMat 133) = codeMat 10 := by
      unfold actionA
      rw [step109wc213s7_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 133 * (codeMat 331 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 241) (codeMat 410) (codeMat 3) = codeMat 6 := by
      unfold actionA
      rw [step109wc213s7_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 3 * (codeMat 331 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 241) (codeMat 410) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc213s7_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 2 * (codeMat 331 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact

theorem step109wc213s7Dispatch :
    QuotientRankAtLeast (o213SourceU_wc ⟨7, by omega⟩) 14 := by
  have hP : Invertible (codeMat 241 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 410 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 241) (codeMat 410) o57W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 241) (codeMat 410) hP hQ o57W_wc 14
      step109_orbit57_lb14_wc
  exact quotientRankAtLeast_mono step109wc213s7_contain hAct


private theorem step109wc213s8_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = (codeMat 267 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * (codeMat 267 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc213s8_contain :
    (o213SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 267) (codeMat 282) o68W := by
  change spanCodes [260, 132, 96, 16, 10, 1] ≤ actionW (codeMat 267) (codeMat 282) o68W
  apply step109wc213_spanCodes_le_of_gens [260, 132, 96, 16, 10, 1]
    (actionW (codeMat 267) (codeMat 282) o68W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 288 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 288) = codeMat 260 := by
      unfold actionA
      rw [step109wc213s8_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 288 * (codeMat 267 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 224 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 224 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 224) = codeMat 132 := by
      unfold actionA
      rw [step109wc213s8_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 224 * (codeMat 267 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 164 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 164 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 164) = codeMat 96 := by
      unfold actionA
      rw [step109wc213s8_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 164 * (codeMat 267 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 27 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 27) = codeMat 16 := by
      unfold actionA
      rw [step109wc213s8_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 27 * (codeMat 267 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step109wc213s8_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 10 * (codeMat 267 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc213s8_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 16 * (codeMat 267 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact

theorem step109wc213s8Dispatch :
    QuotientRankAtLeast (o213SourceU_wc ⟨8, by omega⟩) 14 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 282) o68W) 14 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 282) hP hQ o68W 14
      step99_orbit68_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc213s8_contain hAct

private def step109wc213s9SrcT : Submodule F2 Mat3 := spanCodes [256, 160, 66, 20, 8, 1]

private theorem step109wc213s9SrcT_lb : QuotientRankAtLeast step109wc213s9SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step99_orbit56_lb14_unconditional
  have hle : step109wc213s9SrcT ≤ transposeW o56W := by
    unfold step109wc213s9SrcT transposeW
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

private theorem step109wc213s9_QtInv :
    (codeMat 311 : Mat3).transpose⁻¹ = (codeMat 307 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 311 : Mat3).transpose * (codeMat 307 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc213s9_contain :
    (o213SourceU_wc ⟨9, by omega⟩) ≤ actionW (codeMat 425) (codeMat 311) step109wc213s9SrcT := by
  change spanCodes [276, 132, 64, 32, 10, 1] ≤ actionW (codeMat 425) (codeMat 311) step109wc213s9SrcT
  apply step109wc213_spanCodes_le_of_gens [276, 132, 64, 32, 10, 1]
    (actionW (codeMat 425) (codeMat 311) step109wc213s9SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 227 ∈ step109wc213s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 227 (by decide)
    have hact : actionA (codeMat 425) (codeMat 311) (codeMat 227) = codeMat 276 := by
      unfold actionA
      rw [step109wc213s9_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 227 * (codeMat 307 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 28 ∈ step109wc213s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 28 (by decide)
    have hact : actionA (codeMat 425) (codeMat 311) (codeMat 28) = codeMat 132 := by
      unfold actionA
      rw [step109wc213s9_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 28 * (codeMat 307 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 9 ∈ step109wc213s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 9 (by decide)
    have hact : actionA (codeMat 425) (codeMat 311) (codeMat 9) = codeMat 64 := by
      unfold actionA
      rw [step109wc213s9_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 9 * (codeMat 307 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 511 ∈ step109wc213s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 511 (by decide)
    have hact : actionA (codeMat 425) (codeMat 311) (codeMat 511) = codeMat 32 := by
      unfold actionA
      rw [step109wc213s9_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 511 * (codeMat 307 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 74 ∈ step109wc213s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 74 (by decide)
    have hact : actionA (codeMat 425) (codeMat 311) (codeMat 74) = codeMat 10 := by
      unfold actionA
      rw [step109wc213s9_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 74 * (codeMat 307 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ step109wc213s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 1 (by decide)
    have hact : actionA (codeMat 425) (codeMat 311) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc213s9_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 1 * (codeMat 307 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact

theorem step109wc213s9Dispatch :
    QuotientRankAtLeast (o213SourceU_wc ⟨9, by omega⟩) 14 := by
  have hP : Invertible (codeMat 425 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 311 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 425) (codeMat 311) step109wc213s9SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 425) (codeMat 311) hP hQ step109wc213s9SrcT 14
      step109wc213s9SrcT_lb
  exact quotientRankAtLeast_mono step109wc213s9_contain hAct

private def step109wc213s10SrcT : Submodule F2 Mat3 := spanCodes [272, 132, 66, 34, 8, 1]

private theorem step109wc213s10SrcT_lb : QuotientRankAtLeast step109wc213s10SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step109_orbit57_lb14_wc
  have hle : step109wc213s10SrcT ≤ transposeW o57W_wc := by
    unfold step109wc213s10SrcT transposeW
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

private theorem step109wc213s10_QtInv :
    (codeMat 421 : Mat3).transpose⁻¹ = (codeMat 179 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 421 : Mat3).transpose * (codeMat 179 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc213s10_contain :
    (o213SourceU_wc ⟨10, by omega⟩) ≤ actionW (codeMat 334) (codeMat 421) step109wc213s10SrcT := by
  change spanCodes [276, 132, 66, 34, 10, 1] ≤ actionW (codeMat 334) (codeMat 421) step109wc213s10SrcT
  apply step109wc213_spanCodes_le_of_gens [276, 132, 66, 34, 10, 1]
    (actionW (codeMat 334) (codeMat 421) step109wc213s10SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 228 ∈ step109wc213s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 66, 34, 8, 1] 228 (by decide)
    have hact : actionA (codeMat 334) (codeMat 421) (codeMat 228) = codeMat 276 := by
      unfold actionA
      rw [step109wc213s10_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 228 * (codeMat 179 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 280 ∈ step109wc213s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 66, 34, 8, 1] 280 (by decide)
    have hact : actionA (codeMat 334) (codeMat 421) (codeMat 280) = codeMat 132 := by
      unfold actionA
      rw [step109wc213s10_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 280 * (codeMat 179 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 104 ∈ step109wc213s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 66, 34, 8, 1] 104 (by decide)
    have hact : actionA (codeMat 334) (codeMat 421) (codeMat 104) = codeMat 66 := by
      unfold actionA
      rw [step109wc213s10_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 104 * (codeMat 179 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 479 ∈ step109wc213s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 66, 34, 8, 1] 479 (by decide)
    have hact : actionA (codeMat 334) (codeMat 421) (codeMat 479) = codeMat 34 := by
      unfold actionA
      rw [step109wc213s10_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 479 * (codeMat 179 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 105 ∈ step109wc213s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 66, 34, 8, 1] 105 (by decide)
    have hact : actionA (codeMat 334) (codeMat 421) (codeMat 105) = codeMat 10 := by
      unfold actionA
      rw [step109wc213s10_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 105 * (codeMat 179 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ step109wc213s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 66, 34, 8, 1] 8 (by decide)
    have hact : actionA (codeMat 334) (codeMat 421) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc213s10_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 8 * (codeMat 179 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact

theorem step109wc213s10Dispatch :
    QuotientRankAtLeast (o213SourceU_wc ⟨10, by omega⟩) 14 := by
  have hP : Invertible (codeMat 334 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 421 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 334) (codeMat 421) step109wc213s10SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 334) (codeMat 421) hP hQ step109wc213s10SrcT 14
      step109wc213s10SrcT_lb
  exact quotientRankAtLeast_mono step109wc213s10_contain hAct


private theorem step109wc213s11_QtInv :
    (codeMat 489 : Mat3).transpose⁻¹ = (codeMat 241 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 489 : Mat3).transpose * (codeMat 241 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc213s11_contain :
    (o213SourceU_wc ⟨11, by omega⟩) ≤ actionW (codeMat 157) (codeMat 489) o78W_wc := by
  change spanCodes [276, 132, 80, 48, 10, 1] ≤ actionW (codeMat 157) (codeMat 489) o78W_wc
  apply step109wc213_spanCodes_le_of_gens [276, 132, 80, 48, 10, 1]
    (actionW (codeMat 157) (codeMat 489) o78W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 262 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 262 (by decide)
    have hact : actionA (codeMat 157) (codeMat 489) (codeMat 262) = codeMat 276 := by
      unfold actionA
      rw [step109wc213s11_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 262 * (codeMat 241 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 148 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 148 (by decide)
    have hact : actionA (codeMat 157) (codeMat 489) (codeMat 148) = codeMat 132 := by
      unfold actionA
      rw [step109wc213s11_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 148 * (codeMat 241 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 255 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 255 (by decide)
    have hact : actionA (codeMat 157) (codeMat 489) (codeMat 255) = codeMat 80 := by
      unfold actionA
      rw [step109wc213s11_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 255 * (codeMat 241 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 157) (codeMat 489) (codeMat 128) = codeMat 48 := by
      unfold actionA
      rw [step109wc213s11_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 128 * (codeMat 241 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 224 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 224 (by decide)
    have hact : actionA (codeMat 157) (codeMat 489) (codeMat 224) = codeMat 10 := by
      unfold actionA
      rw [step109wc213s11_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 224 * (codeMat 241 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 504 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 504 (by decide)
    have hact : actionA (codeMat 157) (codeMat 489) (codeMat 504) = codeMat 1 := by
      unfold actionA
      rw [step109wc213s11_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 504 * (codeMat 241 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact

theorem step109wc213s11Dispatch :
    QuotientRankAtLeast (o213SourceU_wc ⟨11, by omega⟩) 14 := by
  have hP : Invertible (codeMat 157 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 489 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 157) (codeMat 489) o78W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 157) (codeMat 489) hP hQ o78W_wc 14
      step109_orbit78_lb14_wc
  exact quotientRankAtLeast_mono step109wc213s11_contain hAct


private theorem step109wc213s12_QtInv :
    (codeMat 485 : Mat3).transpose⁻¹ = (codeMat 171 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 485 : Mat3).transpose * (codeMat 171 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc213s12_contain :
    (o213SourceU_wc ⟨12, by omega⟩) ≤ actionW (codeMat 279) (codeMat 485) o78W_wc := by
  change spanCodes [276, 132, 84, 52, 10, 1] ≤ actionW (codeMat 279) (codeMat 485) o78W_wc
  apply step109wc213_spanCodes_le_of_gens [276, 132, 84, 52, 10, 1]
    (actionW (codeMat 279) (codeMat 485) o78W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 31 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 31 (by decide)
    have hact : actionA (codeMat 279) (codeMat 485) (codeMat 31) = codeMat 276 := by
      unfold actionA
      rw [step109wc213s12_QtInv]
      show (codeMat 279 : Mat3).transpose * codeMat 31 * (codeMat 171 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 255 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 255 (by decide)
    have hact : actionA (codeMat 279) (codeMat 485) (codeMat 255) = codeMat 132 := by
      unfold actionA
      rw [step109wc213s12_QtInv]
      show (codeMat 279 : Mat3).transpose * codeMat 255 * (codeMat 171 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 159 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 159 (by decide)
    have hact : actionA (codeMat 279) (codeMat 485) (codeMat 159) = codeMat 84 := by
      unfold actionA
      rw [step109wc213s12_QtInv]
      show (codeMat 279 : Mat3).transpose * codeMat 159 * (codeMat 171 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 487 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 487 (by decide)
    have hact : actionA (codeMat 279) (codeMat 485) (codeMat 487) = codeMat 52 := by
      unfold actionA
      rw [step109wc213s12_QtInv]
      show (codeMat 279 : Mat3).transpose * codeMat 487 * (codeMat 171 : Mat3).transpose = codeMat 52
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 268 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 268 (by decide)
    have hact : actionA (codeMat 279) (codeMat 485) (codeMat 268) = codeMat 10 := by
      unfold actionA
      rw [step109wc213s12_QtInv]
      show (codeMat 279 : Mat3).transpose * codeMat 268 * (codeMat 171 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 365 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 365 (by decide)
    have hact : actionA (codeMat 279) (codeMat 485) (codeMat 365) = codeMat 1 := by
      unfold actionA
      rw [step109wc213s12_QtInv]
      show (codeMat 279 : Mat3).transpose * codeMat 365 * (codeMat 171 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact

theorem step109wc213s12Dispatch :
    QuotientRankAtLeast (o213SourceU_wc ⟨12, by omega⟩) 14 := by
  have hP : Invertible (codeMat 279 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 485 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 279) (codeMat 485) o78W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 279) (codeMat 485) hP hQ o78W_wc 14
      step109_orbit78_lb14_wc
  exact quotientRankAtLeast_mono step109wc213s12_contain hAct


private theorem step109wc213s13_QtInv :
    (codeMat 498 : Mat3).transpose⁻¹ = (codeMat 206 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 498 : Mat3).transpose * (codeMat 206 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc213s13_contain :
    (o213SourceU_wc ⟨13, by omega⟩) ≤ actionW (codeMat 419) (codeMat 498) o82W := by
  change spanCodes [276, 132, 86, 54, 10, 1] ≤ actionW (codeMat 419) (codeMat 498) o82W
  apply step109wc213_spanCodes_le_of_gens [276, 132, 86, 54, 10, 1]
    (actionW (codeMat 419) (codeMat 498) o82W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 126 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 126 (by decide)
    have hact : actionA (codeMat 419) (codeMat 498) (codeMat 126) = codeMat 276 := by
      unfold actionA
      rw [step109wc213s13_QtInv]
      show (codeMat 419 : Mat3).transpose * codeMat 126 * (codeMat 206 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 398 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 398 (by decide)
    have hact : actionA (codeMat 419) (codeMat 498) (codeMat 398) = codeMat 132 := by
      unfold actionA
      rw [step109wc213s13_QtInv]
      show (codeMat 419 : Mat3).transpose * codeMat 398 * (codeMat 206 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 401 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 401 (by decide)
    have hact : actionA (codeMat 419) (codeMat 498) (codeMat 401) = codeMat 86 := by
      unfold actionA
      rw [step109wc213s13_QtInv]
      show (codeMat 419 : Mat3).transpose * codeMat 401 * (codeMat 206 : Mat3).transpose = codeMat 86
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 419) (codeMat 498) (codeMat 1) = codeMat 54 := by
      unfold actionA
      rw [step109wc213s13_QtInv]
      show (codeMat 419 : Mat3).transpose * codeMat 1 * (codeMat 206 : Mat3).transpose = codeMat 54
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 223 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 223 (by decide)
    have hact : actionA (codeMat 419) (codeMat 498) (codeMat 223) = codeMat 10 := by
      unfold actionA
      rw [step109wc213s13_QtInv]
      show (codeMat 419 : Mat3).transpose * codeMat 223 * (codeMat 206 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 292 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 292 (by decide)
    have hact : actionA (codeMat 419) (codeMat 498) (codeMat 292) = codeMat 1 := by
      unfold actionA
      rw [step109wc213s13_QtInv]
      show (codeMat 419 : Mat3).transpose * codeMat 292 * (codeMat 206 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact

theorem step109wc213s13Dispatch :
    QuotientRankAtLeast (o213SourceU_wc ⟨13, by omega⟩) 14 := by
  have hP : Invertible (codeMat 419 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 498 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 419) (codeMat 498) o82W) 14 :=
    @quotientRankAtLeast_action (codeMat 419) (codeMat 498) hP hQ o82W 14
      step99_orbit82_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc213s13_contain hAct


private theorem step109wc213s14_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc213s14_contain :
    (o213SourceU_wc ⟨14, by omega⟩) ≤ actionW (codeMat 337) (codeMat 273) o50W_wc := by
  change spanCodes [276, 132, 96, 8, 2, 1] ≤ actionW (codeMat 337) (codeMat 273) o50W_wc
  apply step109wc213_spanCodes_le_of_gens [276, 132, 96, 8, 2, 1]
    (actionW (codeMat 337) (codeMat 273) o50W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 272 ∈ o50W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 8, 2, 1] 272 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 272) = codeMat 276 := by
      unfold actionA
      rw [step109wc213s14_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 272 * (codeMat 273 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 134 ∈ o50W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 8, 2, 1] 134 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 134) = codeMat 132 := by
      unfold actionA
      rw [step109wc213s14_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 134 * (codeMat 273 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 97 ∈ o50W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 8, 2, 1] 97 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 97) = codeMat 96 := by
      unfold actionA
      rw [step109wc213s14_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 97 * (codeMat 273 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ o50W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc213s14_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o50W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc213s14_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o50W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc213s14_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc213_codeMat_mem_actionW_of_witness hw hact

theorem step109wc213s14Dispatch :
    QuotientRankAtLeast (o213SourceU_wc ⟨14, by omega⟩) 13 := by
  have hP : Invertible (codeMat 337 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 337) (codeMat 273) o50W_wc) 13 :=
    @quotientRankAtLeast_action (codeMat 337) (codeMat 273) hP hQ o50W_wc 13
      step109_orbit50_lb13_wc
  exact quotientRankAtLeast_mono step109wc213s14_contain hAct

theorem step109wc213_all_dispatch (i : Fin 15) :
    QuotientRankAtLeast (o213SourceU_wc i) (o213SourceLb_wc i) := by
  fin_cases i
  · exact step109wc213s0Dispatch
  · exact step109wc213s1Dispatch
  · exact step109wc213s2Dispatch
  · exact step109wc213s3Dispatch
  · exact step109wc213s4Dispatch
  · exact step109wc213s5Dispatch
  · exact step109wc213s6Dispatch
  · exact step109wc213s7Dispatch
  · exact step109wc213s8Dispatch
  · exact step109wc213s9Dispatch
  · exact step109wc213s10Dispatch
  · exact step109wc213s11Dispatch
  · exact step109wc213s12Dispatch
  · exact step109wc213s13Dispatch
  · exact step109wc213s14Dispatch

theorem step109_orbit213_lb16_wc : QuotientRankAtLeast o213W_wc 16 :=
  o213Lb16_wc step109wc213_all_dispatch

end QiushiMatmul
