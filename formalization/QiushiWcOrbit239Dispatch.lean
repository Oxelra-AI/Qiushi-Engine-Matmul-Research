import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit239Consumer
import QiushiStep99Orbit67Dispatch
import QiushiStep99Orbit76Dispatch
import QiushiWcOrbit81Dispatch
import QiushiStep99Orbit68Dispatch
import QiushiWcOrbit79Dispatch

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc239_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc239_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc239s0_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = (codeMat 275 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * (codeMat 275 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc239s0_contain :
    (o239SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 273) (codeMat 275) o67W := by
  change spanCodes [262, 160, 68, 18, 10, 1] ≤ actionW (codeMat 273) (codeMat 275) o67W
  apply step109wc239_spanCodes_le_of_gens [262, 160, 68, 18, 10, 1]
    (actionW (codeMat 273) (codeMat 275) o67W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 263 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 263 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 263) = codeMat 262 := by
      unfold actionA
      rw [step109wc239s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 263 * (codeMat 275 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 224 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 224 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 224) = codeMat 160 := by
      unfold actionA
      rw [step109wc239s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 224 * (codeMat 275 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step109wc239s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 68 * (codeMat 275 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 27 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 27) = codeMat 18 := by
      unfold actionA
      rw [step109wc239s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 27 * (codeMat 275 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 11 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 11) = codeMat 10 := by
      unfold actionA
      rw [step109wc239s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 11 * (codeMat 275 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc239s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 275 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact

theorem step109wc239s0Dispatch :
    QuotientRankAtLeast (o239SourceU_wc ⟨0, by omega⟩) 15 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 275) o67W) 15 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 275) hP hQ o67W 15
      step99_orbit67_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc239s0_contain hAct


private theorem step109wc239s1_QtInv :
    (codeMat 370 : Mat3).transpose⁻¹ = (codeMat 207 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 370 : Mat3).transpose * (codeMat 207 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc239s1_contain :
    (o239SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 111) (codeMat 370) o76W := by
  change spanCodes [258, 160, 64, 19, 10, 4] ≤ actionW (codeMat 111) (codeMat 370) o76W
  apply step109wc239_spanCodes_le_of_gens [258, 160, 64, 19, 10, 4]
    (actionW (codeMat 111) (codeMat 370) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 368 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 368 (by decide)
    have hact : actionA (codeMat 111) (codeMat 370) (codeMat 368) = codeMat 258 := by
      unfold actionA
      rw [step109wc239s1_QtInv]
      show (codeMat 111 : Mat3).transpose * codeMat 368 * (codeMat 207 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 238 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 238 (by decide)
    have hact : actionA (codeMat 111) (codeMat 370) (codeMat 238) = codeMat 160 := by
      unfold actionA
      rw [step109wc239s1_QtInv]
      show (codeMat 111 : Mat3).transpose * codeMat 238 * (codeMat 207 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 288 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 111) (codeMat 370) (codeMat 288) = codeMat 64 := by
      unfold actionA
      rw [step109wc239s1_QtInv]
      show (codeMat 111 : Mat3).transpose * codeMat 288 * (codeMat 207 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 475 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 475 (by decide)
    have hact : actionA (codeMat 111) (codeMat 370) (codeMat 475) = codeMat 19 := by
      unfold actionA
      rw [step109wc239s1_QtInv]
      show (codeMat 111 : Mat3).transpose * codeMat 475 * (codeMat 207 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 228 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 228 (by decide)
    have hact : actionA (codeMat 111) (codeMat 370) (codeMat 228) = codeMat 10 := by
      unfold actionA
      rw [step109wc239s1_QtInv]
      show (codeMat 111 : Mat3).transpose * codeMat 228 * (codeMat 207 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 384 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 384 (by decide)
    have hact : actionA (codeMat 111) (codeMat 370) (codeMat 384) = codeMat 4 := by
      unfold actionA
      rw [step109wc239s1_QtInv]
      show (codeMat 111 : Mat3).transpose * codeMat 384 * (codeMat 207 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact

theorem step109wc239s1Dispatch :
    QuotientRankAtLeast (o239SourceU_wc ⟨1, by omega⟩) 15 := by
  have hP : Invertible (codeMat 111 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 370 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 111) (codeMat 370) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 111) (codeMat 370) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc239s1_contain hAct


private theorem step109wc239s2_QtInv :
    (codeMat 114 : Mat3).transpose⁻¹ = (codeMat 204 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 114 : Mat3).transpose * (codeMat 204 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc239s2_contain :
    (o239SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 102) (codeMat 114) o76W := by
  change spanCodes [259, 160, 65, 19, 10, 5] ≤ actionW (codeMat 102) (codeMat 114) o76W
  apply step109wc239_spanCodes_le_of_gens [259, 160, 65, 19, 10, 5]
    (actionW (codeMat 102) (codeMat 114) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 464 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 464 (by decide)
    have hact : actionA (codeMat 102) (codeMat 114) (codeMat 464) = codeMat 259 := by
      unfold actionA
      rw [step109wc239s2_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 464 * (codeMat 204 : Mat3).transpose = codeMat 259
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 10 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 102) (codeMat 114) (codeMat 10) = codeMat 160 := by
      unfold actionA
      rw [step109wc239s2_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 10 * (codeMat 204 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 288 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 102) (codeMat 114) (codeMat 288) = codeMat 65 := by
      unfold actionA
      rw [step109wc239s2_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 288 * (codeMat 204 : Mat3).transpose = codeMat 65
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 475 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 475 (by decide)
    have hact : actionA (codeMat 102) (codeMat 114) (codeMat 475) = codeMat 19 := by
      unfold actionA
      rw [step109wc239s2_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 475 * (codeMat 204 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 228 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 228 (by decide)
    have hact : actionA (codeMat 102) (codeMat 114) (codeMat 228) = codeMat 10 := by
      unfold actionA
      rw [step109wc239s2_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 228 * (codeMat 204 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 384 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 384 (by decide)
    have hact : actionA (codeMat 102) (codeMat 114) (codeMat 384) = codeMat 5 := by
      unfold actionA
      rw [step109wc239s2_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 384 * (codeMat 204 : Mat3).transpose = codeMat 5
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact

theorem step109wc239s2Dispatch :
    QuotientRankAtLeast (o239SourceU_wc ⟨2, by omega⟩) 15 := by
  have hP : Invertible (codeMat 102 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 114 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 102) (codeMat 114) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 102) (codeMat 114) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc239s2_contain hAct


private theorem step109wc239s3_QtInv :
    (codeMat 214 : Mat3).transpose⁻¹ = (codeMat 214 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 214 : Mat3).transpose * (codeMat 214 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc239s3_contain :
    (o239SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 124) (codeMat 214) o76W := by
  change spanCodes [256, 160, 66, 19, 10, 6] ≤ actionW (codeMat 124) (codeMat 214) o76W
  apply step109wc239_spanCodes_le_of_gens [256, 160, 66, 19, 10, 6]
    (actionW (codeMat 124) (codeMat 214) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 1 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 124) (codeMat 214) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc239s3_QtInv]
      show (codeMat 124 : Mat3).transpose * codeMat 1 * (codeMat 214 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 78 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 124) (codeMat 214) (codeMat 78) = codeMat 160 := by
      unfold actionA
      rw [step109wc239s3_QtInv]
      show (codeMat 124 : Mat3).transpose * codeMat 78 * (codeMat 214 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 452 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 452 (by decide)
    have hact : actionA (codeMat 124) (codeMat 214) (codeMat 452) = codeMat 66 := by
      unfold actionA
      rw [step109wc239s3_QtInv]
      show (codeMat 124 : Mat3).transpose * codeMat 452 * (codeMat 214 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 319 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 319 (by decide)
    have hact : actionA (codeMat 124) (codeMat 214) (codeMat 319) = codeMat 19 := by
      unfold actionA
      rw [step109wc239s3_QtInv]
      show (codeMat 124 : Mat3).transpose * codeMat 319 * (codeMat 214 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 228 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 228 (by decide)
    have hact : actionA (codeMat 124) (codeMat 214) (codeMat 228) = codeMat 10 := by
      unfold actionA
      rw [step109wc239s3_QtInv]
      show (codeMat 124 : Mat3).transpose * codeMat 228 * (codeMat 214 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 384 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 384 (by decide)
    have hact : actionA (codeMat 124) (codeMat 214) (codeMat 384) = codeMat 6 := by
      unfold actionA
      rw [step109wc239s3_QtInv]
      show (codeMat 124 : Mat3).transpose * codeMat 384 * (codeMat 214 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact

theorem step109wc239s3Dispatch :
    QuotientRankAtLeast (o239SourceU_wc ⟨3, by omega⟩) 15 := by
  have hP : Invertible (codeMat 124 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 214 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 124) (codeMat 214) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 124) (codeMat 214) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc239s3_contain hAct


private theorem step109wc239s4_QtInv :
    (codeMat 470 : Mat3).transpose⁻¹ = (codeMat 213 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 470 : Mat3).transpose * (codeMat 213 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc239s4_contain :
    (o239SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 117) (codeMat 470) o76W := by
  change spanCodes [257, 160, 67, 19, 10, 7] ≤ actionW (codeMat 117) (codeMat 470) o76W
  apply step109wc239_spanCodes_le_of_gens [257, 160, 67, 19, 10, 7]
    (actionW (codeMat 117) (codeMat 470) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 69 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 117) (codeMat 470) (codeMat 69) = codeMat 257 := by
      unfold actionA
      rw [step109wc239s4_QtInv]
      show (codeMat 117 : Mat3).transpose * codeMat 69 * (codeMat 213 : Mat3).transpose = codeMat 257
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 170 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 170 (by decide)
    have hact : actionA (codeMat 117) (codeMat 470) (codeMat 170) = codeMat 160 := by
      unfold actionA
      rw [step109wc239s4_QtInv]
      show (codeMat 117 : Mat3).transpose * codeMat 170 * (codeMat 213 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 452 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 452 (by decide)
    have hact : actionA (codeMat 117) (codeMat 470) (codeMat 452) = codeMat 67 := by
      unfold actionA
      rw [step109wc239s4_QtInv]
      show (codeMat 117 : Mat3).transpose * codeMat 452 * (codeMat 213 : Mat3).transpose = codeMat 67
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 319 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 319 (by decide)
    have hact : actionA (codeMat 117) (codeMat 470) (codeMat 319) = codeMat 19 := by
      unfold actionA
      rw [step109wc239s4_QtInv]
      show (codeMat 117 : Mat3).transpose * codeMat 319 * (codeMat 213 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 228 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 228 (by decide)
    have hact : actionA (codeMat 117) (codeMat 470) (codeMat 228) = codeMat 10 := by
      unfold actionA
      rw [step109wc239s4_QtInv]
      show (codeMat 117 : Mat3).transpose * codeMat 228 * (codeMat 213 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 384 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 384 (by decide)
    have hact : actionA (codeMat 117) (codeMat 470) (codeMat 384) = codeMat 7 := by
      unfold actionA
      rw [step109wc239s4_QtInv]
      show (codeMat 117 : Mat3).transpose * codeMat 384 * (codeMat 213 : Mat3).transpose = codeMat 7
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact

theorem step109wc239s4Dispatch :
    QuotientRankAtLeast (o239SourceU_wc ⟨4, by omega⟩) 15 := by
  have hP : Invertible (codeMat 117 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 470 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 117) (codeMat 470) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 117) (codeMat 470) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc239s4_contain hAct


private theorem step109wc239s5_QtInv :
    (codeMat 370 : Mat3).transpose⁻¹ = (codeMat 207 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 370 : Mat3).transpose * (codeMat 207 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc239s5_contain :
    (o239SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 482) (codeMat 370) o81W_wc := by
  change spanCodes [262, 129, 68, 33, 19, 10] ≤ actionW (codeMat 482) (codeMat 370) o81W_wc
  apply step109wc239_spanCodes_le_of_gens [262, 129, 68, 33, 19, 10]
    (actionW (codeMat 482) (codeMat 370) o81W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 349 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 349 (by decide)
    have hact : actionA (codeMat 482) (codeMat 370) (codeMat 349) = codeMat 262 := by
      unfold actionA
      rw [step109wc239s5_QtInv]
      show (codeMat 482 : Mat3).transpose * codeMat 349 * (codeMat 207 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 316 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 316 (by decide)
    have hact : actionA (codeMat 482) (codeMat 370) (codeMat 316) = codeMat 129 := by
      unfold actionA
      rw [step109wc239s5_QtInv]
      show (codeMat 482 : Mat3).transpose * codeMat 316 * (codeMat 207 : Mat3).transpose = codeMat 129
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 406 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 406 (by decide)
    have hact : actionA (codeMat 482) (codeMat 370) (codeMat 406) = codeMat 68 := by
      unfold actionA
      rw [step109wc239s5_QtInv]
      show (codeMat 482 : Mat3).transpose * codeMat 406 * (codeMat 207 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 290 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 290 (by decide)
    have hact : actionA (codeMat 482) (codeMat 370) (codeMat 290) = codeMat 33 := by
      unfold actionA
      rw [step109wc239s5_QtInv]
      show (codeMat 482 : Mat3).transpose * codeMat 290 * (codeMat 207 : Mat3).transpose = codeMat 33
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 508 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 508 (by decide)
    have hact : actionA (codeMat 482) (codeMat 370) (codeMat 508) = codeMat 19 := by
      unfold actionA
      rw [step109wc239s5_QtInv]
      show (codeMat 482 : Mat3).transpose * codeMat 508 * (codeMat 207 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 223 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 223 (by decide)
    have hact : actionA (codeMat 482) (codeMat 370) (codeMat 223) = codeMat 10 := by
      unfold actionA
      rw [step109wc239s5_QtInv]
      show (codeMat 482 : Mat3).transpose * codeMat 223 * (codeMat 207 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact

theorem step109wc239s5Dispatch :
    QuotientRankAtLeast (o239SourceU_wc ⟨5, by omega⟩) 15 := by
  have hP : Invertible (codeMat 482 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 370 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 482) (codeMat 370) o81W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 482) (codeMat 370) hP hQ o81W_wc 15
      step109_orbit81_lb15_wc
  exact quotientRankAtLeast_mono step109wc239s5_contain hAct


private theorem step109wc239s6_QtInv :
    (codeMat 114 : Mat3).transpose⁻¹ = (codeMat 204 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 114 : Mat3).transpose * (codeMat 204 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc239s6_contain :
    (o239SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 426) (codeMat 114) o81W_wc := by
  change spanCodes [262, 131, 68, 35, 19, 10] ≤ actionW (codeMat 426) (codeMat 114) o81W_wc
  apply step109wc239_spanCodes_le_of_gens [262, 131, 68, 35, 19, 10]
    (actionW (codeMat 426) (codeMat 114) o81W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 203 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 203 (by decide)
    have hact : actionA (codeMat 426) (codeMat 114) (codeMat 203) = codeMat 262 := by
      unfold actionA
      rw [step109wc239s6_QtInv]
      show (codeMat 426 : Mat3).transpose * codeMat 203 * (codeMat 204 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 316 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 316 (by decide)
    have hact : actionA (codeMat 426) (codeMat 114) (codeMat 316) = codeMat 131 := by
      unfold actionA
      rw [step109wc239s6_QtInv]
      show (codeMat 426 : Mat3).transpose * codeMat 316 * (codeMat 204 : Mat3).transpose = codeMat 131
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 406 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 406 (by decide)
    have hact : actionA (codeMat 426) (codeMat 114) (codeMat 406) = codeMat 68 := by
      unfold actionA
      rw [step109wc239s6_QtInv]
      show (codeMat 426 : Mat3).transpose * codeMat 406 * (codeMat 204 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 509 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 509 (by decide)
    have hact : actionA (codeMat 426) (codeMat 114) (codeMat 509) = codeMat 35 := by
      unfold actionA
      rw [step109wc239s6_QtInv]
      show (codeMat 426 : Mat3).transpose * codeMat 509 * (codeMat 204 : Mat3).transpose = codeMat 35
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 508 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 508 (by decide)
    have hact : actionA (codeMat 426) (codeMat 114) (codeMat 508) = codeMat 19 := by
      unfold actionA
      rw [step109wc239s6_QtInv]
      show (codeMat 426 : Mat3).transpose * codeMat 508 * (codeMat 204 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 223 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 223 (by decide)
    have hact : actionA (codeMat 426) (codeMat 114) (codeMat 223) = codeMat 10 := by
      unfold actionA
      rw [step109wc239s6_QtInv]
      show (codeMat 426 : Mat3).transpose * codeMat 223 * (codeMat 204 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact

theorem step109wc239s6Dispatch :
    QuotientRankAtLeast (o239SourceU_wc ⟨6, by omega⟩) 15 := by
  have hP : Invertible (codeMat 426 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 114 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 426) (codeMat 114) o81W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 426) (codeMat 114) hP hQ o81W_wc 15
      step109_orbit81_lb15_wc
  exact quotientRankAtLeast_mono step109wc239s6_contain hAct


private theorem step109wc239s7_QtInv :
    (codeMat 205 : Mat3).transpose⁻¹ = (codeMat 242 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 205 : Mat3).transpose * (codeMat 242 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc239s7_contain :
    (o239SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 299) (codeMat 205) o81W_wc := by
  change spanCodes [262, 132, 68, 36, 19, 10] ≤ actionW (codeMat 299) (codeMat 205) o81W_wc
  apply step109wc239_spanCodes_le_of_gens [262, 132, 68, 36, 19, 10]
    (actionW (codeMat 299) (codeMat 205) o81W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 296 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 296 (by decide)
    have hact : actionA (codeMat 299) (codeMat 205) (codeMat 296) = codeMat 262 := by
      unfold actionA
      rw [step109wc239s7_QtInv]
      show (codeMat 299 : Mat3).transpose * codeMat 296 * (codeMat 242 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 328 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 328 (by decide)
    have hact : actionA (codeMat 299) (codeMat 205) (codeMat 328) = codeMat 132 := by
      unfold actionA
      rw [step109wc239s7_QtInv]
      show (codeMat 299 : Mat3).transpose * codeMat 328 * (codeMat 242 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 392 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 392 (by decide)
    have hact : actionA (codeMat 299) (codeMat 205) (codeMat 392) = codeMat 68 := by
      unfold actionA
      rw [step109wc239s7_QtInv]
      show (codeMat 299 : Mat3).transpose * codeMat 392 * (codeMat 242 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 299) (codeMat 205) (codeMat 1) = codeMat 36 := by
      unfold actionA
      rw [step109wc239s7_QtInv]
      show (codeMat 299 : Mat3).transpose * codeMat 1 * (codeMat 242 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 508 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 508 (by decide)
    have hact : actionA (codeMat 299) (codeMat 205) (codeMat 508) = codeMat 19 := by
      unfold actionA
      rw [step109wc239s7_QtInv]
      show (codeMat 299 : Mat3).transpose * codeMat 508 * (codeMat 242 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 223 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 223 (by decide)
    have hact : actionA (codeMat 299) (codeMat 205) (codeMat 223) = codeMat 10 := by
      unfold actionA
      rw [step109wc239s7_QtInv]
      show (codeMat 299 : Mat3).transpose * codeMat 223 * (codeMat 242 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact

theorem step109wc239s7Dispatch :
    QuotientRankAtLeast (o239SourceU_wc ⟨7, by omega⟩) 15 := by
  have hP : Invertible (codeMat 299 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 205 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 299) (codeMat 205) o81W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 299) (codeMat 205) hP hQ o81W_wc 15
      step109_orbit81_lb15_wc
  exact quotientRankAtLeast_mono step109wc239s7_contain hAct


private theorem step109wc239s8_QtInv :
    (codeMat 489 : Mat3).transpose⁻¹ = (codeMat 241 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 489 : Mat3).transpose * (codeMat 241 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc239s8_contain :
    (o239SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 355) (codeMat 489) o81W_wc := by
  change spanCodes [262, 135, 68, 39, 19, 10] ≤ actionW (codeMat 355) (codeMat 489) o81W_wc
  apply step109wc239_spanCodes_le_of_gens [262, 135, 68, 39, 19, 10]
    (actionW (codeMat 355) (codeMat 489) o81W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 160 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 355) (codeMat 489) (codeMat 160) = codeMat 262 := by
      unfold actionA
      rw [step109wc239s8_QtInv]
      show (codeMat 355 : Mat3).transpose * codeMat 160 * (codeMat 241 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 328 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 328 (by decide)
    have hact : actionA (codeMat 355) (codeMat 489) (codeMat 328) = codeMat 135 := by
      unfold actionA
      rw [step109wc239s8_QtInv]
      show (codeMat 355 : Mat3).transpose * codeMat 328 * (codeMat 241 : Mat3).transpose = codeMat 135
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 392 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 392 (by decide)
    have hact : actionA (codeMat 355) (codeMat 489) (codeMat 392) = codeMat 68 := by
      unfold actionA
      rw [step109wc239s8_QtInv]
      show (codeMat 355 : Mat3).transpose * codeMat 392 * (codeMat 241 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 222 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 222 (by decide)
    have hact : actionA (codeMat 355) (codeMat 489) (codeMat 222) = codeMat 39 := by
      unfold actionA
      rw [step109wc239s8_QtInv]
      show (codeMat 355 : Mat3).transpose * codeMat 222 * (codeMat 241 : Mat3).transpose = codeMat 39
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 508 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 508 (by decide)
    have hact : actionA (codeMat 355) (codeMat 489) (codeMat 508) = codeMat 19 := by
      unfold actionA
      rw [step109wc239s8_QtInv]
      show (codeMat 355 : Mat3).transpose * codeMat 508 * (codeMat 241 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 223 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 223 (by decide)
    have hact : actionA (codeMat 355) (codeMat 489) (codeMat 223) = codeMat 10 := by
      unfold actionA
      rw [step109wc239s8_QtInv]
      show (codeMat 355 : Mat3).transpose * codeMat 223 * (codeMat 241 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact

theorem step109wc239s8Dispatch :
    QuotientRankAtLeast (o239SourceU_wc ⟨8, by omega⟩) 15 := by
  have hP : Invertible (codeMat 355 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 489 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 355) (codeMat 489) o81W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 355) (codeMat 489) hP hQ o81W_wc 15
      step109_orbit81_lb15_wc
  exact quotientRankAtLeast_mono step109wc239s8_contain hAct


private theorem step109wc239s9_QtInv :
    (codeMat 281 : Mat3).transpose⁻¹ = (codeMat 281 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 281 : Mat3).transpose * (codeMat 281 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc239s9_contain :
    (o239SourceU_wc ⟨9, by omega⟩) ≤ actionW (codeMat 267) (codeMat 281) o68W := by
  change spanCodes [260, 160, 68, 17, 8, 2] ≤ actionW (codeMat 267) (codeMat 281) o68W
  apply step109wc239_spanCodes_le_of_gens [260, 160, 68, 17, 8, 2]
    (actionW (codeMat 267) (codeMat 281) o68W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 288 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 267) (codeMat 281) (codeMat 288) = codeMat 260 := by
      unfold actionA
      rw [step109wc239s9_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 288 * (codeMat 281 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 164 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 164 (by decide)
    have hact : actionA (codeMat 267) (codeMat 281) (codeMat 164) = codeMat 160 := by
      unfold actionA
      rw [step109wc239s9_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 164 * (codeMat 281 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 224 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 224 (by decide)
    have hact : actionA (codeMat 267) (codeMat 281) (codeMat 224) = codeMat 68 := by
      unfold actionA
      rw [step109wc239s9_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 224 * (codeMat 281 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 10 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 267) (codeMat 281) (codeMat 10) = codeMat 17 := by
      unfold actionA
      rw [step109wc239s9_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 10 * (codeMat 281 : Mat3).transpose = codeMat 17
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 27 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 267) (codeMat 281) (codeMat 27) = codeMat 8 := by
      unfold actionA
      rw [step109wc239s9_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 27 * (codeMat 281 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 267) (codeMat 281) (codeMat 16) = codeMat 2 := by
      unfold actionA
      rw [step109wc239s9_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 16 * (codeMat 281 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact

theorem step109wc239s9Dispatch :
    QuotientRankAtLeast (o239SourceU_wc ⟨9, by omega⟩) 14 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 281) o68W) 14 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 281) hP hQ o68W 14
      step99_orbit68_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc239s9_contain hAct


private theorem step109wc239s10_QtInv :
    (codeMat 271 : Mat3).transpose⁻¹ = (codeMat 314 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 271 : Mat3).transpose * (codeMat 314 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc239s10_contain :
    (o239SourceU_wc ⟨10, by omega⟩) ≤ actionW (codeMat 394) (codeMat 271) o68W := by
  change spanCodes [261, 160, 68, 16, 9, 3] ≤ actionW (codeMat 394) (codeMat 271) o68W
  apply step109wc239_spanCodes_le_of_gens [261, 160, 68, 16, 9, 3]
    (actionW (codeMat 394) (codeMat 271) o68W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 373 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 373 (by decide)
    have hact : actionA (codeMat 394) (codeMat 271) (codeMat 373) = codeMat 261 := by
      unfold actionA
      rw [step109wc239s10_QtInv]
      show (codeMat 394 : Mat3).transpose * codeMat 373 * (codeMat 314 : Mat3).transpose = codeMat 261
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 394) (codeMat 271) (codeMat 68) = codeMat 160 := by
      unfold actionA
      rw [step109wc239s10_QtInv]
      show (codeMat 394 : Mat3).transpose * codeMat 68 * (codeMat 314 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 235 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 235 (by decide)
    have hact : actionA (codeMat 394) (codeMat 271) (codeMat 235) = codeMat 68 := by
      unfold actionA
      rw [step109wc239s10_QtInv]
      show (codeMat 394 : Mat3).transpose * codeMat 235 * (codeMat 314 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 394) (codeMat 271) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc239s10_QtInv]
      show (codeMat 394 : Mat3).transpose * codeMat 1 * (codeMat 314 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 27 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 394) (codeMat 271) (codeMat 27) = codeMat 9 := by
      unfold actionA
      rw [step109wc239s10_QtInv]
      show (codeMat 394 : Mat3).transpose * codeMat 27 * (codeMat 314 : Mat3).transpose = codeMat 9
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 394) (codeMat 271) (codeMat 16) = codeMat 3 := by
      unfold actionA
      rw [step109wc239s10_QtInv]
      show (codeMat 394 : Mat3).transpose * codeMat 16 * (codeMat 314 : Mat3).transpose = codeMat 3
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact

theorem step109wc239s10Dispatch :
    QuotientRankAtLeast (o239SourceU_wc ⟨10, by omega⟩) 14 := by
  have hP : Invertible (codeMat 394 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 271 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 394) (codeMat 271) o68W) 14 :=
    @quotientRankAtLeast_action (codeMat 394) (codeMat 271) hP hQ o68W 14
      step99_orbit68_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc239s10_contain hAct


private theorem step109wc239s11_QtInv :
    (codeMat 491 : Mat3).transpose⁻¹ = (codeMat 375 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 491 : Mat3).transpose * (codeMat 375 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc239s11_contain :
    (o239SourceU_wc ⟨11, by omega⟩) ≤ actionW (codeMat 334) (codeMat 491) o79W_wc := by
  change spanCodes [262, 128, 68, 32, 19, 10] ≤ actionW (codeMat 334) (codeMat 491) o79W_wc
  apply step109wc239_spanCodes_le_of_gens [262, 128, 68, 32, 19, 10]
    (actionW (codeMat 334) (codeMat 491) o79W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 424 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 424 (by decide)
    have hact : actionA (codeMat 334) (codeMat 491) (codeMat 424) = codeMat 262 := by
      unfold actionA
      rw [step109wc239s11_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 424 * (codeMat 375 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 360 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 360 (by decide)
    have hact : actionA (codeMat 334) (codeMat 491) (codeMat 360) = codeMat 128 := by
      unfold actionA
      rw [step109wc239s11_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 360 * (codeMat 375 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 456 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 456 (by decide)
    have hact : actionA (codeMat 334) (codeMat 491) (codeMat 456) = codeMat 68 := by
      unfold actionA
      rw [step109wc239s11_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 456 * (codeMat 375 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 438 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 438 (by decide)
    have hact : actionA (codeMat 334) (codeMat 491) (codeMat 438) = codeMat 32 := by
      unfold actionA
      rw [step109wc239s11_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 438 * (codeMat 375 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 381 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 381 (by decide)
    have hact : actionA (codeMat 334) (codeMat 491) (codeMat 381) = codeMat 19 := by
      unfold actionA
      rw [step109wc239s11_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 381 * (codeMat 375 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 471 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 471 (by decide)
    have hact : actionA (codeMat 334) (codeMat 491) (codeMat 471) = codeMat 10 := by
      unfold actionA
      rw [step109wc239s11_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 471 * (codeMat 375 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact

theorem step109wc239s11Dispatch :
    QuotientRankAtLeast (o239SourceU_wc ⟨11, by omega⟩) 14 := by
  have hP : Invertible (codeMat 334 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 491 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 334) (codeMat 491) o79W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 334) (codeMat 491) hP hQ o79W_wc 14
      step109_orbit79_lb14_wc
  exact quotientRankAtLeast_mono step109wc239s11_contain hAct


private theorem step109wc239s12_QtInv :
    (codeMat 207 : Mat3).transpose⁻¹ = (codeMat 370 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 207 : Mat3).transpose * (codeMat 370 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc239s12_contain :
    (o239SourceU_wc ⟨12, by omega⟩) ≤ actionW (codeMat 271) (codeMat 207) o79W_wc := by
  change spanCodes [262, 130, 68, 34, 19, 10] ≤ actionW (codeMat 271) (codeMat 207) o79W_wc
  apply step109wc239_spanCodes_le_of_gens [262, 130, 68, 34, 19, 10]
    (actionW (codeMat 271) (codeMat 207) o79W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 96 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 96 (by decide)
    have hact : actionA (codeMat 271) (codeMat 207) (codeMat 96) = codeMat 262 := by
      unfold actionA
      rw [step109wc239s12_QtInv]
      show (codeMat 271 : Mat3).transpose * codeMat 96 * (codeMat 370 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 360 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 360 (by decide)
    have hact : actionA (codeMat 271) (codeMat 207) (codeMat 360) = codeMat 130 := by
      unfold actionA
      rw [step109wc239s12_QtInv]
      show (codeMat 271 : Mat3).transpose * codeMat 360 * (codeMat 370 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 456 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 456 (by decide)
    have hact : actionA (codeMat 271) (codeMat 207) (codeMat 456) = codeMat 68 := by
      unfold actionA
      rw [step109wc239s12_QtInv]
      show (codeMat 271 : Mat3).transpose * codeMat 456 * (codeMat 370 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 97 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 97 (by decide)
    have hact : actionA (codeMat 271) (codeMat 207) (codeMat 97) = codeMat 34 := by
      unfold actionA
      rw [step109wc239s12_QtInv]
      show (codeMat 271 : Mat3).transpose * codeMat 97 * (codeMat 370 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 381 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 381 (by decide)
    have hact : actionA (codeMat 271) (codeMat 207) (codeMat 381) = codeMat 19 := by
      unfold actionA
      rw [step109wc239s12_QtInv]
      show (codeMat 271 : Mat3).transpose * codeMat 381 * (codeMat 370 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 471 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 471 (by decide)
    have hact : actionA (codeMat 271) (codeMat 207) (codeMat 471) = codeMat 10 := by
      unfold actionA
      rw [step109wc239s12_QtInv]
      show (codeMat 271 : Mat3).transpose * codeMat 471 * (codeMat 370 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact

theorem step109wc239s12Dispatch :
    QuotientRankAtLeast (o239SourceU_wc ⟨12, by omega⟩) 14 := by
  have hP : Invertible (codeMat 271 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 207 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 271) (codeMat 207) o79W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 271) (codeMat 207) hP hQ o79W_wc 14
      step109_orbit79_lb14_wc
  exact quotientRankAtLeast_mono step109wc239s12_contain hAct


private theorem step109wc239s13_QtInv :
    (codeMat 345 : Mat3).transpose⁻¹ = (codeMat 345 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 345 : Mat3).transpose * (codeMat 345 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc239s13_contain :
    (o239SourceU_wc ⟨13, by omega⟩) ≤ actionW (codeMat 461) (codeMat 345) o79W_wc := by
  change spanCodes [262, 133, 68, 37, 19, 10] ≤ actionW (codeMat 461) (codeMat 345) o79W_wc
  apply step109wc239_spanCodes_le_of_gens [262, 133, 68, 37, 19, 10]
    (actionW (codeMat 461) (codeMat 345) o79W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 20 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 20 (by decide)
    have hact : actionA (codeMat 461) (codeMat 345) (codeMat 20) = codeMat 262 := by
      unfold actionA
      rw [step109wc239s13_QtInv]
      show (codeMat 461 : Mat3).transpose * codeMat 20 * (codeMat 345 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 10 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 461) (codeMat 345) (codeMat 10) = codeMat 133 := by
      unfold actionA
      rw [step109wc239s13_QtInv]
      show (codeMat 461 : Mat3).transpose * codeMat 10 * (codeMat 345 : Mat3).transpose = codeMat 133
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 31 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 31 (by decide)
    have hact : actionA (codeMat 461) (codeMat 345) (codeMat 31) = codeMat 68 := by
      unfold actionA
      rw [step109wc239s13_QtInv]
      show (codeMat 461 : Mat3).transpose * codeMat 31 * (codeMat 345 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 284 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 284 (by decide)
    have hact : actionA (codeMat 461) (codeMat 345) (codeMat 284) = codeMat 37 := by
      unfold actionA
      rw [step109wc239s13_QtInv]
      show (codeMat 461 : Mat3).transpose * codeMat 284 * (codeMat 345 : Mat3).transpose = codeMat 37
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 170 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 170 (by decide)
    have hact : actionA (codeMat 461) (codeMat 345) (codeMat 170) = codeMat 19 := by
      unfold actionA
      rw [step109wc239s13_QtInv]
      show (codeMat 461 : Mat3).transpose * codeMat 170 * (codeMat 345 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 471 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 471 (by decide)
    have hact : actionA (codeMat 461) (codeMat 345) (codeMat 471) = codeMat 10 := by
      unfold actionA
      rw [step109wc239s13_QtInv]
      show (codeMat 461 : Mat3).transpose * codeMat 471 * (codeMat 345 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact

theorem step109wc239s13Dispatch :
    QuotientRankAtLeast (o239SourceU_wc ⟨13, by omega⟩) 14 := by
  have hP : Invertible (codeMat 461 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 345 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 461) (codeMat 345) o79W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 461) (codeMat 345) hP hQ o79W_wc 14
      step109_orbit79_lb14_wc
  exact quotientRankAtLeast_mono step109wc239s13_contain hAct


private theorem step109wc239s14_QtInv :
    (codeMat 125 : Mat3).transpose⁻¹ = (codeMat 348 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 125 : Mat3).transpose * (codeMat 348 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc239s14_contain :
    (o239SourceU_wc ⟨14, by omega⟩) ≤ actionW (codeMat 396) (codeMat 125) o79W_wc := by
  change spanCodes [262, 134, 68, 38, 19, 10] ≤ actionW (codeMat 396) (codeMat 125) o79W_wc
  apply step109wc239_spanCodes_le_of_gens [262, 134, 68, 38, 19, 10]
    (actionW (codeMat 396) (codeMat 125) o79W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 11 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 396) (codeMat 125) (codeMat 11) = codeMat 262 := by
      unfold actionA
      rw [step109wc239s14_QtInv]
      show (codeMat 396 : Mat3).transpose * codeMat 11 * (codeMat 348 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 10 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 396) (codeMat 125) (codeMat 10) = codeMat 134 := by
      unfold actionA
      rw [step109wc239s14_QtInv]
      show (codeMat 396 : Mat3).transpose * codeMat 10 * (codeMat 348 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 31 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 31 (by decide)
    have hact : actionA (codeMat 396) (codeMat 125) (codeMat 31) = codeMat 68 := by
      unfold actionA
      rw [step109wc239s14_QtInv]
      show (codeMat 396 : Mat3).transpose * codeMat 31 * (codeMat 348 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 203 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 203 (by decide)
    have hact : actionA (codeMat 396) (codeMat 125) (codeMat 203) = codeMat 38 := by
      unfold actionA
      rw [step109wc239s14_QtInv]
      show (codeMat 396 : Mat3).transpose * codeMat 203 * (codeMat 348 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 170 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 170 (by decide)
    have hact : actionA (codeMat 396) (codeMat 125) (codeMat 170) = codeMat 19 := by
      unfold actionA
      rw [step109wc239s14_QtInv]
      show (codeMat 396 : Mat3).transpose * codeMat 170 * (codeMat 348 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 471 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 471 (by decide)
    have hact : actionA (codeMat 396) (codeMat 125) (codeMat 471) = codeMat 10 := by
      unfold actionA
      rw [step109wc239s14_QtInv]
      show (codeMat 396 : Mat3).transpose * codeMat 471 * (codeMat 348 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc239_codeMat_mem_actionW_of_witness hw hact

theorem step109wc239s14Dispatch :
    QuotientRankAtLeast (o239SourceU_wc ⟨14, by omega⟩) 14 := by
  have hP : Invertible (codeMat 396 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 125 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 396) (codeMat 125) o79W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 396) (codeMat 125) hP hQ o79W_wc 14
      step109_orbit79_lb14_wc
  exact quotientRankAtLeast_mono step109wc239s14_contain hAct

theorem step109wc239_all_dispatch (i : Fin 15) :
    QuotientRankAtLeast (o239SourceU_wc i) (o239SourceLb_wc i) := by
  fin_cases i
  · exact step109wc239s0Dispatch
  · exact step109wc239s1Dispatch
  · exact step109wc239s2Dispatch
  · exact step109wc239s3Dispatch
  · exact step109wc239s4Dispatch
  · exact step109wc239s5Dispatch
  · exact step109wc239s6Dispatch
  · exact step109wc239s7Dispatch
  · exact step109wc239s8Dispatch
  · exact step109wc239s9Dispatch
  · exact step109wc239s10Dispatch
  · exact step109wc239s11Dispatch
  · exact step109wc239s12Dispatch
  · exact step109wc239s13Dispatch
  · exact step109wc239s14Dispatch

theorem step109_orbit239_lb16_wc : QuotientRankAtLeast o239W_wc 16 :=
  o239Lb16_wc step109wc239_all_dispatch

end QiushiMatmul
