import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit161Consumer
import QiushiWcOrbit72Dispatch
import QiushiStep99Orbit76Dispatch
import QiushiStep99Orbit34Dispatch
import QiushiStep99Orbit55Dispatch
import QiushiMonoOrbit38From11

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc161_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc161_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc161s0_QtInv :
    (codeMat 340 : Mat3).transpose⁻¹ = (codeMat 85 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 340 : Mat3).transpose * (codeMat 85 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc161s0_contain :
    (o161SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 330) (codeMat 340) o72W_wc := by
  change spanCodes [258, 68, 34, 20, 10, 1] ≤ actionW (codeMat 330) (codeMat 340) o72W_wc
  apply step109wc161_spanCodes_le_of_gens [258, 68, 34, 20, 10, 1]
    (actionW (codeMat 330) (codeMat 340) o72W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 376 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 376 (by decide)
    have hact : actionA (codeMat 330) (codeMat 340) (codeMat 376) = codeMat 258 := by
      unfold actionA
      rw [step109wc161s0_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 376 * (codeMat 85 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 264 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 264 (by decide)
    have hact : actionA (codeMat 330) (codeMat 340) (codeMat 264) = codeMat 68 := by
      unfold actionA
      rw [step109wc161s0_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 264 * (codeMat 85 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 21 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 21 (by decide)
    have hact : actionA (codeMat 330) (codeMat 340) (codeMat 21) = codeMat 34 := by
      unfold actionA
      rw [step109wc161s0_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 21 * (codeMat 85 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 42 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 42 (by decide)
    have hact : actionA (codeMat 330) (codeMat 340) (codeMat 42) = codeMat 20 := by
      unfold actionA
      rw [step109wc161s0_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 42 * (codeMat 85 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 20 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 20 (by decide)
    have hact : actionA (codeMat 330) (codeMat 340) (codeMat 20) = codeMat 10 := by
      unfold actionA
      rw [step109wc161s0_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 20 * (codeMat 85 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 330) (codeMat 340) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc161s0_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 32 * (codeMat 85 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact

theorem step109wc161s0Dispatch :
    QuotientRankAtLeast (o161SourceU_wc ⟨0, by omega⟩) 15 := by
  have hP : Invertible (codeMat 330 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 340 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 330) (codeMat 340) o72W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 330) (codeMat 340) hP hQ o72W_wc 15
      step109_orbit72_lb15_wc
  exact quotientRankAtLeast_mono step109wc161s0_contain hAct


private theorem step109wc161s1_QtInv :
    (codeMat 468 : Mat3).transpose⁻¹ = (codeMat 87 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 468 : Mat3).transpose * (codeMat 87 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc161s1_contain :
    (o161SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 267) (codeMat 468) o72W_wc := by
  change spanCodes [262, 68, 38, 20, 10, 1] ≤ actionW (codeMat 267) (codeMat 468) o72W_wc
  apply step109wc161_spanCodes_le_of_gens [262, 68, 38, 20, 10, 1]
    (actionW (codeMat 267) (codeMat 468) o72W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 344 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 344 (by decide)
    have hact : actionA (codeMat 267) (codeMat 468) (codeMat 344) = codeMat 262 := by
      unfold actionA
      rw [step109wc161s1_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 344 * (codeMat 87 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 296 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 296 (by decide)
    have hact : actionA (codeMat 267) (codeMat 468) (codeMat 296) = codeMat 68 := by
      unfold actionA
      rw [step109wc161s1_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 296 * (codeMat 87 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 53 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 53 (by decide)
    have hact : actionA (codeMat 267) (codeMat 468) (codeMat 53) = codeMat 38 := by
      unfold actionA
      rw [step109wc161s1_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 53 * (codeMat 87 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 30 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 30 (by decide)
    have hact : actionA (codeMat 267) (codeMat 468) (codeMat 30) = codeMat 20 := by
      unfold actionA
      rw [step109wc161s1_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 30 * (codeMat 87 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 20 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 20 (by decide)
    have hact : actionA (codeMat 267) (codeMat 468) (codeMat 20) = codeMat 10 := by
      unfold actionA
      rw [step109wc161s1_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 20 * (codeMat 87 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 267) (codeMat 468) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc161s1_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 32 * (codeMat 87 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact

theorem step109wc161s1Dispatch :
    QuotientRankAtLeast (o161SourceU_wc ⟨1, by omega⟩) 15 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 468 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 468) o72W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 468) hP hQ o72W_wc 15
      step109_orbit72_lb15_wc
  exact quotientRankAtLeast_mono step109wc161s1_contain hAct


private theorem step109wc161s2_QtInv :
    (codeMat 486 : Mat3).transpose⁻¹ = (codeMat 157 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 486 : Mat3).transpose * (codeMat 157 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc161s2_contain :
    (o161SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 143) (codeMat 486) o72W_wc := by
  change spanCodes [288, 128, 68, 20, 10, 1] ≤ actionW (codeMat 143) (codeMat 486) o72W_wc
  apply step109wc161_spanCodes_le_of_gens [288, 128, 68, 20, 10, 1]
    (actionW (codeMat 143) (codeMat 486) o72W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 63 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 63 (by decide)
    have hact : actionA (codeMat 143) (codeMat 486) (codeMat 63) = codeMat 288 := by
      unfold actionA
      rw [step109wc161s2_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 63 * (codeMat 157 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 365 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 365 (by decide)
    have hact : actionA (codeMat 143) (codeMat 486) (codeMat 365) = codeMat 128 := by
      unfold actionA
      rw [step109wc161s2_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 365 * (codeMat 157 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 284 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 284 (by decide)
    have hact : actionA (codeMat 143) (codeMat 486) (codeMat 284) = codeMat 68 := by
      unfold actionA
      rw [step109wc161s2_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 284 * (codeMat 157 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 376 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 376 (by decide)
    have hact : actionA (codeMat 143) (codeMat 486) (codeMat 376) = codeMat 20 := by
      unfold actionA
      rw [step109wc161s2_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 376 * (codeMat 157 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 296 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 296 (by decide)
    have hact : actionA (codeMat 143) (codeMat 486) (codeMat 296) = codeMat 10 := by
      unfold actionA
      rw [step109wc161s2_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 296 * (codeMat 157 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 143) (codeMat 486) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc161s2_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 32 * (codeMat 157 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact

theorem step109wc161s2Dispatch :
    QuotientRankAtLeast (o161SourceU_wc ⟨2, by omega⟩) 15 := by
  have hP : Invertible (codeMat 143 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 486 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 143) (codeMat 486) o72W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 143) (codeMat 486) hP hQ o72W_wc 15
      step109_orbit72_lb15_wc
  exact quotientRankAtLeast_mono step109wc161s2_contain hAct


private theorem step109wc161s3_QtInv :
    (codeMat 358 : Mat3).transpose⁻¹ = (codeMat 158 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 358 : Mat3).transpose * (codeMat 158 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc161s3_contain :
    (o161SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 207) (codeMat 358) o72W_wc := by
  change spanCodes [288, 134, 68, 20, 10, 1] ≤ actionW (codeMat 207) (codeMat 358) o72W_wc
  apply step109wc161_spanCodes_le_of_gens [288, 134, 68, 20, 10, 1]
    (actionW (codeMat 207) (codeMat 358) o72W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 63 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 63 (by decide)
    have hact : actionA (codeMat 207) (codeMat 358) (codeMat 63) = codeMat 288 := by
      unfold actionA
      rw [step109wc161s3_QtInv]
      show (codeMat 207 : Mat3).transpose * codeMat 63 * (codeMat 158 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 113 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 113 (by decide)
    have hact : actionA (codeMat 207) (codeMat 358) (codeMat 113) = codeMat 134 := by
      unfold actionA
      rw [step109wc161s3_QtInv]
      show (codeMat 207 : Mat3).transpose * codeMat 113 * (codeMat 158 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 316 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 316 (by decide)
    have hact : actionA (codeMat 207) (codeMat 358) (codeMat 316) = codeMat 68 := by
      unfold actionA
      rw [step109wc161s3_QtInv]
      show (codeMat 207 : Mat3).transpose * codeMat 316 * (codeMat 158 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 112 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 112 (by decide)
    have hact : actionA (codeMat 207) (codeMat 358) (codeMat 112) = codeMat 20 := by
      unfold actionA
      rw [step109wc161s3_QtInv]
      show (codeMat 207 : Mat3).transpose * codeMat 112 * (codeMat 158 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 296 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 296 (by decide)
    have hact : actionA (codeMat 207) (codeMat 358) (codeMat 296) = codeMat 10 := by
      unfold actionA
      rw [step109wc161s3_QtInv]
      show (codeMat 207 : Mat3).transpose * codeMat 296 * (codeMat 158 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 207) (codeMat 358) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc161s3_QtInv]
      show (codeMat 207 : Mat3).transpose * codeMat 32 * (codeMat 158 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact

theorem step109wc161s3Dispatch :
    QuotientRankAtLeast (o161SourceU_wc ⟨3, by omega⟩) 15 := by
  have hP : Invertible (codeMat 207 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 358 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 207) (codeMat 358) o72W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 207) (codeMat 358) hP hQ o72W_wc 15
      step109_orbit72_lb15_wc
  exact quotientRankAtLeast_mono step109wc161s3_contain hAct


private theorem step109wc161s4_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc161s4_contain :
    (o161SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 273) (codeMat 273) o76W := by
  change spanCodes [288, 160, 68, 20, 10, 1] ≤ actionW (codeMat 273) (codeMat 273) o76W
  apply step109wc161_spanCodes_le_of_gens [288, 160, 68, 20, 10, 1]
    (actionW (codeMat 273) (codeMat 273) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 288 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 288) = codeMat 288 := by
      unfold actionA
      rw [step109wc161s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 288 * (codeMat 273 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 160) = codeMat 160 := by
      unfold actionA
      rw [step109wc161s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 160 * (codeMat 273 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step109wc161s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 68 * (codeMat 273 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 20 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 20) = codeMat 20 := by
      unfold actionA
      rw [step109wc161s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * (codeMat 273 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step109wc161s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 10 * (codeMat 273 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc161s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact

theorem step109wc161s4Dispatch :
    QuotientRankAtLeast (o161SourceU_wc ⟨4, by omega⟩) 15 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 273) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 273) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc161s4_contain hAct


private theorem step109wc161s5_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = (codeMat 275 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * (codeMat 275 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc161s5_contain :
    (o161SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 345) (codeMat 275) o76W := by
  change spanCodes [288, 162, 68, 20, 10, 1] ≤ actionW (codeMat 345) (codeMat 275) o76W
  apply step109wc161_spanCodes_le_of_gens [288, 162, 68, 20, 10, 1]
    (actionW (codeMat 345) (codeMat 275) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 288 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 345) (codeMat 275) (codeMat 288) = codeMat 288 := by
      unfold actionA
      rw [step109wc161s5_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 288 * (codeMat 275 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 228 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 228 (by decide)
    have hact : actionA (codeMat 345) (codeMat 275) (codeMat 228) = codeMat 162 := by
      unfold actionA
      rw [step109wc161s5_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 228 * (codeMat 275 : Mat3).transpose = codeMat 162
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 69 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 345) (codeMat 275) (codeMat 69) = codeMat 68 := by
      unfold actionA
      rw [step109wc161s5_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 69 * (codeMat 275 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 31 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 31 (by decide)
    have hact : actionA (codeMat 345) (codeMat 275) (codeMat 31) = codeMat 20 := by
      unfold actionA
      rw [step109wc161s5_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 31 * (codeMat 275 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 345) (codeMat 275) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step109wc161s5_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 10 * (codeMat 275 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 345) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc161s5_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 1 * (codeMat 275 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact

theorem step109wc161s5Dispatch :
    QuotientRankAtLeast (o161SourceU_wc ⟨5, by omega⟩) 15 := by
  have hP : Invertible (codeMat 345 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 345) (codeMat 275) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 345) (codeMat 275) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc161s5_contain hAct


private theorem step109wc161s6_QtInv :
    (codeMat 307 : Mat3).transpose⁻¹ = (codeMat 311 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 307 : Mat3).transpose * (codeMat 311 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc161s6_contain :
    (o161SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 401) (codeMat 307) o76W := by
  change spanCodes [288, 164, 68, 20, 10, 1] ≤ actionW (codeMat 401) (codeMat 307) o76W
  apply step109wc161_spanCodes_le_of_gens [288, 164, 68, 20, 10, 1]
    (actionW (codeMat 401) (codeMat 307) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 384 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 384 (by decide)
    have hact : actionA (codeMat 401) (codeMat 307) (codeMat 384) = codeMat 288 := by
      unfold actionA
      rw [step109wc161s6_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 384 * (codeMat 311 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 238 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 238 (by decide)
    have hact : actionA (codeMat 401) (codeMat 307) (codeMat 238) = codeMat 164 := by
      unfold actionA
      rw [step109wc161s6_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 238 * (codeMat 311 : Mat3).transpose = codeMat 164
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 78 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 401) (codeMat 307) (codeMat 78) = codeMat 68 := by
      unfold actionA
      rw [step109wc161s6_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 78 * (codeMat 311 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 30 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 30 (by decide)
    have hact : actionA (codeMat 401) (codeMat 307) (codeMat 30) = codeMat 20 := by
      unfold actionA
      rw [step109wc161s6_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 30 * (codeMat 311 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 11 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 401) (codeMat 307) (codeMat 11) = codeMat 10 := by
      unfold actionA
      rw [step109wc161s6_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 11 * (codeMat 311 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 401) (codeMat 307) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc161s6_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 1 * (codeMat 311 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact

theorem step109wc161s6Dispatch :
    QuotientRankAtLeast (o161SourceU_wc ⟨6, by omega⟩) 15 := by
  have hP : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 307 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 401) (codeMat 307) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 401) (codeMat 307) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc161s6_contain hAct


private theorem step109wc161s7_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = (codeMat 305 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * (codeMat 305 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc161s7_contain :
    (o161SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 409) (codeMat 305) o76W := by
  change spanCodes [288, 166, 68, 20, 10, 1] ≤ actionW (codeMat 409) (codeMat 305) o76W
  apply step109wc161_spanCodes_le_of_gens [288, 166, 68, 20, 10, 1]
    (actionW (codeMat 409) (codeMat 305) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 384 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 384 (by decide)
    have hact : actionA (codeMat 409) (codeMat 305) (codeMat 384) = codeMat 288 := by
      unfold actionA
      rw [step109wc161s7_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 384 * (codeMat 305 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 409) (codeMat 305) (codeMat 160) = codeMat 166 := by
      unfold actionA
      rw [step109wc161s7_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 160 * (codeMat 305 : Mat3).transpose = codeMat 166
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 79 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 79 (by decide)
    have hact : actionA (codeMat 409) (codeMat 305) (codeMat 79) = codeMat 68 := by
      unfold actionA
      rw [step109wc161s7_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 79 * (codeMat 305 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 20 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 20 (by decide)
    have hact : actionA (codeMat 409) (codeMat 305) (codeMat 20) = codeMat 20 := by
      unfold actionA
      rw [step109wc161s7_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 20 * (codeMat 305 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 11 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 409) (codeMat 305) (codeMat 11) = codeMat 10 := by
      unfold actionA
      rw [step109wc161s7_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 11 * (codeMat 305 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 409) (codeMat 305) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc161s7_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 1 * (codeMat 305 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact

theorem step109wc161s7Dispatch :
    QuotientRankAtLeast (o161SourceU_wc ⟨7, by omega⟩) 15 := by
  have hP : Invertible (codeMat 409 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 409) (codeMat 305) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 409) (codeMat 305) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc161s7_contain hAct


private theorem step109wc161s8_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc161s8_contain :
    (o161SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 401) (codeMat 273) o34W := by
  change spanCodes [288, 68, 20, 8, 2, 1] ≤ actionW (codeMat 401) (codeMat 273) o34W
  apply step109wc161_spanCodes_le_of_gens [288, 68, 20, 8, 2, 1]
    (actionW (codeMat 401) (codeMat 273) o34W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 256 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 401) (codeMat 273) (codeMat 256) = codeMat 288 := by
      unfold actionA
      rw [step109wc161s8_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 256 * (codeMat 273 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 76 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 76 (by decide)
    have hact : actionA (codeMat 401) (codeMat 273) (codeMat 76) = codeMat 68 := by
      unfold actionA
      rw [step109wc161s8_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 76 * (codeMat 273 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 20 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 20 (by decide)
    have hact : actionA (codeMat 401) (codeMat 273) (codeMat 20) = codeMat 20 := by
      unfold actionA
      rw [step109wc161s8_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 20 * (codeMat 273 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 401) (codeMat 273) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc161s8_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 401) (codeMat 273) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc161s8_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 401) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc161s8_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact

theorem step109wc161s8Dispatch :
    QuotientRankAtLeast (o161SourceU_wc ⟨8, by omega⟩) 14 := by
  have hP : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 401) (codeMat 273) o34W) 14 :=
    @quotientRankAtLeast_action (codeMat 401) (codeMat 273) hP hQ o34W 14
      step99_orbit34_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc161s8_contain hAct

private def step109wc161s9SrcT : Submodule F2 Mat3 := spanCodes [272, 128, 66, 34, 8, 1]

private theorem step109wc161s9SrcT_lb : QuotientRankAtLeast step109wc161s9SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step99_orbit55_lb14_unconditional
  have hle : step109wc161s9SrcT ≤ transposeW o55W := by
    unfold step109wc161s9SrcT transposeW
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

private theorem step109wc161s9_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc161s9_contain :
    (o161SourceU_wc ⟨9, by omega⟩) ≤ actionW (codeMat 84) (codeMat 140) step109wc161s9SrcT := by
  change spanCodes [256, 68, 32, 20, 10, 1] ≤ actionW (codeMat 84) (codeMat 140) step109wc161s9SrcT
  apply step109wc161_spanCodes_le_of_gens [256, 68, 32, 20, 10, 1]
    (actionW (codeMat 84) (codeMat 140) step109wc161s9SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 1 ∈ step109wc161s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc161s9_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 66 ∈ step109wc161s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 66 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 66) = codeMat 68 := by
      unfold actionA
      rw [step109wc161s9_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 66 * (codeMat 98 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ step109wc161s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc161s9_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 96 ∈ step109wc161s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 96 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 96) = codeMat 20 := by
      unfold actionA
      rw [step109wc161s9_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 96 * (codeMat 98 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 272 ∈ step109wc161s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 272 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 272) = codeMat 10 := by
      unfold actionA
      rw [step109wc161s9_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 272 * (codeMat 98 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ step109wc161s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc161s9_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact

theorem step109wc161s9Dispatch :
    QuotientRankAtLeast (o161SourceU_wc ⟨9, by omega⟩) 14 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 140) step109wc161s9SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 140) hP hQ step109wc161s9SrcT 14
      step109wc161s9SrcT_lb
  exact quotientRankAtLeast_mono step109wc161s9_contain hAct

private def step109wc161s10SrcT : Submodule F2 Mat3 := spanCodes [272, 128, 66, 34, 8, 1]

private theorem step109wc161s10SrcT_lb : QuotientRankAtLeast step109wc161s10SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step99_orbit55_lb14_unconditional
  have hle : step109wc161s10SrcT ≤ transposeW o55W := by
    unfold step109wc161s10SrcT transposeW
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

private theorem step109wc161s10_QtInv :
    (codeMat 156 : Mat3).transpose⁻¹ = (codeMat 102 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 156 : Mat3).transpose * (codeMat 102 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc161s10_contain :
    (o161SourceU_wc ⟨10, by omega⟩) ≤ actionW (codeMat 93) (codeMat 156) step109wc161s10SrcT := by
  change spanCodes [260, 68, 36, 20, 10, 1] ≤ actionW (codeMat 93) (codeMat 156) step109wc161s10SrcT
  apply step109wc161_spanCodes_le_of_gens [260, 68, 36, 20, 10, 1]
    (actionW (codeMat 93) (codeMat 156) step109wc161s10SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 1 ∈ step109wc161s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 1 (by decide)
    have hact : actionA (codeMat 93) (codeMat 156) (codeMat 1) = codeMat 260 := by
      unfold actionA
      rw [step109wc161s10_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 1 * (codeMat 102 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 194 ∈ step109wc161s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 194 (by decide)
    have hact : actionA (codeMat 93) (codeMat 156) (codeMat 194) = codeMat 68 := by
      unfold actionA
      rw [step109wc161s10_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 194 * (codeMat 102 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ step109wc161s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 8 (by decide)
    have hact : actionA (codeMat 93) (codeMat 156) (codeMat 8) = codeMat 36 := by
      unfold actionA
      rw [step109wc161s10_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 8 * (codeMat 102 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 496 ∈ step109wc161s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 496 (by decide)
    have hact : actionA (codeMat 93) (codeMat 156) (codeMat 496) = codeMat 20 := by
      unfold actionA
      rw [step109wc161s10_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 496 * (codeMat 102 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 272 ∈ step109wc161s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 272 (by decide)
    have hact : actionA (codeMat 93) (codeMat 156) (codeMat 272) = codeMat 10 := by
      unfold actionA
      rw [step109wc161s10_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 272 * (codeMat 102 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ step109wc161s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 128 (by decide)
    have hact : actionA (codeMat 93) (codeMat 156) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc161s10_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 128 * (codeMat 102 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact

theorem step109wc161s10Dispatch :
    QuotientRankAtLeast (o161SourceU_wc ⟨10, by omega⟩) 14 := by
  have hP : Invertible (codeMat 93 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 156 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 93) (codeMat 156) step109wc161s10SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 93) (codeMat 156) hP hQ step109wc161s10SrcT 14
      step109wc161s10SrcT_lb
  exact quotientRankAtLeast_mono step109wc161s10_contain hAct


private theorem step109wc161s11_QtInv :
    (codeMat 244 : Mat3).transpose⁻¹ = (codeMat 95 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 244 : Mat3).transpose * (codeMat 95 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc161s11_contain :
    (o161SourceU_wc ⟨11, by omega⟩) ≤ actionW (codeMat 142) (codeMat 244) o55W := by
  change spanCodes [288, 130, 68, 20, 10, 1] ≤ actionW (codeMat 142) (codeMat 244) o55W
  apply step109wc161_spanCodes_le_of_gens [288, 130, 68, 20, 10, 1]
    (actionW (codeMat 142) (codeMat 244) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 3 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 142) (codeMat 244) (codeMat 3) = codeMat 288 := by
      unfold actionA
      rw [step109wc161s11_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 3 * (codeMat 95 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 438 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 438 (by decide)
    have hact : actionA (codeMat 142) (codeMat 244) (codeMat 438) = codeMat 130 := by
      unfold actionA
      rw [step109wc161s11_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 438 * (codeMat 95 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 284 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 284 (by decide)
    have hact : actionA (codeMat 142) (codeMat 244) (codeMat 284) = codeMat 68 := by
      unfold actionA
      rw [step109wc161s11_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 284 * (codeMat 95 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 408 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 408 (by decide)
    have hact : actionA (codeMat 142) (codeMat 244) (codeMat 408) = codeMat 20 := by
      unfold actionA
      rw [step109wc161s11_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 408 * (codeMat 95 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 304 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 304 (by decide)
    have hact : actionA (codeMat 142) (codeMat 244) (codeMat 304) = codeMat 10 := by
      unfold actionA
      rw [step109wc161s11_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 304 * (codeMat 95 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 142) (codeMat 244) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc161s11_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 32 * (codeMat 95 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact

theorem step109wc161s11Dispatch :
    QuotientRankAtLeast (o161SourceU_wc ⟨11, by omega⟩) 14 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 244 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 244) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 244) hP hQ o55W 14
      step99_orbit55_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc161s11_contain hAct


private theorem step109wc161s12_QtInv :
    (codeMat 116 : Mat3).transpose⁻¹ = (codeMat 92 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 116 : Mat3).transpose * (codeMat 92 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc161s12_contain :
    (o161SourceU_wc ⟨12, by omega⟩) ≤ actionW (codeMat 206) (codeMat 116) o55W := by
  change spanCodes [288, 132, 68, 20, 10, 1] ≤ actionW (codeMat 206) (codeMat 116) o55W
  apply step109wc161_spanCodes_le_of_gens [288, 132, 68, 20, 10, 1]
    (actionW (codeMat 206) (codeMat 116) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 3 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 206) (codeMat 116) (codeMat 3) = codeMat 288 := by
      unfold actionA
      rw [step109wc161s12_QtInv]
      show (codeMat 206 : Mat3).transpose * codeMat 3 * (codeMat 92 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 138 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 138 (by decide)
    have hact : actionA (codeMat 206) (codeMat 116) (codeMat 138) = codeMat 132 := by
      unfold actionA
      rw [step109wc161s12_QtInv]
      show (codeMat 206 : Mat3).transpose * codeMat 138 * (codeMat 92 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 316 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 316 (by decide)
    have hact : actionA (codeMat 206) (codeMat 116) (codeMat 316) = codeMat 68 := by
      unfold actionA
      rw [step109wc161s12_QtInv]
      show (codeMat 206 : Mat3).transpose * codeMat 316 * (codeMat 92 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 136 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 136 (by decide)
    have hact : actionA (codeMat 206) (codeMat 116) (codeMat 136) = codeMat 20 := by
      unfold actionA
      rw [step109wc161s12_QtInv]
      show (codeMat 206 : Mat3).transpose * codeMat 136 * (codeMat 92 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 304 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 304 (by decide)
    have hact : actionA (codeMat 206) (codeMat 116) (codeMat 304) = codeMat 10 := by
      unfold actionA
      rw [step109wc161s12_QtInv]
      show (codeMat 206 : Mat3).transpose * codeMat 304 * (codeMat 92 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 206) (codeMat 116) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc161s12_QtInv]
      show (codeMat 206 : Mat3).transpose * codeMat 32 * (codeMat 92 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact

theorem step109wc161s12Dispatch :
    QuotientRankAtLeast (o161SourceU_wc ⟨12, by omega⟩) 14 := by
  have hP : Invertible (codeMat 206 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 116 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 206) (codeMat 116) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 206) (codeMat 116) hP hQ o55W 14
      step99_orbit55_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc161s12_contain hAct


private theorem step109wc161s13_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc161s13_contain :
    (o161SourceU_wc ⟨13, by omega⟩) ≤ actionW (codeMat 305) (codeMat 140) o38W_mono := by
  change spanCodes [288, 64, 16, 10, 4, 1] ≤ actionW (codeMat 305) (codeMat 140) o38W_mono
  apply step109wc161_spanCodes_le_of_gens [288, 64, 16, 10, 4, 1]
    (actionW (codeMat 305) (codeMat 140) o38W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 8 ∈ o38W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 128, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 305) (codeMat 140) (codeMat 8) = codeMat 288 := by
      unfold actionA
      rw [step109wc161s13_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 128 ∈ o38W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 128, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 305) (codeMat 140) (codeMat 128) = codeMat 64 := by
      unfold actionA
      rw [step109wc161s13_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 128 * (codeMat 98 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 288 ∈ o38W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 128, 20, 8, 2, 1] 288 (by decide)
    have hact : actionA (codeMat 305) (codeMat 140) (codeMat 288) = codeMat 16 := by
      unfold actionA
      rw [step109wc161s13_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 288 * (codeMat 98 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 148 ∈ o38W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 128, 20, 8, 2, 1] 148 (by decide)
    have hact : actionA (codeMat 305) (codeMat 140) (codeMat 148) = codeMat 10 := by
      unfold actionA
      rw [step109wc161s13_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 148 * (codeMat 98 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o38W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 128, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 305) (codeMat 140) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step109wc161s13_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o38W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 128, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 305) (codeMat 140) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc161s13_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact

theorem step109wc161s13Dispatch :
    QuotientRankAtLeast (o161SourceU_wc ⟨13, by omega⟩) 12 := by
  have hP : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 305) (codeMat 140) o38W_mono) 12 :=
    @quotientRankAtLeast_action (codeMat 305) (codeMat 140) hP hQ o38W_mono 12
      orbit38_lb12_mono
  exact quotientRankAtLeast_mono step109wc161s13_contain hAct

private def step109wc161s14SrcT : Submodule F2 Mat3 := spanCodes [384, 80, 32, 8, 2, 1]

private theorem step109wc161s14SrcT_lb : QuotientRankAtLeast step109wc161s14SrcT 12 := by
  have ht := quotientRankAtLeast_transpose orbit38_lb12_mono
  have hle : step109wc161s14SrcT ≤ transposeW o38W_mono := by
    unfold step109wc161s14SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4 | h5
    · subst h0
      show codeMat 384 ∈ Submodule.map transposeLinearMap o38W_mono
      exact ⟨codeMat 288, spanContainsCodeCore_implies_mem_spanCodes [288, 128, 20, 8, 2, 1] 288 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 80 ∈ Submodule.map transposeLinearMap o38W_mono
      exact ⟨codeMat 20, spanContainsCodeCore_implies_mem_spanCodes [288, 128, 20, 8, 2, 1] 20 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 32 ∈ Submodule.map transposeLinearMap o38W_mono
      exact ⟨codeMat 128, spanContainsCodeCore_implies_mem_spanCodes [288, 128, 20, 8, 2, 1] 128 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 8 ∈ Submodule.map transposeLinearMap o38W_mono
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [288, 128, 20, 8, 2, 1] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 2 ∈ Submodule.map transposeLinearMap o38W_mono
      exact ⟨codeMat 8, spanContainsCodeCore_implies_mem_spanCodes [288, 128, 20, 8, 2, 1] 8 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h5
      show codeMat 1 ∈ Submodule.map transposeLinearMap o38W_mono
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [288, 128, 20, 8, 2, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc161s14_QtInv :
    (codeMat 179 : Mat3).transpose⁻¹ = (codeMat 421 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 179 : Mat3).transpose * (codeMat 421 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc161s14_contain :
    (o161SourceU_wc ⟨14, by omega⟩) ≤ actionW (codeMat 142) (codeMat 179) step109wc161s14SrcT := by
  change spanCodes [288, 66, 18, 10, 6, 1] ≤ actionW (codeMat 142) (codeMat 179) step109wc161s14SrcT
  apply step109wc161_spanCodes_le_of_gens [288, 66, 18, 10, 6, 1]
    (actionW (codeMat 142) (codeMat 179) step109wc161s14SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 2 ∈ step109wc161s14SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [384, 80, 32, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 142) (codeMat 179) (codeMat 2) = codeMat 288 := by
      unfold actionA
      rw [step109wc161s14_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 2 * (codeMat 421 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 121 ∈ step109wc161s14SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [384, 80, 32, 8, 2, 1] 121 (by decide)
    have hact : actionA (codeMat 142) (codeMat 179) (codeMat 121) = codeMat 66 := by
      unfold actionA
      rw [step109wc161s14_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 121 * (codeMat 421 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 504 ∈ step109wc161s14SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [384, 80, 32, 8, 2, 1] 504 (by decide)
    have hact : actionA (codeMat 142) (codeMat 179) (codeMat 504) = codeMat 18 := by
      unfold actionA
      rw [step109wc161s14_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 504 * (codeMat 421 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 120 ∈ step109wc161s14SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [384, 80, 32, 8, 2, 1] 120 (by decide)
    have hact : actionA (codeMat 142) (codeMat 179) (codeMat 120) = codeMat 10 := by
      unfold actionA
      rw [step109wc161s14_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 120 * (codeMat 421 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 40 ∈ step109wc161s14SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [384, 80, 32, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 142) (codeMat 179) (codeMat 40) = codeMat 6 := by
      unfold actionA
      rw [step109wc161s14_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 40 * (codeMat 421 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ step109wc161s14SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [384, 80, 32, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 142) (codeMat 179) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc161s14_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 8 * (codeMat 421 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc161_codeMat_mem_actionW_of_witness hw hact

theorem step109wc161s14Dispatch :
    QuotientRankAtLeast (o161SourceU_wc ⟨14, by omega⟩) 12 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 179 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 179) step109wc161s14SrcT) 12 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 179) hP hQ step109wc161s14SrcT 12
      step109wc161s14SrcT_lb
  exact quotientRankAtLeast_mono step109wc161s14_contain hAct

theorem step109wc161_all_dispatch (i : Fin 15) :
    QuotientRankAtLeast (o161SourceU_wc i) (o161SourceLb_wc i) := by
  fin_cases i
  · exact step109wc161s0Dispatch
  · exact step109wc161s1Dispatch
  · exact step109wc161s2Dispatch
  · exact step109wc161s3Dispatch
  · exact step109wc161s4Dispatch
  · exact step109wc161s5Dispatch
  · exact step109wc161s6Dispatch
  · exact step109wc161s7Dispatch
  · exact step109wc161s8Dispatch
  · exact step109wc161s9Dispatch
  · exact step109wc161s10Dispatch
  · exact step109wc161s11Dispatch
  · exact step109wc161s12Dispatch
  · exact step109wc161s13Dispatch
  · exact step109wc161s14Dispatch

theorem step109_orbit161_lb16_wc : QuotientRankAtLeast o161W_wc 16 :=
  o161Lb16_wc step109wc161_all_dispatch

end QiushiMatmul
