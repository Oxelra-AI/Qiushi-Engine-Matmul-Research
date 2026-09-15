import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit166Consumer
import QiushiWcOrbit72Dispatch
import QiushiStep99Orbit76Dispatch
import QiushiStep99Orbit77Dispatch
import QiushiWcOrbit81Dispatch
import QiushiWcOrbit51Dispatch
import QiushiStep99Orbit55Dispatch
import QiushiStep99Orbit82Dispatch
import QiushiWcOrbit36Dispatch
import QiushiMonoOrbit53From14

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc166_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc166_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc166s0_QtInv :
    (codeMat 212 : Mat3).transpose⁻¹ = (codeMat 86 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 212 : Mat3).transpose * (codeMat 86 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc166s0_contain :
    (o166SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 331) (codeMat 212) o72W_wc := by
  change spanCodes [262, 68, 36, 20, 10, 1] ≤ actionW (codeMat 331) (codeMat 212) o72W_wc
  apply step109wc166_spanCodes_le_of_gens [262, 68, 36, 20, 10, 1]
    (actionW (codeMat 331) (codeMat 212) o72W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 112 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 112 (by decide)
    have hact : actionA (codeMat 331) (codeMat 212) (codeMat 112) = codeMat 262 := by
      unfold actionA
      rw [step109wc166s0_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 112 * (codeMat 86 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 296 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 296 (by decide)
    have hact : actionA (codeMat 331) (codeMat 212) (codeMat 296) = codeMat 68 := by
      unfold actionA
      rw [step109wc166s0_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 296 * (codeMat 86 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 331) (codeMat 212) (codeMat 1) = codeMat 36 := by
      unfold actionA
      rw [step109wc166s0_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 1 * (codeMat 86 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 62 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 62 (by decide)
    have hact : actionA (codeMat 331) (codeMat 212) (codeMat 62) = codeMat 20 := by
      unfold actionA
      rw [step109wc166s0_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 62 * (codeMat 86 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 20 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 20 (by decide)
    have hact : actionA (codeMat 331) (codeMat 212) (codeMat 20) = codeMat 10 := by
      unfold actionA
      rw [step109wc166s0_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 20 * (codeMat 86 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 331) (codeMat 212) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc166s0_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 32 * (codeMat 86 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact

theorem step109wc166s0Dispatch :
    QuotientRankAtLeast (o166SourceU_wc ⟨0, by omega⟩) 15 := by
  have hP : Invertible (codeMat 331 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 212 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 331) (codeMat 212) o72W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 331) (codeMat 212) hP hQ o72W_wc 15
      step109_orbit72_lb15_wc
  exact quotientRankAtLeast_mono step109wc166s0_contain hAct


private theorem step109wc166s1_QtInv :
    (codeMat 468 : Mat3).transpose⁻¹ = (codeMat 87 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 468 : Mat3).transpose * (codeMat 87 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc166s1_contain :
    (o166SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 459) (codeMat 468) o72W_wc := by
  change spanCodes [260, 70, 38, 20, 10, 1] ≤ actionW (codeMat 459) (codeMat 468) o72W_wc
  apply step109wc166_spanCodes_le_of_gens [260, 70, 38, 20, 10, 1]
    (actionW (codeMat 459) (codeMat 468) o72W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 365 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 365 (by decide)
    have hact : actionA (codeMat 459) (codeMat 468) (codeMat 365) = codeMat 260 := by
      unfold actionA
      rw [step109wc166s1_QtInv]
      show (codeMat 459 : Mat3).transpose * codeMat 365 * (codeMat 87 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 284 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 284 (by decide)
    have hact : actionA (codeMat 459) (codeMat 468) (codeMat 284) = codeMat 70 := by
      unfold actionA
      rw [step109wc166s1_QtInv]
      show (codeMat 459 : Mat3).transpose * codeMat 284 * (codeMat 87 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 53 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 53 (by decide)
    have hact : actionA (codeMat 459) (codeMat 468) (codeMat 53) = codeMat 38 := by
      unfold actionA
      rw [step109wc166s1_QtInv]
      show (codeMat 459 : Mat3).transpose * codeMat 53 * (codeMat 87 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 30 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 30 (by decide)
    have hact : actionA (codeMat 459) (codeMat 468) (codeMat 30) = codeMat 20 := by
      unfold actionA
      rw [step109wc166s1_QtInv]
      show (codeMat 459 : Mat3).transpose * codeMat 30 * (codeMat 87 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 20 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 20 (by decide)
    have hact : actionA (codeMat 459) (codeMat 468) (codeMat 20) = codeMat 10 := by
      unfold actionA
      rw [step109wc166s1_QtInv]
      show (codeMat 459 : Mat3).transpose * codeMat 20 * (codeMat 87 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 459) (codeMat 468) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc166s1_QtInv]
      show (codeMat 459 : Mat3).transpose * codeMat 32 * (codeMat 87 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact

theorem step109wc166s1Dispatch :
    QuotientRankAtLeast (o166SourceU_wc ⟨1, by omega⟩) 15 := by
  have hP : Invertible (codeMat 459 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 468 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 459) (codeMat 468) o72W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 459) (codeMat 468) hP hQ o72W_wc 15
      step109_orbit72_lb15_wc
  exact quotientRankAtLeast_mono step109wc166s1_contain hAct


private theorem step109wc166s2_QtInv :
    (codeMat 500 : Mat3).transpose⁻¹ = (codeMat 94 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 500 : Mat3).transpose * (codeMat 94 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc166s2_contain :
    (o166SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 303) (codeMat 500) o76W := by
  change spanCodes [290, 128, 96, 20, 10, 1] ≤ actionW (codeMat 303) (codeMat 500) o76W
  apply step109wc166_spanCodes_le_of_gens [290, 128, 96, 20, 10, 1]
    (actionW (codeMat 303) (codeMat 500) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 79 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 79 (by decide)
    have hact : actionA (codeMat 303) (codeMat 500) (codeMat 79) = codeMat 290 := by
      unfold actionA
      rw [step109wc166s2_QtInv]
      show (codeMat 303 : Mat3).transpose * codeMat 79 * (codeMat 94 : Mat3).transpose = codeMat 290
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 384 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 384 (by decide)
    have hact : actionA (codeMat 303) (codeMat 500) (codeMat 384) = codeMat 128 := by
      unfold actionA
      rw [step109wc166s2_QtInv]
      show (codeMat 303 : Mat3).transpose * codeMat 384 * (codeMat 94 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 319 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 319 (by decide)
    have hact : actionA (codeMat 303) (codeMat 500) (codeMat 319) = codeMat 96 := by
      unfold actionA
      rw [step109wc166s2_QtInv]
      show (codeMat 303 : Mat3).transpose * codeMat 319 * (codeMat 94 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 462 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 462 (by decide)
    have hact : actionA (codeMat 303) (codeMat 500) (codeMat 462) = codeMat 20 := by
      unfold actionA
      rw [step109wc166s2_QtInv]
      show (codeMat 303 : Mat3).transpose * codeMat 462 * (codeMat 94 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 404 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 404 (by decide)
    have hact : actionA (codeMat 303) (codeMat 500) (codeMat 404) = codeMat 10 := by
      unfold actionA
      rw [step109wc166s2_QtInv]
      show (codeMat 303 : Mat3).transpose * codeMat 404 * (codeMat 94 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 288 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 303) (codeMat 500) (codeMat 288) = codeMat 1 := by
      unfold actionA
      rw [step109wc166s2_QtInv]
      show (codeMat 303 : Mat3).transpose * codeMat 288 * (codeMat 94 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact

theorem step109wc166s2Dispatch :
    QuotientRankAtLeast (o166SourceU_wc ⟨2, by omega⟩) 15 := by
  have hP : Invertible (codeMat 303 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 500 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 303) (codeMat 500) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 303) (codeMat 500) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc166s2_contain hAct


private theorem step109wc166s3_QtInv :
    (codeMat 428 : Mat3).transpose⁻¹ = (codeMat 107 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 428 : Mat3).transpose * (codeMat 107 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc166s3_contain :
    (o166SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 92) (codeMat 428) o77W := by
  change spanCodes [290, 130, 96, 20, 10, 1] ≤ actionW (codeMat 92) (codeMat 428) o77W
  apply step109wc166_spanCodes_le_of_gens [290, 130, 96, 20, 10, 1]
    (actionW (codeMat 92) (codeMat 428) o77W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 255 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 255 (by decide)
    have hact : actionA (codeMat 92) (codeMat 428) (codeMat 255) = codeMat 290 := by
      unfold actionA
      rw [step109wc166s3_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 255 * (codeMat 107 : Mat3).transpose = codeMat 290
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 260 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 92) (codeMat 428) (codeMat 260) = codeMat 130 := by
      unfold actionA
      rw [step109wc166s3_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 260 * (codeMat 107 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 506 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 506 (by decide)
    have hact : actionA (codeMat 92) (codeMat 428) (codeMat 506) = codeMat 96 := by
      unfold actionA
      rw [step109wc166s3_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 506 * (codeMat 107 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 224 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 224 (by decide)
    have hact : actionA (codeMat 92) (codeMat 428) (codeMat 224) = codeMat 20 := by
      unfold actionA
      rw [step109wc166s3_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 224 * (codeMat 107 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 400 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 400 (by decide)
    have hact : actionA (codeMat 92) (codeMat 428) (codeMat 400) = codeMat 10 := by
      unfold actionA
      rw [step109wc166s3_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 400 * (codeMat 107 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 92) (codeMat 428) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc166s3_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 128 * (codeMat 107 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact

theorem step109wc166s3Dispatch :
    QuotientRankAtLeast (o166SourceU_wc ⟨3, by omega⟩) 15 := by
  have hP : Invertible (codeMat 92 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 428 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 92) (codeMat 428) o77W) 15 :=
    @quotientRankAtLeast_action (codeMat 92) (codeMat 428) hP hQ o77W 15
      step99_orbit77_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc166s3_contain hAct


private theorem step109wc166s4_QtInv :
    (codeMat 244 : Mat3).transpose⁻¹ = (codeMat 95 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 244 : Mat3).transpose * (codeMat 95 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc166s4_contain :
    (o166SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 445) (codeMat 244) o76W := by
  change spanCodes [290, 132, 96, 20, 10, 1] ≤ actionW (codeMat 445) (codeMat 244) o76W
  apply step109wc166_spanCodes_le_of_gens [290, 132, 96, 20, 10, 1]
    (actionW (codeMat 445) (codeMat 244) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 368 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 368 (by decide)
    have hact : actionA (codeMat 445) (codeMat 244) (codeMat 368) = codeMat 290 := by
      unfold actionA
      rw [step109wc166s4_QtInv]
      show (codeMat 445 : Mat3).transpose * codeMat 368 * (codeMat 95 : Mat3).transpose = codeMat 290
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 366 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 366 (by decide)
    have hact : actionA (codeMat 445) (codeMat 244) (codeMat 366) = codeMat 132 := by
      unfold actionA
      rw [step109wc166s4_QtInv]
      show (codeMat 445 : Mat3).transpose * codeMat 366 * (codeMat 95 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 319 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 319 (by decide)
    have hact : actionA (codeMat 445) (codeMat 244) (codeMat 319) = codeMat 96 := by
      unfold actionA
      rw [step109wc166s4_QtInv]
      show (codeMat 445 : Mat3).transpose * codeMat 319 * (codeMat 95 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 238 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 238 (by decide)
    have hact : actionA (codeMat 445) (codeMat 244) (codeMat 238) = codeMat 20 := by
      unfold actionA
      rw [step109wc166s4_QtInv]
      show (codeMat 445 : Mat3).transpose * codeMat 238 * (codeMat 95 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 404 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 404 (by decide)
    have hact : actionA (codeMat 445) (codeMat 244) (codeMat 404) = codeMat 10 := by
      unfold actionA
      rw [step109wc166s4_QtInv]
      show (codeMat 445 : Mat3).transpose * codeMat 404 * (codeMat 95 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 288 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 445) (codeMat 244) (codeMat 288) = codeMat 1 := by
      unfold actionA
      rw [step109wc166s4_QtInv]
      show (codeMat 445 : Mat3).transpose * codeMat 288 * (codeMat 95 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact

theorem step109wc166s4Dispatch :
    QuotientRankAtLeast (o166SourceU_wc ⟨4, by omega⟩) 15 := by
  have hP : Invertible (codeMat 445 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 244 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 445) (codeMat 244) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 445) (codeMat 244) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc166s4_contain hAct


private theorem step109wc166s5_QtInv :
    (codeMat 396 : Mat3).transpose⁻¹ = (codeMat 106 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 396 : Mat3).transpose * (codeMat 106 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc166s5_contain :
    (o166SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 94) (codeMat 396) o77W := by
  change spanCodes [290, 134, 96, 20, 10, 1] ≤ actionW (codeMat 94) (codeMat 396) o77W
  apply step109wc166_spanCodes_le_of_gens [290, 134, 96, 20, 10, 1]
    (actionW (codeMat 94) (codeMat 396) o77W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 261 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 261 (by decide)
    have hact : actionA (codeMat 94) (codeMat 396) (codeMat 261) = codeMat 290 := by
      unfold actionA
      rw [step109wc166s5_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 261 * (codeMat 106 : Mat3).transpose = codeMat 290
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 356 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 356 (by decide)
    have hact : actionA (codeMat 94) (codeMat 396) (codeMat 356) = codeMat 134 := by
      unfold actionA
      rw [step109wc166s5_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 356 * (codeMat 106 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 506 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 506 (by decide)
    have hact : actionA (codeMat 94) (codeMat 396) (codeMat 506) = codeMat 96 := by
      unfold actionA
      rw [step109wc166s5_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 506 * (codeMat 106 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 96 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 96 (by decide)
    have hact : actionA (codeMat 94) (codeMat 396) (codeMat 96) = codeMat 20 := by
      unfold actionA
      rw [step109wc166s5_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 96 * (codeMat 106 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 400 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 400 (by decide)
    have hact : actionA (codeMat 94) (codeMat 396) (codeMat 400) = codeMat 10 := by
      unfold actionA
      rw [step109wc166s5_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 400 * (codeMat 106 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 94) (codeMat 396) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc166s5_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 128 * (codeMat 106 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact

theorem step109wc166s5Dispatch :
    QuotientRankAtLeast (o166SourceU_wc ⟨5, by omega⟩) 15 := by
  have hP : Invertible (codeMat 94 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 396 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 94) (codeMat 396) o77W) 15 :=
    @quotientRankAtLeast_action (codeMat 94) (codeMat 396) hP hQ o77W 15
      step99_orbit77_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc166s5_contain hAct


private theorem step109wc166s6_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc166s6_contain :
    (o166SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 273) (codeMat 273) o81W_wc := by
  change spanCodes [290, 160, 96, 20, 10, 1] ≤ actionW (codeMat 273) (codeMat 273) o81W_wc
  apply step109wc166_spanCodes_le_of_gens [290, 160, 96, 20, 10, 1]
    (actionW (codeMat 273) (codeMat 273) o81W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 290 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 290 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 290) = codeMat 290 := by
      unfold actionA
      rw [step109wc166s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 290 * (codeMat 273 : Mat3).transpose = codeMat 290
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 160) = codeMat 160 := by
      unfold actionA
      rw [step109wc166s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 160 * (codeMat 273 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 96 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 96 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 96) = codeMat 96 := by
      unfold actionA
      rw [step109wc166s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 96 * (codeMat 273 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 20 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 20) = codeMat 20 := by
      unfold actionA
      rw [step109wc166s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * (codeMat 273 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step109wc166s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 10 * (codeMat 273 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc166s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact

theorem step109wc166s6Dispatch :
    QuotientRankAtLeast (o166SourceU_wc ⟨6, by omega⟩) 15 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 273) o81W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 273) hP hQ o81W_wc 15
      step109_orbit81_lb15_wc
  exact quotientRankAtLeast_mono step109wc166s6_contain hAct


private theorem step109wc166s7_QtInv :
    (codeMat 277 : Mat3).transpose⁻¹ = (codeMat 277 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 277 : Mat3).transpose * (codeMat 277 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc166s7_contain :
    (o166SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 401) (codeMat 277) o81W_wc := by
  change spanCodes [290, 166, 96, 20, 10, 1] ≤ actionW (codeMat 401) (codeMat 277) o81W_wc
  apply step109wc166_spanCodes_le_of_gens [290, 166, 96, 20, 10, 1]
    (actionW (codeMat 401) (codeMat 277) o81W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 322 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 322 (by decide)
    have hact : actionA (codeMat 401) (codeMat 277) (codeMat 322) = codeMat 290 := by
      unfold actionA
      rw [step109wc166s7_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 322 * (codeMat 277 : Mat3).transpose = codeMat 290
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 191 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 191 (by decide)
    have hact : actionA (codeMat 401) (codeMat 277) (codeMat 191) = codeMat 166 := by
      unfold actionA
      rw [step109wc166s7_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 191 * (codeMat 277 : Mat3).transpose = codeMat 166
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 96 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 96 (by decide)
    have hact : actionA (codeMat 401) (codeMat 277) (codeMat 96) = codeMat 96 := by
      unfold actionA
      rw [step109wc166s7_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 96 * (codeMat 277 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 21 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 21 (by decide)
    have hact : actionA (codeMat 401) (codeMat 277) (codeMat 21) = codeMat 20 := by
      unfold actionA
      rw [step109wc166s7_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 21 * (codeMat 277 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 401) (codeMat 277) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step109wc166s7_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 10 * (codeMat 277 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 401) (codeMat 277) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc166s7_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 1 * (codeMat 277 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact

theorem step109wc166s7Dispatch :
    QuotientRankAtLeast (o166SourceU_wc ⟨7, by omega⟩) 15 := by
  have hP : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 277 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 401) (codeMat 277) o81W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 401) (codeMat 277) hP hQ o81W_wc 15
      step109_orbit81_lb15_wc
  exact quotientRankAtLeast_mono step109wc166s7_contain hAct


private theorem step109wc166s8_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc166s8_contain :
    (o166SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 273) (codeMat 161) o51W_wc := by
  change spanCodes [290, 96, 16, 10, 4, 1] ≤ actionW (codeMat 273) (codeMat 161) o51W_wc
  apply step109wc166_spanCodes_le_of_gens [290, 96, 16, 10, 4, 1]
    (actionW (codeMat 273) (codeMat 161) o51W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 148 ∈ o51W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [148, 80, 32, 12, 2, 1] 148 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 148) = codeMat 290 := by
      unfold actionA
      rw [step109wc166s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 148 * (codeMat 161 : Mat3).transpose = codeMat 290
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 80 ∈ o51W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [148, 80, 32, 12, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 80) = codeMat 96 := by
      unfold actionA
      rw [step109wc166s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 80 * (codeMat 161 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ o51W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [148, 80, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 32) = codeMat 16 := by
      unfold actionA
      rw [step109wc166s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 32 * (codeMat 161 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 12 ∈ o51W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [148, 80, 32, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 12) = codeMat 10 := by
      unfold actionA
      rw [step109wc166s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 12 * (codeMat 161 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o51W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [148, 80, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 2) = codeMat 4 := by
      unfold actionA
      rw [step109wc166s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o51W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [148, 80, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc166s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact

theorem step109wc166s8Dispatch :
    QuotientRankAtLeast (o166SourceU_wc ⟨8, by omega⟩) 14 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 161) o51W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 161) hP hQ o51W_wc 14
      step109_orbit51_lb14_wc
  exact quotientRankAtLeast_mono step109wc166s8_contain hAct

private def step109wc166s9SrcT : Submodule F2 Mat3 := spanCodes [272, 128, 66, 34, 8, 1]

private theorem step109wc166s9SrcT_lb : QuotientRankAtLeast step109wc166s9SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step99_orbit55_lb14_unconditional
  have hle : step109wc166s9SrcT ≤ transposeW o55W := by
    unfold step109wc166s9SrcT transposeW
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

private theorem step109wc166s9_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc166s9_contain :
    (o166SourceU_wc ⟨9, by omega⟩) ≤ actionW (codeMat 140) (codeMat 161) step109wc166s9SrcT := by
  change spanCodes [258, 64, 32, 20, 10, 1] ≤ actionW (codeMat 140) (codeMat 161) step109wc166s9SrcT
  apply step109wc166_spanCodes_le_of_gens [258, 64, 32, 20, 10, 1]
    (actionW (codeMat 140) (codeMat 161) step109wc166s9SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 34 ∈ step109wc166s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 34 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 34) = codeMat 258 := by
      unfold actionA
      rw [step109wc166s9_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 34 * (codeMat 161 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ step109wc166s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 1) = codeMat 64 := by
      unfold actionA
      rw [step109wc166s9_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 128 ∈ step109wc166s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 128 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 128) = codeMat 32 := by
      unfold actionA
      rw [step109wc166s9_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 128 * (codeMat 161 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 272 ∈ step109wc166s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 272 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 272) = codeMat 20 := by
      unfold actionA
      rw [step109wc166s9_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 272 * (codeMat 161 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 96 ∈ step109wc166s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 96 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step109wc166s9_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 96 * (codeMat 161 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ step109wc166s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 8 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc166s9_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact

theorem step109wc166s9Dispatch :
    QuotientRankAtLeast (o166SourceU_wc ⟨9, by omega⟩) 14 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 161) step109wc166s9SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 161) hP hQ step109wc166s9SrcT 14
      step109wc166s9SrcT_lb
  exact quotientRankAtLeast_mono step109wc166s9_contain hAct

private def step109wc166s10SrcT : Submodule F2 Mat3 := spanCodes [272, 128, 66, 34, 8, 1]

private theorem step109wc166s10SrcT_lb : QuotientRankAtLeast step109wc166s10SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step99_orbit55_lb14_unconditional
  have hle : step109wc166s10SrcT ≤ transposeW o55W := by
    unfold step109wc166s10SrcT transposeW
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

private theorem step109wc166s10_QtInv :
    (codeMat 165 : Mat3).transpose⁻¹ = (codeMat 163 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 165 : Mat3).transpose * (codeMat 163 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc166s10_contain :
    (o166SourceU_wc ⟨10, by omega⟩) ≤ actionW (codeMat 142) (codeMat 165) step109wc166s10SrcT := by
  change spanCodes [256, 66, 34, 20, 10, 1] ≤ actionW (codeMat 142) (codeMat 165) step109wc166s10SrcT
  apply step109wc166_spanCodes_le_of_gens [256, 66, 34, 20, 10, 1]
    (actionW (codeMat 142) (codeMat 165) step109wc166s10SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 195 ∈ step109wc166s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 195 (by decide)
    have hact : actionA (codeMat 142) (codeMat 165) (codeMat 195) = codeMat 256 := by
      unfold actionA
      rw [step109wc166s10_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 195 * (codeMat 163 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 97 ∈ step109wc166s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 97 (by decide)
    have hact : actionA (codeMat 142) (codeMat 165) (codeMat 97) = codeMat 66 := by
      unfold actionA
      rw [step109wc166s10_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 97 * (codeMat 163 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 224 ∈ step109wc166s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 224 (by decide)
    have hact : actionA (codeMat 142) (codeMat 165) (codeMat 224) = codeMat 34 := by
      unfold actionA
      rw [step109wc166s10_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 224 * (codeMat 163 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 280 ∈ step109wc166s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 280 (by decide)
    have hact : actionA (codeMat 142) (codeMat 165) (codeMat 280) = codeMat 20 := by
      unfold actionA
      rw [step109wc166s10_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 280 * (codeMat 163 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 96 ∈ step109wc166s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 96 (by decide)
    have hact : actionA (codeMat 142) (codeMat 165) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step109wc166s10_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 96 * (codeMat 163 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ step109wc166s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 8 (by decide)
    have hact : actionA (codeMat 142) (codeMat 165) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc166s10_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 8 * (codeMat 163 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact

theorem step109wc166s10Dispatch :
    QuotientRankAtLeast (o166SourceU_wc ⟨10, by omega⟩) 14 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 165 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 165) step109wc166s10SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 165) hP hQ step109wc166s10SrcT 14
      step109wc166s10SrcT_lb
  exact quotientRankAtLeast_mono step109wc166s10_contain hAct


private theorem step109wc166s11_QtInv :
    (codeMat 309 : Mat3).transpose⁻¹ = (codeMat 309 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 309 : Mat3).transpose * (codeMat 309 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc166s11_contain :
    (o166SourceU_wc ⟨11, by omega⟩) ≤ actionW (codeMat 345) (codeMat 309) o82W := by
  change spanCodes [290, 162, 96, 20, 10, 1] ≤ actionW (codeMat 345) (codeMat 309) o82W
  apply step109wc166_spanCodes_le_of_gens [290, 162, 96, 20, 10, 1]
    (actionW (codeMat 345) (codeMat 309) o82W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 506 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 506 (by decide)
    have hact : actionA (codeMat 345) (codeMat 309) (codeMat 506) = codeMat 290 := by
      unfold actionA
      rw [step109wc166s11_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 506 * (codeMat 309 : Mat3).transpose = codeMat 290
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 191 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 191 (by decide)
    have hact : actionA (codeMat 345) (codeMat 309) (codeMat 191) = codeMat 162 := by
      unfold actionA
      rw [step109wc166s11_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 191 * (codeMat 309 : Mat3).transpose = codeMat 162
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 126 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 126 (by decide)
    have hact : actionA (codeMat 345) (codeMat 309) (codeMat 126) = codeMat 96 := by
      unfold actionA
      rw [step109wc166s11_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 126 * (codeMat 309 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 21 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 21 (by decide)
    have hact : actionA (codeMat 345) (codeMat 309) (codeMat 21) = codeMat 20 := by
      unfold actionA
      rw [step109wc166s11_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 21 * (codeMat 309 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 11 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 345) (codeMat 309) (codeMat 11) = codeMat 10 := by
      unfold actionA
      rw [step109wc166s11_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 11 * (codeMat 309 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 345) (codeMat 309) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc166s11_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 1 * (codeMat 309 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact

theorem step109wc166s11Dispatch :
    QuotientRankAtLeast (o166SourceU_wc ⟨11, by omega⟩) 14 := by
  have hP : Invertible (codeMat 345 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 309 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 345) (codeMat 309) o82W) 14 :=
    @quotientRankAtLeast_action (codeMat 345) (codeMat 309) hP hQ o82W 14
      step99_orbit82_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc166s11_contain hAct


private theorem step109wc166s12_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = (codeMat 305 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * (codeMat 305 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc166s12_contain :
    (o166SourceU_wc ⟨12, by omega⟩) ≤ actionW (codeMat 473) (codeMat 305) o82W := by
  change spanCodes [290, 164, 96, 20, 10, 1] ≤ actionW (codeMat 473) (codeMat 305) o82W
  apply step109wc166_spanCodes_le_of_gens [290, 164, 96, 20, 10, 1]
    (actionW (codeMat 473) (codeMat 305) o82W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 388 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 388 (by decide)
    have hact : actionA (codeMat 473) (codeMat 305) (codeMat 388) = codeMat 290 := by
      unfold actionA
      rw [step109wc166s12_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 388 * (codeMat 305 : Mat3).transpose = codeMat 290
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 473) (codeMat 305) (codeMat 160) = codeMat 164 := by
      unfold actionA
      rw [step109wc166s12_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 160 * (codeMat 305 : Mat3).transpose = codeMat 164
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 126 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 126 (by decide)
    have hact : actionA (codeMat 473) (codeMat 305) (codeMat 126) = codeMat 96 := by
      unfold actionA
      rw [step109wc166s12_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 126 * (codeMat 305 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 20 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 20 (by decide)
    have hact : actionA (codeMat 473) (codeMat 305) (codeMat 20) = codeMat 20 := by
      unfold actionA
      rw [step109wc166s12_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 20 * (codeMat 305 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 11 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 473) (codeMat 305) (codeMat 11) = codeMat 10 := by
      unfold actionA
      rw [step109wc166s12_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 11 * (codeMat 305 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 473) (codeMat 305) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc166s12_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 1 * (codeMat 305 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact

theorem step109wc166s12Dispatch :
    QuotientRankAtLeast (o166SourceU_wc ⟨12, by omega⟩) 14 := by
  have hP : Invertible (codeMat 473 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 473) (codeMat 305) o82W) 14 :=
    @quotientRankAtLeast_action (codeMat 473) (codeMat 305) hP hQ o82W 14
      step99_orbit82_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc166s12_contain hAct


private theorem step109wc166s13_QtInv :
    (codeMat 277 : Mat3).transpose⁻¹ = (codeMat 277 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 277 : Mat3).transpose * (codeMat 277 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc166s13_contain :
    (o166SourceU_wc ⟨13, by omega⟩) ≤ actionW (codeMat 273) (codeMat 277) o36W_wc := by
  change spanCodes [288, 96, 20, 8, 2, 1] ≤ actionW (codeMat 273) (codeMat 277) o36W_wc
  apply step109wc166_spanCodes_le_of_gens [288, 96, 20, 8, 2, 1]
    (actionW (codeMat 273) (codeMat 277) o36W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 360 ∈ o36W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 8, 2, 1] 360 (by decide)
    have hact : actionA (codeMat 273) (codeMat 277) (codeMat 360) = codeMat 288 := by
      unfold actionA
      rw [step109wc166s13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 360 * (codeMat 277 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 104 ∈ o36W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 8, 2, 1] 104 (by decide)
    have hact : actionA (codeMat 273) (codeMat 277) (codeMat 104) = codeMat 96 := by
      unfold actionA
      rw [step109wc166s13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 104 * (codeMat 277 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 21 ∈ o36W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 8, 2, 1] 21 (by decide)
    have hact : actionA (codeMat 273) (codeMat 277) (codeMat 21) = codeMat 20 := by
      unfold actionA
      rw [step109wc166s13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 21 * (codeMat 277 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ o36W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 277) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc166s13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 277 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o36W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 277) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc166s13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 277 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o36W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 277) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc166s13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 277 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact

theorem step109wc166s13Dispatch :
    QuotientRankAtLeast (o166SourceU_wc ⟨13, by omega⟩) 13 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 277 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 277) o36W_wc) 13 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 277) hP hQ o36W_wc 13
      step109_orbit36_lb13_wc
  exact quotientRankAtLeast_mono step109wc166s13_contain hAct


private theorem step109wc166s14_QtInv :
    (codeMat 421 : Mat3).transpose⁻¹ = (codeMat 179 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 421 : Mat3).transpose * (codeMat 179 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc166s14_contain :
    (o166SourceU_wc ⟨14, by omega⟩) ≤ actionW (codeMat 345) (codeMat 421) o53W_mono := by
  change spanCodes [290, 96, 18, 10, 6, 1] ≤ actionW (codeMat 345) (codeMat 421) o53W_mono
  apply step109wc166_spanCodes_le_of_gens [290, 96, 18, 10, 6, 1]
    (actionW (codeMat 345) (codeMat 421) o53W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 508 ∈ o53W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [384, 80, 32, 12, 2, 1] 508 (by decide)
    have hact : actionA (codeMat 345) (codeMat 421) (codeMat 508) = codeMat 290 := by
      unfold actionA
      rw [step109wc166s14_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 508 * (codeMat 179 : Mat3).transpose = codeMat 290
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 126 ∈ o53W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [384, 80, 32, 12, 2, 1] 126 (by decide)
    have hact : actionA (codeMat 345) (codeMat 421) (codeMat 126) = codeMat 96 := by
      unfold actionA
      rw [step109wc166s14_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 126 * (codeMat 179 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ o53W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [384, 80, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 345) (codeMat 421) (codeMat 32) = codeMat 18 := by
      unfold actionA
      rw [step109wc166s14_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 32 * (codeMat 179 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 13 ∈ o53W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [384, 80, 32, 12, 2, 1] 13 (by decide)
    have hact : actionA (codeMat 345) (codeMat 421) (codeMat 13) = codeMat 10 := by
      unfold actionA
      rw [step109wc166s14_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 13 * (codeMat 179 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o53W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [384, 80, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 345) (codeMat 421) (codeMat 3) = codeMat 6 := by
      unfold actionA
      rw [step109wc166s14_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 3 * (codeMat 179 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o53W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [384, 80, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 345) (codeMat 421) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc166s14_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 1 * (codeMat 179 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc166_codeMat_mem_actionW_of_witness hw hact

theorem step109wc166s14Dispatch :
    QuotientRankAtLeast (o166SourceU_wc ⟨14, by omega⟩) 12 := by
  have hP : Invertible (codeMat 345 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 421 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 345) (codeMat 421) o53W_mono) 12 :=
    @quotientRankAtLeast_action (codeMat 345) (codeMat 421) hP hQ o53W_mono 12
      orbit53_lb12_mono
  exact quotientRankAtLeast_mono step109wc166s14_contain hAct

theorem step109wc166_all_dispatch (i : Fin 15) :
    QuotientRankAtLeast (o166SourceU_wc i) (o166SourceLb_wc i) := by
  fin_cases i
  · exact step109wc166s0Dispatch
  · exact step109wc166s1Dispatch
  · exact step109wc166s2Dispatch
  · exact step109wc166s3Dispatch
  · exact step109wc166s4Dispatch
  · exact step109wc166s5Dispatch
  · exact step109wc166s6Dispatch
  · exact step109wc166s7Dispatch
  · exact step109wc166s8Dispatch
  · exact step109wc166s9Dispatch
  · exact step109wc166s10Dispatch
  · exact step109wc166s11Dispatch
  · exact step109wc166s12Dispatch
  · exact step109wc166s13Dispatch
  · exact step109wc166s14Dispatch

theorem step109_orbit166_lb16_wc : QuotientRankAtLeast o166W_wc 16 :=
  o166Lb16_wc step109wc166_all_dispatch

end QiushiMatmul
