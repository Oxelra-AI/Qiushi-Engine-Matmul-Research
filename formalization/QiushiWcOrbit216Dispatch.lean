import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit216Consumer
import QiushiStep99Orbit67Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiStep99Orbit77Dispatch
import QiushiWcOrbit81Dispatch
import QiushiWcOrbit72Dispatch
import QiushiWcOrbit51Dispatch
import QiushiStep99Orbit55Dispatch
import QiushiMonoOrbit71From17
import QiushiWcOrbit84Dispatch
import QiushiWcOrbit79Dispatch
import QiushiMonoOrbit49From10

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc216_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc216_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc216s0_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = (codeMat 267 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * (codeMat 267 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc216s0_contain :
    (o216SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 267) (codeMat 282) o67W := by
  change spanCodes [294, 132, 96, 16, 10, 1] ≤ actionW (codeMat 267) (codeMat 282) o67W
  apply step109wc216_spanCodes_le_of_gens [294, 132, 96, 16, 10, 1]
    (actionW (codeMat 267) (codeMat 282) o67W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 284 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 284 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 284) = codeMat 294 := by
      unfold actionA
      rw [step109wc216s0_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 284 * (codeMat 267 : Mat3).transpose = codeMat 294
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 224 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 224 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 224) = codeMat 132 := by
      unfold actionA
      rw [step109wc216s0_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 224 * (codeMat 267 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 164 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 164 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 164) = codeMat 96 := by
      unfold actionA
      rw [step109wc216s0_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 164 * (codeMat 267 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 27 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 27) = codeMat 16 := by
      unfold actionA
      rw [step109wc216s0_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 27 * (codeMat 267 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step109wc216s0_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 10 * (codeMat 267 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc216s0_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 16 * (codeMat 267 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact

theorem step109wc216s0Dispatch :
    QuotientRankAtLeast (o216SourceU_wc ⟨0, by omega⟩) 15 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 282) o67W) 15 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 282) hP hQ o67W 15
      step99_orbit67_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc216s0_contain hAct


private theorem step109wc216s1_QtInv :
    (codeMat 270 : Mat3).transpose⁻¹ = (codeMat 298 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 270 : Mat3).transpose * (codeMat 298 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc216s1_contain :
    (o216SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 395) (codeMat 270) o69W := by
  change spanCodes [294, 132, 96, 18, 10, 1] ≤ actionW (codeMat 395) (codeMat 270) o69W
  apply step109wc216_spanCodes_le_of_gens [294, 132, 96, 18, 10, 1]
    (actionW (codeMat 395) (codeMat 270) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 352 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 352 (by decide)
    have hact : actionA (codeMat 395) (codeMat 270) (codeMat 352) = codeMat 294 := by
      unfold actionA
      rw [step109wc216s1_QtInv]
      show (codeMat 395 : Mat3).transpose * codeMat 352 * (codeMat 298 : Mat3).transpose = codeMat 294
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 97 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 97 (by decide)
    have hact : actionA (codeMat 395) (codeMat 270) (codeMat 97) = codeMat 132 := by
      unfold actionA
      rw [step109wc216s1_QtInv]
      show (codeMat 395 : Mat3).transpose * codeMat 97 * (codeMat 298 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 191 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 191 (by decide)
    have hact : actionA (codeMat 395) (codeMat 270) (codeMat 191) = codeMat 96 := by
      unfold actionA
      rw [step109wc216s1_QtInv]
      show (codeMat 395 : Mat3).transpose * codeMat 191 * (codeMat 298 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 395) (codeMat 270) (codeMat 1) = codeMat 18 := by
      unfold actionA
      rw [step109wc216s1_QtInv]
      show (codeMat 395 : Mat3).transpose * codeMat 1 * (codeMat 298 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 26 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 26 (by decide)
    have hact : actionA (codeMat 395) (codeMat 270) (codeMat 26) = codeMat 10 := by
      unfold actionA
      rw [step109wc216s1_QtInv]
      show (codeMat 395 : Mat3).transpose * codeMat 26 * (codeMat 298 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 395) (codeMat 270) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc216s1_QtInv]
      show (codeMat 395 : Mat3).transpose * codeMat 16 * (codeMat 298 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact

theorem step109wc216s1Dispatch :
    QuotientRankAtLeast (o216SourceU_wc ⟨1, by omega⟩) 15 := by
  have hP : Invertible (codeMat 395 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 270 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 395) (codeMat 270) o69W) 15 :=
    @quotientRankAtLeast_action (codeMat 395) (codeMat 270) hP hQ o69W 15
      step99_orbit69_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc216s1_contain hAct


private theorem step109wc216s2_QtInv :
    (codeMat 396 : Mat3).transpose⁻¹ = (codeMat 106 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 396 : Mat3).transpose * (codeMat 106 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc216s2_contain :
    (o216SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 95) (codeMat 396) o77W := by
  change spanCodes [294, 132, 96, 20, 10, 1] ≤ actionW (codeMat 95) (codeMat 396) o77W
  apply step109wc216_spanCodes_le_of_gens [294, 132, 96, 20, 10, 1]
    (actionW (codeMat 95) (codeMat 396) o77W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 261 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 261 (by decide)
    have hact : actionA (codeMat 95) (codeMat 396) (codeMat 261) = codeMat 294 := by
      unfold actionA
      rw [step109wc216s2_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 261 * (codeMat 106 : Mat3).transpose = codeMat 294
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 356 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 356 (by decide)
    have hact : actionA (codeMat 95) (codeMat 396) (codeMat 356) = codeMat 132 := by
      unfold actionA
      rw [step109wc216s2_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 356 * (codeMat 106 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 378 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 378 (by decide)
    have hact : actionA (codeMat 95) (codeMat 396) (codeMat 378) = codeMat 96 := by
      unfold actionA
      rw [step109wc216s2_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 378 * (codeMat 106 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 96 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 96 (by decide)
    have hact : actionA (codeMat 95) (codeMat 396) (codeMat 96) = codeMat 20 := by
      unfold actionA
      rw [step109wc216s2_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 96 * (codeMat 106 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 400 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 400 (by decide)
    have hact : actionA (codeMat 95) (codeMat 396) (codeMat 400) = codeMat 10 := by
      unfold actionA
      rw [step109wc216s2_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 400 * (codeMat 106 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 95) (codeMat 396) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc216s2_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 128 * (codeMat 106 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact

theorem step109wc216s2Dispatch :
    QuotientRankAtLeast (o216SourceU_wc ⟨2, by omega⟩) 15 := by
  have hP : Invertible (codeMat 95 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 396 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 95) (codeMat 396) o77W) 15 :=
    @quotientRankAtLeast_action (codeMat 95) (codeMat 396) hP hQ o77W 15
      step99_orbit77_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc216s2_contain hAct


private theorem step109wc216s3_QtInv :
    (codeMat 279 : Mat3).transpose⁻¹ = (codeMat 279 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 279 : Mat3).transpose * (codeMat 279 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc216s3_contain :
    (o216SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 465) (codeMat 279) o81W_wc := by
  change spanCodes [294, 132, 96, 22, 10, 1] ≤ actionW (codeMat 465) (codeMat 279) o81W_wc
  apply step109wc216_spanCodes_le_of_gens [294, 132, 96, 22, 10, 1]
    (actionW (codeMat 465) (codeMat 279) o81W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 323 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 323 (by decide)
    have hact : actionA (codeMat 465) (codeMat 279) (codeMat 323) = codeMat 294 := by
      unfold actionA
      rw [step109wc216s3_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 323 * (codeMat 279 : Mat3).transpose = codeMat 294
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 222 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 222 (by decide)
    have hact : actionA (codeMat 465) (codeMat 279) (codeMat 222) = codeMat 132 := by
      unfold actionA
      rw [step109wc216s3_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 222 * (codeMat 279 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 97 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 97 (by decide)
    have hact : actionA (codeMat 465) (codeMat 279) (codeMat 97) = codeMat 96 := by
      unfold actionA
      rw [step109wc216s3_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 97 * (codeMat 279 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 30 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 30 (by decide)
    have hact : actionA (codeMat 465) (codeMat 279) (codeMat 30) = codeMat 22 := by
      unfold actionA
      rw [step109wc216s3_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 30 * (codeMat 279 : Mat3).transpose = codeMat 22
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 11 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 465) (codeMat 279) (codeMat 11) = codeMat 10 := by
      unfold actionA
      rw [step109wc216s3_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 11 * (codeMat 279 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 465) (codeMat 279) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc216s3_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 1 * (codeMat 279 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact

theorem step109wc216s3Dispatch :
    QuotientRankAtLeast (o216SourceU_wc ⟨3, by omega⟩) 15 := by
  have hP : Invertible (codeMat 465 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 279 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 465) (codeMat 279) o81W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 465) (codeMat 279) hP hQ o81W_wc 15
      step109_orbit81_lb15_wc
  exact quotientRankAtLeast_mono step109wc216s3_contain hAct


private theorem step109wc216s4_QtInv :
    (codeMat 86 : Mat3).transpose⁻¹ = (codeMat 212 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 86 : Mat3).transpose * (codeMat 212 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc216s4_contain :
    (o216SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 396) (codeMat 86) o72W_wc := by
  change spanCodes [256, 132, 70, 38, 10, 1] ≤ actionW (codeMat 396) (codeMat 86) o72W_wc
  apply step109wc216_spanCodes_le_of_gens [256, 132, 70, 38, 10, 1]
    (actionW (codeMat 396) (codeMat 86) o72W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 1 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 396) (codeMat 86) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc216s4_QtInv]
      show (codeMat 396 : Mat3).transpose * codeMat 1 * (codeMat 212 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 11 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 396) (codeMat 86) (codeMat 11) = codeMat 132 := by
      unfold actionA
      rw [step109wc216s4_QtInv]
      show (codeMat 396 : Mat3).transpose * codeMat 11 * (codeMat 212 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 20 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 20 (by decide)
    have hact : actionA (codeMat 396) (codeMat 86) (codeMat 20) = codeMat 70 := by
      unfold actionA
      rw [step109wc216s4_QtInv]
      show (codeMat 396 : Mat3).transpose * codeMat 20 * (codeMat 212 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 81 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 81 (by decide)
    have hact : actionA (codeMat 396) (codeMat 86) (codeMat 81) = codeMat 38 := by
      unfold actionA
      rw [step109wc216s4_QtInv]
      show (codeMat 396 : Mat3).transpose * codeMat 81 * (codeMat 212 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 284 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 284 (by decide)
    have hact : actionA (codeMat 396) (codeMat 86) (codeMat 284) = codeMat 10 := by
      unfold actionA
      rw [step109wc216s4_QtInv]
      show (codeMat 396 : Mat3).transpose * codeMat 284 * (codeMat 212 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 396) (codeMat 86) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc216s4_QtInv]
      show (codeMat 396 : Mat3).transpose * codeMat 32 * (codeMat 212 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact

theorem step109wc216s4Dispatch :
    QuotientRankAtLeast (o216SourceU_wc ⟨4, by omega⟩) 15 := by
  have hP : Invertible (codeMat 396 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 396) (codeMat 86) o72W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 396) (codeMat 86) hP hQ o72W_wc 15
      step109_orbit72_lb15_wc
  exact quotientRankAtLeast_mono step109wc216s4_contain hAct

private def step109wc216s5SrcT : Submodule F2 Mat3 := spanCodes [272, 132, 80, 32, 10, 1]

private theorem step109wc216s5SrcT_lb : QuotientRankAtLeast step109wc216s5SrcT 15 := by
  have ht := quotientRankAtLeast_transpose step99_orbit77_lb15_unconditional
  have hle : step109wc216s5SrcT ≤ transposeW o77W := by
    unfold step109wc216s5SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4 | h5
    · subst h0
      show codeMat 272 ∈ Submodule.map transposeLinearMap o77W
      exact ⟨codeMat 272, spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 272 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 132 ∈ Submodule.map transposeLinearMap o77W
      exact ⟨codeMat 96, spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 96 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 80 ∈ Submodule.map transposeLinearMap o77W
      exact ⟨codeMat 20, spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 20 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 32 ∈ Submodule.map transposeLinearMap o77W
      exact ⟨codeMat 128, spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 128 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 10 ∈ Submodule.map transposeLinearMap o77W
      exact ⟨codeMat 10, spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 10 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h5
      show codeMat 1 ∈ Submodule.map transposeLinearMap o77W
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc216s5_QtInv :
    (codeMat 499 : Mat3).transpose⁻¹ = (codeMat 382 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 499 : Mat3).transpose * (codeMat 382 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc216s5_contain :
    (o216SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 114) (codeMat 499) step109wc216s5SrcT := by
  change spanCodes [278, 132, 80, 48, 10, 1] ≤ actionW (codeMat 114) (codeMat 499) step109wc216s5SrcT
  apply step109wc216_spanCodes_le_of_gens [278, 132, 80, 48, 10, 1]
    (actionW (codeMat 114) (codeMat 499) step109wc216s5SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 113 ∈ step109wc216s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 113 (by decide)
    have hact : actionA (codeMat 114) (codeMat 499) (codeMat 113) = codeMat 278 := by
      unfold actionA
      rw [step109wc216s5_QtInv]
      show (codeMat 114 : Mat3).transpose * codeMat 113 * (codeMat 382 : Mat3).transpose = codeMat 278
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 447 ∈ step109wc216s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 447 (by decide)
    have hact : actionA (codeMat 114) (codeMat 499) (codeMat 447) = codeMat 132 := by
      unfold actionA
      rw [step109wc216s5_QtInv]
      show (codeMat 114 : Mat3).transpose * codeMat 447 * (codeMat 382 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 42 ∈ step109wc216s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 42 (by decide)
    have hact : actionA (codeMat 114) (codeMat 499) (codeMat 42) = codeMat 80 := by
      unfold actionA
      rw [step109wc216s5_QtInv]
      show (codeMat 114 : Mat3).transpose * codeMat 42 * (codeMat 382 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ step109wc216s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 114) (codeMat 499) (codeMat 1) = codeMat 48 := by
      unfold actionA
      rw [step109wc216s5_QtInv]
      show (codeMat 114 : Mat3).transpose * codeMat 1 * (codeMat 382 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 453 ∈ step109wc216s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 453 (by decide)
    have hact : actionA (codeMat 114) (codeMat 499) (codeMat 453) = codeMat 10 := by
      unfold actionA
      rw [step109wc216s5_QtInv]
      show (codeMat 114 : Mat3).transpose * codeMat 453 * (codeMat 382 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 320 ∈ step109wc216s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 320 (by decide)
    have hact : actionA (codeMat 114) (codeMat 499) (codeMat 320) = codeMat 1 := by
      unfold actionA
      rw [step109wc216s5_QtInv]
      show (codeMat 114 : Mat3).transpose * codeMat 320 * (codeMat 382 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact

theorem step109wc216s5Dispatch :
    QuotientRankAtLeast (o216SourceU_wc ⟨5, by omega⟩) 15 := by
  have hP : Invertible (codeMat 114 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 499 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 114) (codeMat 499) step109wc216s5SrcT) 15 :=
    @quotientRankAtLeast_action (codeMat 114) (codeMat 499) hP hQ step109wc216s5SrcT 15
      step109wc216s5SrcT_lb
  exact quotientRankAtLeast_mono step109wc216s5_contain hAct


private theorem step109wc216s6_QtInv :
    (codeMat 431 : Mat3).transpose⁻¹ = (codeMat 477 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 431 : Mat3).transpose * (codeMat 477 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc216s6_contain :
    (o216SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 98) (codeMat 431) o81W_wc := by
  change spanCodes [276, 132, 82, 50, 10, 1] ≤ actionW (codeMat 98) (codeMat 431) o81W_wc
  apply step109wc216_spanCodes_le_of_gens [276, 132, 82, 50, 10, 1]
    (actionW (codeMat 98) (codeMat 431) o81W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 509 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 509 (by decide)
    have hact : actionA (codeMat 98) (codeMat 431) (codeMat 509) = codeMat 276 := by
      unfold actionA
      rw [step109wc216s6_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 509 * (codeMat 477 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 488 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 488 (by decide)
    have hact : actionA (codeMat 98) (codeMat 431) (codeMat 488) = codeMat 132 := by
      unfold actionA
      rw [step109wc216s6_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 488 * (codeMat 477 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 349 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 349 (by decide)
    have hact : actionA (codeMat 98) (codeMat 431) (codeMat 349) = codeMat 82 := by
      unfold actionA
      rw [step109wc216s6_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 349 * (codeMat 477 : Mat3).transpose = codeMat 82
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 322 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 322 (by decide)
    have hact : actionA (codeMat 98) (codeMat 431) (codeMat 322) = codeMat 50 := by
      unfold actionA
      rw [step109wc216s6_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 322 * (codeMat 477 : Mat3).transpose = codeMat 50
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 323 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 323 (by decide)
    have hact : actionA (codeMat 98) (codeMat 431) (codeMat 323) = codeMat 10 := by
      unfold actionA
      rw [step109wc216s6_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 323 * (codeMat 477 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 192 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 192 (by decide)
    have hact : actionA (codeMat 98) (codeMat 431) (codeMat 192) = codeMat 1 := by
      unfold actionA
      rw [step109wc216s6_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 192 * (codeMat 477 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact

theorem step109wc216s6Dispatch :
    QuotientRankAtLeast (o216SourceU_wc ⟨6, by omega⟩) 15 := by
  have hP : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 431 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 98) (codeMat 431) o81W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 98) (codeMat 431) hP hQ o81W_wc 15
      step109_orbit81_lb15_wc
  exact quotientRankAtLeast_mono step109wc216s6_contain hAct


private theorem step109wc216s7_QtInv :
    (codeMat 169 : Mat3).transpose⁻¹ = (codeMat 225 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 169 : Mat3).transpose * (codeMat 225 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc216s7_contain :
    (o216SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 161) (codeMat 169) o51W_wc := by
  change spanCodes [290, 128, 96, 10, 4, 1] ≤ actionW (codeMat 161) (codeMat 169) o51W_wc
  apply step109wc216_spanCodes_le_of_gens [290, 128, 96, 10, 4, 1]
    (actionW (codeMat 161) (codeMat 169) o51W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 148 ∈ o51W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [148, 80, 32, 12, 2, 1] 148 (by decide)
    have hact : actionA (codeMat 161) (codeMat 169) (codeMat 148) = codeMat 290 := by
      unfold actionA
      rw [step109wc216s7_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 148 * (codeMat 225 : Mat3).transpose = codeMat 290
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 32 ∈ o51W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [148, 80, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 161) (codeMat 169) (codeMat 32) = codeMat 128 := by
      unfold actionA
      rw [step109wc216s7_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 32 * (codeMat 225 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 152 ∈ o51W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [148, 80, 32, 12, 2, 1] 152 (by decide)
    have hact : actionA (codeMat 161) (codeMat 169) (codeMat 152) = codeMat 96 := by
      unfold actionA
      rw [step109wc216s7_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 152 * (codeMat 225 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 196 ∈ o51W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [148, 80, 32, 12, 2, 1] 196 (by decide)
    have hact : actionA (codeMat 161) (codeMat 169) (codeMat 196) = codeMat 10 := by
      unfold actionA
      rw [step109wc216s7_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 196 * (codeMat 225 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o51W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [148, 80, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 169) (codeMat 2) = codeMat 4 := by
      unfold actionA
      rw [step109wc216s7_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 225 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ o51W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [148, 80, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 161) (codeMat 169) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step109wc216s7_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 3 * (codeMat 225 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact

theorem step109wc216s7Dispatch :
    QuotientRankAtLeast (o216SourceU_wc ⟨7, by omega⟩) 14 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 169) o51W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 169) hP hQ o51W_wc 14
      step109_orbit51_lb14_wc
  exact quotientRankAtLeast_mono step109wc216s7_contain hAct


private theorem step109wc216s8_QtInv :
    (codeMat 426 : Mat3).transpose⁻¹ = (codeMat 335 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 426 : Mat3).transpose * (codeMat 335 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc216s8_contain :
    (o216SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 225) (codeMat 426) o55W := by
  change spanCodes [288, 130, 96, 10, 6, 1] ≤ actionW (codeMat 225) (codeMat 426) o55W
  apply step109wc216_spanCodes_le_of_gens [288, 130, 96, 10, 6, 1]
    (actionW (codeMat 225) (codeMat 426) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 438 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 438 (by decide)
    have hact : actionA (codeMat 225) (codeMat 426) (codeMat 438) = codeMat 288 := by
      unfold actionA
      rw [step109wc216s8_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 438 * (codeMat 335 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 45 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 45 (by decide)
    have hact : actionA (codeMat 225) (codeMat 426) (codeMat 45) = codeMat 130 := by
      unfold actionA
      rw [step109wc216s8_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 45 * (codeMat 335 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 406 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 406 (by decide)
    have hact : actionA (codeMat 225) (codeMat 426) (codeMat 406) = codeMat 96 := by
      unfold actionA
      rw [step109wc216s8_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 406 * (codeMat 335 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 135 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 135 (by decide)
    have hact : actionA (codeMat 225) (codeMat 426) (codeMat 135) = codeMat 10 := by
      unfold actionA
      rw [step109wc216s8_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 135 * (codeMat 335 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 225) (codeMat 426) (codeMat 3) = codeMat 6 := by
      unfold actionA
      rw [step109wc216s8_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 3 * (codeMat 335 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 225) (codeMat 426) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc216s8_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 2 * (codeMat 335 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact

theorem step109wc216s8Dispatch :
    QuotientRankAtLeast (o216SourceU_wc ⟨8, by omega⟩) 14 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 426 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 426) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 426) hP hQ o55W 14
      step99_orbit55_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc216s8_contain hAct

private def step109wc216s9SrcT : Submodule F2 Mat3 := spanCodes [128, 66, 38, 20, 8, 1]

private theorem step109wc216s9SrcT_lb : QuotientRankAtLeast step109wc216s9SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step109_orbit51_lb14_wc
  have hle : step109wc216s9SrcT ≤ transposeW o51W_wc := by
    unfold step109wc216s9SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4 | h5
    · subst h0
      show codeMat 128 ∈ Submodule.map transposeLinearMap o51W_wc
      exact ⟨codeMat 32, spanContainsCodeCore_implies_mem_spanCodes [148, 80, 32, 12, 2, 1] 32 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 66 ∈ Submodule.map transposeLinearMap o51W_wc
      exact ⟨codeMat 12, spanContainsCodeCore_implies_mem_spanCodes [148, 80, 32, 12, 2, 1] 12 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 38 ∈ Submodule.map transposeLinearMap o51W_wc
      exact ⟨codeMat 200, spanContainsCodeCore_implies_mem_spanCodes [148, 80, 32, 12, 2, 1] 200 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 20 ∈ Submodule.map transposeLinearMap o51W_wc
      exact ⟨codeMat 80, spanContainsCodeCore_implies_mem_spanCodes [148, 80, 32, 12, 2, 1] 80 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 8 ∈ Submodule.map transposeLinearMap o51W_wc
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [148, 80, 32, 12, 2, 1] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h5
      show codeMat 1 ∈ Submodule.map transposeLinearMap o51W_wc
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [148, 80, 32, 12, 2, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc216s9_QtInv :
    (codeMat 177 : Mat3).transpose⁻¹ = (codeMat 417 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 177 : Mat3).transpose * (codeMat 417 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc216s9_contain :
    (o216SourceU_wc ⟨9, by omega⟩) ≤ actionW (codeMat 141) (codeMat 177) step109wc216s9SrcT := by
  change spanCodes [262, 132, 64, 32, 10, 1] ≤ actionW (codeMat 141) (codeMat 177) step109wc216s9SrcT
  apply step109wc216_spanCodes_le_of_gens [262, 132, 64, 32, 10, 1]
    (actionW (codeMat 141) (codeMat 177) step109wc216s9SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 50 ∈ step109wc216s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 66, 38, 20, 8, 1] 50 (by decide)
    have hact : actionA (codeMat 141) (codeMat 177) (codeMat 50) = codeMat 262 := by
      unfold actionA
      rw [step109wc216s9_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 50 * (codeMat 417 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 38 ∈ step109wc216s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 66, 38, 20, 8, 1] 38 (by decide)
    have hact : actionA (codeMat 141) (codeMat 177) (codeMat 38) = codeMat 132 := by
      unfold actionA
      rw [step109wc216s9_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 38 * (codeMat 417 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 9 ∈ step109wc216s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 66, 38, 20, 8, 1] 9 (by decide)
    have hact : actionA (codeMat 141) (codeMat 177) (codeMat 9) = codeMat 64 := by
      unfold actionA
      rw [step109wc216s9_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 9 * (codeMat 417 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ step109wc216s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 66, 38, 20, 8, 1] 128 (by decide)
    have hact : actionA (codeMat 141) (codeMat 177) (codeMat 128) = codeMat 32 := by
      unfold actionA
      rw [step109wc216s9_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 128 * (codeMat 417 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 112 ∈ step109wc216s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 66, 38, 20, 8, 1] 112 (by decide)
    have hact : actionA (codeMat 141) (codeMat 177) (codeMat 112) = codeMat 10 := by
      unfold actionA
      rw [step109wc216s9_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 112 * (codeMat 417 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ step109wc216s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 66, 38, 20, 8, 1] 8 (by decide)
    have hact : actionA (codeMat 141) (codeMat 177) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc216s9_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 8 * (codeMat 417 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact

theorem step109wc216s9Dispatch :
    QuotientRankAtLeast (o216SourceU_wc ⟨9, by omega⟩) 14 := by
  have hP : Invertible (codeMat 141 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 141) (codeMat 177) step109wc216s9SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 141) (codeMat 177) hP hQ step109wc216s9SrcT 14
      step109wc216s9SrcT_lb
  exact quotientRankAtLeast_mono step109wc216s9_contain hAct

private def step109wc216s10SrcT : Submodule F2 Mat3 := spanCodes [272, 128, 66, 34, 8, 1]

private theorem step109wc216s10SrcT_lb : QuotientRankAtLeast step109wc216s10SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step99_orbit55_lb14_unconditional
  have hle : step109wc216s10SrcT ≤ transposeW o55W := by
    unfold step109wc216s10SrcT transposeW
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

private theorem step109wc216s10_QtInv :
    (codeMat 163 : Mat3).transpose⁻¹ = (codeMat 165 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 163 : Mat3).transpose * (codeMat 165 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc216s10_contain :
    (o216SourceU_wc ⟨10, by omega⟩) ≤ actionW (codeMat 335) (codeMat 163) step109wc216s10SrcT := by
  change spanCodes [260, 132, 66, 34, 10, 1] ≤ actionW (codeMat 335) (codeMat 163) step109wc216s10SrcT
  apply step109wc216_spanCodes_le_of_gens [260, 132, 66, 34, 10, 1]
    (actionW (codeMat 335) (codeMat 163) step109wc216s10SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 128 ∈ step109wc216s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 128 (by decide)
    have hact : actionA (codeMat 335) (codeMat 163) (codeMat 128) = codeMat 260 := by
      unfold actionA
      rw [step109wc216s10_QtInv]
      show (codeMat 335 : Mat3).transpose * codeMat 128 * (codeMat 165 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 376 ∈ step109wc216s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 376 (by decide)
    have hact : actionA (codeMat 335) (codeMat 163) (codeMat 376) = codeMat 132 := by
      unfold actionA
      rw [step109wc216s10_QtInv]
      show (codeMat 335 : Mat3).transpose * codeMat 376 * (codeMat 165 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 96 ∈ step109wc216s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 96 (by decide)
    have hact : actionA (codeMat 335) (codeMat 163) (codeMat 96) = codeMat 66 := by
      unfold actionA
      rw [step109wc216s10_QtInv]
      show (codeMat 335 : Mat3).transpose * codeMat 96 * (codeMat 165 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 170 ∈ step109wc216s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 170 (by decide)
    have hact : actionA (codeMat 335) (codeMat 163) (codeMat 170) = codeMat 34 := by
      unfold actionA
      rw [step109wc216s10_QtInv]
      show (codeMat 335 : Mat3).transpose * codeMat 170 * (codeMat 165 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 105 ∈ step109wc216s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 105 (by decide)
    have hact : actionA (codeMat 335) (codeMat 163) (codeMat 105) = codeMat 10 := by
      unfold actionA
      rw [step109wc216s10_QtInv]
      show (codeMat 335 : Mat3).transpose * codeMat 105 * (codeMat 165 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ step109wc216s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 8 (by decide)
    have hact : actionA (codeMat 335) (codeMat 163) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc216s10_QtInv]
      show (codeMat 335 : Mat3).transpose * codeMat 8 * (codeMat 165 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact

theorem step109wc216s10Dispatch :
    QuotientRankAtLeast (o216SourceU_wc ⟨10, by omega⟩) 14 := by
  have hP : Invertible (codeMat 335 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 163 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 335) (codeMat 163) step109wc216s10SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 335) (codeMat 163) hP hQ step109wc216s10SrcT 14
      step109wc216s10SrcT_lb
  exact quotientRankAtLeast_mono step109wc216s10_contain hAct


private theorem step109wc216s11_QtInv :
    (codeMat 163 : Mat3).transpose⁻¹ = (codeMat 165 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 163 : Mat3).transpose * (codeMat 165 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc216s11_contain :
    (o216SourceU_wc ⟨11, by omega⟩) ≤ actionW (codeMat 225) (codeMat 163) o71W_mono := by
  change spanCodes [258, 132, 68, 36, 10, 1] ≤ actionW (codeMat 225) (codeMat 163) o71W_mono
  apply step109wc216_spanCodes_le_of_gens [258, 132, 68, 36, 10, 1]
    (actionW (codeMat 225) (codeMat 163) o71W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 21 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 21 (by decide)
    have hact : actionA (codeMat 225) (codeMat 163) (codeMat 21) = codeMat 258 := by
      unfold actionA
      rw [step109wc216s11_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 21 * (codeMat 165 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 42 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 42 (by decide)
    have hact : actionA (codeMat 225) (codeMat 163) (codeMat 42) = codeMat 132 := by
      unfold actionA
      rw [step109wc216s11_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 42 * (codeMat 165 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 10 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 225) (codeMat 163) (codeMat 10) = codeMat 68 := by
      unfold actionA
      rw [step109wc216s11_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 10 * (codeMat 165 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 225) (codeMat 163) (codeMat 128) = codeMat 36 := by
      unfold actionA
      rw [step109wc216s11_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 128 * (codeMat 165 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 68 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 225) (codeMat 163) (codeMat 68) = codeMat 10 := by
      unfold actionA
      rw [step109wc216s11_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 68 * (codeMat 165 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 163) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc216s11_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * (codeMat 165 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact

theorem step109wc216s11Dispatch :
    QuotientRankAtLeast (o216SourceU_wc ⟨11, by omega⟩) 14 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 163 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 163) o71W_mono) 14 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 163) hP hQ o71W_mono 14
      orbit71_lb14_mono
  exact quotientRankAtLeast_mono step109wc216s11_contain hAct


private theorem step109wc216s12_QtInv :
    (codeMat 412 : Mat3).transpose⁻¹ = (codeMat 111 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 412 : Mat3).transpose * (codeMat 111 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc216s12_contain :
    (o216SourceU_wc ⟨12, by omega⟩) ≤ actionW (codeMat 123) (codeMat 412) o84W_wc := by
  change spanCodes [274, 132, 84, 52, 10, 1] ≤ actionW (codeMat 123) (codeMat 412) o84W_wc
  apply step109wc216_spanCodes_le_of_gens [274, 132, 84, 52, 10, 1]
    (actionW (codeMat 123) (codeMat 412) o84W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 43 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 43 (by decide)
    have hact : actionA (codeMat 123) (codeMat 412) (codeMat 43) = codeMat 274 := by
      unfold actionA
      rw [step109wc216s12_QtInv]
      show (codeMat 123 : Mat3).transpose * codeMat 43 * (codeMat 111 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 374 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 374 (by decide)
    have hact : actionA (codeMat 123) (codeMat 412) (codeMat 374) = codeMat 132 := by
      unfold actionA
      rw [step109wc216s12_QtInv]
      show (codeMat 123 : Mat3).transpose * codeMat 374 * (codeMat 111 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 212 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 212 (by decide)
    have hact : actionA (codeMat 123) (codeMat 412) (codeMat 212) = codeMat 84 := by
      unfold actionA
      rw [step109wc216s12_QtInv]
      show (codeMat 123 : Mat3).transpose * codeMat 212 * (codeMat 111 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 387 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 387 (by decide)
    have hact : actionA (codeMat 123) (codeMat 412) (codeMat 387) = codeMat 52 := by
      unfold actionA
      rw [step109wc216s12_QtInv]
      show (codeMat 123 : Mat3).transpose * codeMat 387 * (codeMat 111 : Mat3).transpose = codeMat 52
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 258 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 258 (by decide)
    have hact : actionA (codeMat 123) (codeMat 412) (codeMat 258) = codeMat 10 := by
      unfold actionA
      rw [step109wc216s12_QtInv]
      show (codeMat 123 : Mat3).transpose * codeMat 258 * (codeMat 111 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 123) (codeMat 412) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc216s12_QtInv]
      show (codeMat 123 : Mat3).transpose * codeMat 128 * (codeMat 111 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact

theorem step109wc216s12Dispatch :
    QuotientRankAtLeast (o216SourceU_wc ⟨12, by omega⟩) 14 := by
  have hP : Invertible (codeMat 123 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 412 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 123) (codeMat 412) o84W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 123) (codeMat 412) hP hQ o84W_wc 14
      step109_orbit84_lb14_wc
  exact quotientRankAtLeast_mono step109wc216s12_contain hAct


private theorem step109wc216s13_QtInv :
    (codeMat 485 : Mat3).transpose⁻¹ = (codeMat 171 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 485 : Mat3).transpose * (codeMat 171 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc216s13_contain :
    (o216SourceU_wc ⟨13, by omega⟩) ≤ actionW (codeMat 214) (codeMat 485) o79W_wc := by
  change spanCodes [272, 132, 86, 54, 10, 1] ≤ actionW (codeMat 214) (codeMat 485) o79W_wc
  apply step109wc216_spanCodes_le_of_gens [272, 132, 86, 54, 10, 1]
    (actionW (codeMat 214) (codeMat 485) o79W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 31 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 31 (by decide)
    have hact : actionA (codeMat 214) (codeMat 485) (codeMat 31) = codeMat 272 := by
      unfold actionA
      rw [step109wc216s13_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 31 * (codeMat 171 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 476 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 476 (by decide)
    have hact : actionA (codeMat 214) (codeMat 485) (codeMat 476) = codeMat 132 := by
      unfold actionA
      rw [step109wc216s13_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 476 * (codeMat 171 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 213 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 213 (by decide)
    have hact : actionA (codeMat 214) (codeMat 485) (codeMat 213) = codeMat 86 := by
      unfold actionA
      rw [step109wc216s13_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 213 * (codeMat 171 : Mat3).transpose = codeMat 86
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 192 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 192 (by decide)
    have hact : actionA (codeMat 214) (codeMat 485) (codeMat 192) = codeMat 54 := by
      unfold actionA
      rw [step109wc216s13_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 192 * (codeMat 171 : Mat3).transpose = codeMat 54
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 264 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 264 (by decide)
    have hact : actionA (codeMat 214) (codeMat 485) (codeMat 264) = codeMat 10 := by
      unfold actionA
      rw [step109wc216s13_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 264 * (codeMat 171 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 360 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 360 (by decide)
    have hact : actionA (codeMat 214) (codeMat 485) (codeMat 360) = codeMat 1 := by
      unfold actionA
      rw [step109wc216s13_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 360 * (codeMat 171 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact

theorem step109wc216s13Dispatch :
    QuotientRankAtLeast (o216SourceU_wc ⟨13, by omega⟩) 14 := by
  have hP : Invertible (codeMat 214 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 485 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 214) (codeMat 485) o79W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 214) (codeMat 485) hP hQ o79W_wc 14
      step109_orbit79_lb14_wc
  exact quotientRankAtLeast_mono step109wc216s13_contain hAct


private theorem step109wc216s14_QtInv :
    (codeMat 277 : Mat3).transpose⁻¹ = (codeMat 277 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 277 : Mat3).transpose * (codeMat 277 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc216s14_contain :
    (o216SourceU_wc ⟨14, by omega⟩) ≤ actionW (codeMat 337) (codeMat 277) o49W_mono := by
  change spanCodes [292, 132, 96, 8, 2, 1] ≤ actionW (codeMat 337) (codeMat 277) o49W_mono
  apply step109wc216_spanCodes_le_of_gens [292, 132, 96, 8, 2, 1]
    (actionW (codeMat 337) (codeMat 277) o49W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 360 ∈ o49W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 96, 8, 2, 1] 360 (by decide)
    have hact : actionA (codeMat 337) (codeMat 277) (codeMat 360) = codeMat 292 := by
      unfold actionA
      rw [step109wc216s14_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 360 * (codeMat 277 : Mat3).transpose = codeMat 292
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 135 ∈ o49W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 96, 8, 2, 1] 135 (by decide)
    have hact : actionA (codeMat 337) (codeMat 277) (codeMat 135) = codeMat 132 := by
      unfold actionA
      rw [step109wc216s14_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 135 * (codeMat 277 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 105 ∈ o49W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 96, 8, 2, 1] 105 (by decide)
    have hact : actionA (codeMat 337) (codeMat 277) (codeMat 105) = codeMat 96 := by
      unfold actionA
      rw [step109wc216s14_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 105 * (codeMat 277 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ o49W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 96, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 337) (codeMat 277) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc216s14_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 8 * (codeMat 277 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o49W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 96, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 337) (codeMat 277) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc216s14_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 2 * (codeMat 277 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o49W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 96, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 337) (codeMat 277) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc216s14_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 1 * (codeMat 277 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc216_codeMat_mem_actionW_of_witness hw hact

theorem step109wc216s14Dispatch :
    QuotientRankAtLeast (o216SourceU_wc ⟨14, by omega⟩) 12 := by
  have hP : Invertible (codeMat 337 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 277 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 337) (codeMat 277) o49W_mono) 12 :=
    @quotientRankAtLeast_action (codeMat 337) (codeMat 277) hP hQ o49W_mono 12
      orbit49_lb12_mono
  exact quotientRankAtLeast_mono step109wc216s14_contain hAct

theorem step109wc216_all_dispatch (i : Fin 15) :
    QuotientRankAtLeast (o216SourceU_wc i) (o216SourceLb_wc i) := by
  fin_cases i
  · exact step109wc216s0Dispatch
  · exact step109wc216s1Dispatch
  · exact step109wc216s2Dispatch
  · exact step109wc216s3Dispatch
  · exact step109wc216s4Dispatch
  · exact step109wc216s5Dispatch
  · exact step109wc216s6Dispatch
  · exact step109wc216s7Dispatch
  · exact step109wc216s8Dispatch
  · exact step109wc216s9Dispatch
  · exact step109wc216s10Dispatch
  · exact step109wc216s11Dispatch
  · exact step109wc216s12Dispatch
  · exact step109wc216s13Dispatch
  · exact step109wc216s14Dispatch

theorem step109_orbit216_lb16_wc : QuotientRankAtLeast o216W_wc 16 :=
  o216Lb16_wc step109wc216_all_dispatch

end QiushiMatmul
