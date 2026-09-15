import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit146Consumer
import QiushiStep99Orbit56Dispatch
import QiushiOrbit10FP
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc146_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc146_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc146s0_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = (codeMat 305 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * (codeMat 305 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc146s0_contain :
    (o146SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 465) (codeMat 305) o56W := by
  change spanCodes [276, 160, 84, 12, 2, 1] ≤ actionW (codeMat 465) (codeMat 305) o56W
  apply step109wc146_spanCodes_le_of_gens [276, 160, 84, 12, 2, 1]
    (actionW (codeMat 465) (codeMat 305) o56W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 416 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 416 (by decide)
    have hact : actionA (codeMat 465) (codeMat 305) (codeMat 416) = codeMat 276 := by
      unfold actionA
      rw [step109wc146s0_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 416 * (codeMat 305 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 162 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 162 (by decide)
    have hact : actionA (codeMat 465) (codeMat 305) (codeMat 162) = codeMat 160 := by
      unfold actionA
      rw [step109wc146s0_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 162 * (codeMat 305 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 95 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 95 (by decide)
    have hact : actionA (codeMat 465) (codeMat 305) (codeMat 95) = codeMat 84 := by
      unfold actionA
      rw [step109wc146s0_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 95 * (codeMat 305 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 14 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 14 (by decide)
    have hact : actionA (codeMat 465) (codeMat 305) (codeMat 14) = codeMat 12 := by
      unfold actionA
      rw [step109wc146s0_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 14 * (codeMat 305 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 465) (codeMat 305) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc146s0_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 2 * (codeMat 305 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 465) (codeMat 305) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc146s0_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 1 * (codeMat 305 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact

theorem step109wc146s0Dispatch :
    QuotientRankAtLeast (o146SourceU_wc ⟨0, by omega⟩) 14 := by
  have hP : Invertible (codeMat 465 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 465) (codeMat 305) o56W) 14 :=
    @quotientRankAtLeast_action (codeMat 465) (codeMat 305) hP hQ o56W 14
      step99_orbit56_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc146s0_contain hAct


private theorem step109wc146s1_QtInv :
    (codeMat 267 : Mat3).transpose⁻¹ = (codeMat 282 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 267 : Mat3).transpose * (codeMat 282 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc146s1_contain :
    (o146SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 225) (codeMat 267) o56W := by
  change spanCodes [280, 132, 84, 36, 2, 1] ≤ actionW (codeMat 225) (codeMat 267) o56W
  apply step109wc146_spanCodes_le_of_gens [280, 132, 84, 36, 2, 1]
    (actionW (codeMat 225) (codeMat 267) o56W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 162 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 162 (by decide)
    have hact : actionA (codeMat 225) (codeMat 267) (codeMat 162) = codeMat 280 := by
      unfold actionA
      rw [step109wc146s1_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 162 * (codeMat 282 : Mat3).transpose = codeMat 280
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 12 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 225) (codeMat 267) (codeMat 12) = codeMat 132 := by
      unfold actionA
      rw [step109wc146s1_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 12 * (codeMat 282 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 93 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 93 (by decide)
    have hact : actionA (codeMat 225) (codeMat 267) (codeMat 93) = codeMat 84 := by
      unfold actionA
      rw [step109wc146s1_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 93 * (codeMat 282 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 225) (codeMat 267) (codeMat 256) = codeMat 36 := by
      unfold actionA
      rw [step109wc146s1_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 256 * (codeMat 282 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 267) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step109wc146s1_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * (codeMat 282 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 225) (codeMat 267) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step109wc146s1_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 3 * (codeMat 282 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact

theorem step109wc146s1Dispatch :
    QuotientRankAtLeast (o146SourceU_wc ⟨1, by omega⟩) 14 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 267) o56W) 14 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 267) hP hQ o56W 14
      step99_orbit56_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc146s1_contain hAct


private theorem step109wc146s2_QtInv :
    (codeMat 286 : Mat3).transpose⁻¹ = (codeMat 303 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 286 : Mat3).transpose * (codeMat 303 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc146s2_contain :
    (o146SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 369) (codeMat 286) o56W := by
  change spanCodes [280, 136, 84, 40, 2, 1] ≤ actionW (codeMat 369) (codeMat 286) o56W
  apply step109wc146_spanCodes_le_of_gens [280, 136, 84, 40, 2, 1]
    (actionW (codeMat 369) (codeMat 286) o56W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 268 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 268 (by decide)
    have hact : actionA (codeMat 369) (codeMat 286) (codeMat 268) = codeMat 280 := by
      unfold actionA
      rw [step109wc146s2_QtInv]
      show (codeMat 369 : Mat3).transpose * codeMat 268 * (codeMat 303 : Mat3).transpose = codeMat 280
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 81 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 81 (by decide)
    have hact : actionA (codeMat 369) (codeMat 286) (codeMat 81) = codeMat 136 := by
      unfold actionA
      rw [step109wc146s2_QtInv]
      show (codeMat 369 : Mat3).transpose * codeMat 81 * (codeMat 303 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 92 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 92 (by decide)
    have hact : actionA (codeMat 369) (codeMat 286) (codeMat 92) = codeMat 84 := by
      unfold actionA
      rw [step109wc146s2_QtInv]
      show (codeMat 369 : Mat3).transpose * codeMat 92 * (codeMat 303 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 511 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 511 (by decide)
    have hact : actionA (codeMat 369) (codeMat 286) (codeMat 511) = codeMat 40 := by
      unfold actionA
      rw [step109wc146s2_QtInv]
      show (codeMat 369 : Mat3).transpose * codeMat 511 * (codeMat 303 : Mat3).transpose = codeMat 40
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 369) (codeMat 286) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc146s2_QtInv]
      show (codeMat 369 : Mat3).transpose * codeMat 3 * (codeMat 303 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 369) (codeMat 286) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc146s2_QtInv]
      show (codeMat 369 : Mat3).transpose * codeMat 2 * (codeMat 303 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact

theorem step109wc146s2Dispatch :
    QuotientRankAtLeast (o146SourceU_wc ⟨2, by omega⟩) 14 := by
  have hP : Invertible (codeMat 369 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 286 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 369) (codeMat 286) o56W) 14 :=
    @quotientRankAtLeast_action (codeMat 369) (codeMat 286) hP hQ o56W 14
      step99_orbit56_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc146s2_contain hAct


private theorem step109wc146s3_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc146s3_contain :
    (o146SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 266) (codeMat 266) orbit10W := by
  change spanCodes [256, 160, 68, 16, 8, 2, 1] ≤ actionW (codeMat 266) (codeMat 266) orbit10W
  apply step109wc146_spanCodes_le_of_gens [256, 160, 68, 16, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 266) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step109wc146s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 256 * (codeMat 266 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 68) = codeMat 160 := by
      unfold actionA
      rw [step109wc146s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 68 * (codeMat 266 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 160) = codeMat 68 := by
      unfold actionA
      rw [step109wc146s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 160 * (codeMat 266 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc146s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 2) = codeMat 8 := by
      unfold actionA
      rw [step109wc146s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 8) = codeMat 2 := by
      unfold actionA
      rw [step109wc146s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc146s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact

theorem step109wc146s3Dispatch :
    QuotientRankAtLeast (o146SourceU_wc ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 266) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 266) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc146s3_contain hAct


private theorem step109wc146s4_QtInv :
    (codeMat 311 : Mat3).transpose⁻¹ = (codeMat 307 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 311 : Mat3).transpose * (codeMat 307 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc146s4_contain :
    (o146SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 142) (codeMat 311) orbit10W := by
  change spanCodes [260, 140, 72, 44, 28, 2, 1] ≤ actionW (codeMat 142) (codeMat 311) orbit10W
  apply step109wc146_spanCodes_le_of_gens [260, 140, 72, 44, 28, 2, 1]
    (actionW (codeMat 142) (codeMat 311) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 511 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 511 (by decide)
    have hact : actionA (codeMat 142) (codeMat 311) (codeMat 511) = codeMat 260 := by
      unfold actionA
      rw [step109wc146s4_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 511 * (codeMat 307 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 187 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 187 (by decide)
    have hact : actionA (codeMat 142) (codeMat 311) (codeMat 187) = codeMat 140 := by
      unfold actionA
      rw [step109wc146s4_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 187 * (codeMat 307 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 142) (codeMat 311) (codeMat 1) = codeMat 72 := by
      unfold actionA
      rw [step109wc146s4_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 1 * (codeMat 307 : Mat3).transpose = codeMat 72
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 440 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 440 (by decide)
    have hact : actionA (codeMat 142) (codeMat 311) (codeMat 440) = codeMat 44 := by
      unfold actionA
      rw [step109wc146s4_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 440 * (codeMat 307 : Mat3).transpose = codeMat 44
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 184 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 184 (by decide)
    have hact : actionA (codeMat 142) (codeMat 311) (codeMat 184) = codeMat 28 := by
      unfold actionA
      rw [step109wc146s4_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 184 * (codeMat 307 : Mat3).transpose = codeMat 28
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 142) (codeMat 311) (codeMat 24) = codeMat 2 := by
      unfold actionA
      rw [step109wc146s4_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 24 * (codeMat 307 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 142) (codeMat 311) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc146s4_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 8 * (codeMat 307 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact

theorem step109wc146s4Dispatch :
    QuotientRankAtLeast (o146SourceU_wc ⟨4, by omega⟩) 12 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 311 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 311) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 311) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc146s4_contain hAct


private theorem step109wc146s5_QtInv :
    (codeMat 281 : Mat3).transpose⁻¹ = (codeMat 281 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 281 : Mat3).transpose * (codeMat 281 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc146s5_contain :
    (o146SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 140) (codeMat 281) orbit10W := by
  change spanCodes [268, 128, 64, 32, 20, 2, 1] ≤ actionW (codeMat 140) (codeMat 281) orbit10W
  apply step109wc146_spanCodes_le_of_gens [268, 128, 64, 32, 20, 2, 1]
    (actionW (codeMat 140) (codeMat 281) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 228 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 228 (by decide)
    have hact : actionA (codeMat 140) (codeMat 281) (codeMat 228) = codeMat 268 := by
      unfold actionA
      rw [step109wc146s5_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 228 * (codeMat 281 : Mat3).transpose = codeMat 268
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 281) (codeMat 2) = codeMat 128 := by
      unfold actionA
      rw [step109wc146s5_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 281 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 3 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 140) (codeMat 281) (codeMat 3) = codeMat 64 := by
      unfold actionA
      rw [step109wc146s5_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 3 * (codeMat 281 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 140) (codeMat 281) (codeMat 256) = codeMat 32 := by
      unfold actionA
      rw [step109wc146s5_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 256 * (codeMat 281 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 140) (codeMat 281) (codeMat 160) = codeMat 20 := by
      unfold actionA
      rw [step109wc146s5_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 160 * (codeMat 281 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 140) (codeMat 281) (codeMat 16) = codeMat 2 := by
      unfold actionA
      rw [step109wc146s5_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 16 * (codeMat 281 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 140) (codeMat 281) (codeMat 24) = codeMat 1 := by
      unfold actionA
      rw [step109wc146s5_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 24 * (codeMat 281 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact

theorem step109wc146s5Dispatch :
    QuotientRankAtLeast (o146SourceU_wc ⟨5, by omega⟩) 12 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 281) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 281) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc146s5_contain hAct


private theorem step109wc146s6_QtInv :
    (codeMat 501 : Mat3).transpose⁻¹ = (codeMat 494 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 501 : Mat3).transpose * (codeMat 494 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc146s6_contain :
    (o146SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 161) (codeMat 501) flatW_9 := by
  change spanCodes [280, 152, 80, 56, 4, 2, 1] ≤ actionW (codeMat 161) (codeMat 501) flatW_9
  apply step109wc146_spanCodes_le_of_gens [280, 152, 80, 56, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 501) flatW_9)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 248 ∈ flatW_9 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 8, 4, 2, 1] 248 (by decide)
    have hact : actionA (codeMat 161) (codeMat 501) (codeMat 248) = codeMat 280 := by
      unfold actionA
      rw [step109wc146s6_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 248 * (codeMat 494 : Mat3).transpose = codeMat 280
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 240 ∈ flatW_9 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 8, 4, 2, 1] 240 (by decide)
    have hact : actionA (codeMat 161) (codeMat 501) (codeMat 240) = codeMat 152 := by
      unfold actionA
      rw [step109wc146s6_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 240 * (codeMat 494 : Mat3).transpose = codeMat 152
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 424 ∈ flatW_9 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 8, 4, 2, 1] 424 (by decide)
    have hact : actionA (codeMat 161) (codeMat 501) (codeMat 424) = codeMat 80 := by
      unfold actionA
      rw [step109wc146s6_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 424 * (codeMat 494 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ flatW_9 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 501) (codeMat 256) = codeMat 56 := by
      unfold actionA
      rw [step109wc146s6_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 494 : Mat3).transpose = codeMat 56
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 7 ∈ flatW_9 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 8, 4, 2, 1] 7 (by decide)
    have hact : actionA (codeMat 161) (codeMat 501) (codeMat 7) = codeMat 4 := by
      unfold actionA
      rw [step109wc146s6_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 7 * (codeMat 494 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 6 ∈ flatW_9 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 8, 4, 2, 1] 6 (by decide)
    have hact : actionA (codeMat 161) (codeMat 501) (codeMat 6) = codeMat 2 := by
      unfold actionA
      rw [step109wc146s6_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 6 * (codeMat 494 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 5 ∈ flatW_9 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 8, 4, 2, 1] 5 (by decide)
    have hact : actionA (codeMat 161) (codeMat 501) (codeMat 5) = codeMat 1 := by
      unfold actionA
      rw [step109wc146s6_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 5 * (codeMat 494 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc146_codeMat_mem_actionW_of_witness hw hact

theorem step109wc146s6Dispatch :
    QuotientRankAtLeast (o146SourceU_wc ⟨6, by omega⟩) 9 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 501 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 501) flatW_9) 9 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 501) hP hQ flatW_9 9
      flatSeed_9
  exact quotientRankAtLeast_mono step109wc146s6_contain hAct

theorem step109wc146_all_dispatch (i : Fin 7) :
    QuotientRankAtLeast (o146SourceU_wc i) (o146SourceLb_wc i) := by
  fin_cases i
  · exact step109wc146s0Dispatch
  · exact step109wc146s1Dispatch
  · exact step109wc146s2Dispatch
  · exact step109wc146s3Dispatch
  · exact step109wc146s4Dispatch
  · exact step109wc146s5Dispatch
  · exact step109wc146s6Dispatch

theorem step109_orbit146_lb15_wc : QuotientRankAtLeast o146W_wc 15 :=
  o146Lb15_wc step109wc146_all_dispatch

end QiushiMatmul
