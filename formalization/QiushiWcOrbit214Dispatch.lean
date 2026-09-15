import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit214Consumer
import QiushiStep99Orbit77Dispatch
import QiushiStep99Orbit56Dispatch
import QiushiOrbit10FP
import QiushiOrbit14FP

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc214_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc214_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

private def step109wc214s0SrcT : Submodule F2 Mat3 := spanCodes [272, 132, 80, 32, 10, 1]

private theorem step109wc214s0SrcT_lb : QuotientRankAtLeast step109wc214s0SrcT 15 := by
  have ht := quotientRankAtLeast_transpose step99_orbit77_lb15_unconditional
  have hle : step109wc214s0SrcT ≤ transposeW o77W := by
    unfold step109wc214s0SrcT transposeW
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

private theorem step109wc214s0_QtInv :
    (codeMat 499 : Mat3).transpose⁻¹ = (codeMat 382 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 499 : Mat3).transpose * (codeMat 382 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc214s0_contain :
    (o214SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 114) (codeMat 499) step109wc214s0SrcT := by
  change spanCodes [278, 132, 80, 48, 10, 1] ≤ actionW (codeMat 114) (codeMat 499) step109wc214s0SrcT
  apply step109wc214_spanCodes_le_of_gens [278, 132, 80, 48, 10, 1]
    (actionW (codeMat 114) (codeMat 499) step109wc214s0SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 113 ∈ step109wc214s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 113 (by decide)
    have hact : actionA (codeMat 114) (codeMat 499) (codeMat 113) = codeMat 278 := by
      unfold actionA
      rw [step109wc214s0_QtInv]
      show (codeMat 114 : Mat3).transpose * codeMat 113 * (codeMat 382 : Mat3).transpose = codeMat 278
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 447 ∈ step109wc214s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 447 (by decide)
    have hact : actionA (codeMat 114) (codeMat 499) (codeMat 447) = codeMat 132 := by
      unfold actionA
      rw [step109wc214s0_QtInv]
      show (codeMat 114 : Mat3).transpose * codeMat 447 * (codeMat 382 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 42 ∈ step109wc214s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 42 (by decide)
    have hact : actionA (codeMat 114) (codeMat 499) (codeMat 42) = codeMat 80 := by
      unfold actionA
      rw [step109wc214s0_QtInv]
      show (codeMat 114 : Mat3).transpose * codeMat 42 * (codeMat 382 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ step109wc214s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 114) (codeMat 499) (codeMat 1) = codeMat 48 := by
      unfold actionA
      rw [step109wc214s0_QtInv]
      show (codeMat 114 : Mat3).transpose * codeMat 1 * (codeMat 382 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 453 ∈ step109wc214s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 453 (by decide)
    have hact : actionA (codeMat 114) (codeMat 499) (codeMat 453) = codeMat 10 := by
      unfold actionA
      rw [step109wc214s0_QtInv]
      show (codeMat 114 : Mat3).transpose * codeMat 453 * (codeMat 382 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 320 ∈ step109wc214s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 320 (by decide)
    have hact : actionA (codeMat 114) (codeMat 499) (codeMat 320) = codeMat 1 := by
      unfold actionA
      rw [step109wc214s0_QtInv]
      show (codeMat 114 : Mat3).transpose * codeMat 320 * (codeMat 382 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact

theorem step109wc214s0Dispatch :
    QuotientRankAtLeast (o214SourceU_wc ⟨0, by omega⟩) 15 := by
  have hP : Invertible (codeMat 114 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 499 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 114) (codeMat 499) step109wc214s0SrcT) 15 :=
    @quotientRankAtLeast_action (codeMat 114) (codeMat 499) hP hQ step109wc214s0SrcT 15
      step109wc214s0SrcT_lb
  exact quotientRankAtLeast_mono step109wc214s0_contain hAct


private theorem step109wc214s1_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc214s1_contain :
    (o214SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 281) (codeMat 161) o56W := by
  change spanCodes [274, 128, 96, 10, 4, 1] ≤ actionW (codeMat 281) (codeMat 161) o56W
  apply step109wc214_spanCodes_le_of_gens [274, 128, 96, 10, 4, 1]
    (actionW (codeMat 281) (codeMat 161) o56W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 160 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 281) (codeMat 161) (codeMat 160) = codeMat 274 := by
      unfold actionA
      rw [step109wc214s1_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 160 * (codeMat 161 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 281) (codeMat 161) (codeMat 256) = codeMat 128 := by
      unfold actionA
      rw [step109wc214s1_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 256 * (codeMat 161 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 82 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 82 (by decide)
    have hact : actionA (codeMat 281) (codeMat 161) (codeMat 82) = codeMat 96 := by
      unfold actionA
      rw [step109wc214s1_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 82 * (codeMat 161 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 13 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 13 (by decide)
    have hact : actionA (codeMat 281) (codeMat 161) (codeMat 13) = codeMat 10 := by
      unfold actionA
      rw [step109wc214s1_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 13 * (codeMat 161 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 281) (codeMat 161) (codeMat 2) = codeMat 4 := by
      unfold actionA
      rw [step109wc214s1_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 281) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc214s1_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact

theorem step109wc214s1Dispatch :
    QuotientRankAtLeast (o214SourceU_wc ⟨1, by omega⟩) 14 := by
  have hP : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 281) (codeMat 161) o56W) 14 :=
    @quotientRankAtLeast_action (codeMat 281) (codeMat 161) hP hQ o56W 14
      step99_orbit56_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc214s1_contain hAct

private def step109wc214s2SrcT : Submodule F2 Mat3 := spanCodes [256, 160, 66, 20, 8, 1]

private theorem step109wc214s2SrcT_lb : QuotientRankAtLeast step109wc214s2SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step99_orbit56_lb14_unconditional
  have hle : step109wc214s2SrcT ≤ transposeW o56W := by
    unfold step109wc214s2SrcT transposeW
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

private theorem step109wc214s2_QtInv :
    (codeMat 351 : Mat3).transpose⁻¹ = (codeMat 239 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 351 : Mat3).transpose * (codeMat 239 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc214s2_contain :
    (o214SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 477) (codeMat 351) step109wc214s2SrcT := by
  change spanCodes [278, 132, 84, 52, 10, 1] ≤ actionW (codeMat 477) (codeMat 351) step109wc214s2SrcT
  apply step109wc214_spanCodes_le_of_gens [278, 132, 84, 52, 10, 1]
    (actionW (codeMat 477) (codeMat 351) step109wc214s2SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 29 ∈ step109wc214s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 29 (by decide)
    have hact : actionA (codeMat 477) (codeMat 351) (codeMat 29) = codeMat 278 := by
      unfold actionA
      rw [step109wc214s2_QtInv]
      show (codeMat 477 : Mat3).transpose * codeMat 29 * (codeMat 239 : Mat3).transpose = codeMat 278
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 437 ∈ step109wc214s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 437 (by decide)
    have hact : actionA (codeMat 477) (codeMat 351) (codeMat 437) = codeMat 132 := by
      unfold actionA
      rw [step109wc214s2_QtInv]
      show (codeMat 477 : Mat3).transpose * codeMat 437 * (codeMat 239 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 86 ∈ step109wc214s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 86 (by decide)
    have hact : actionA (codeMat 477) (codeMat 351) (codeMat 86) = codeMat 84 := by
      unfold actionA
      rw [step109wc214s2_QtInv]
      show (codeMat 477 : Mat3).transpose * codeMat 86 * (codeMat 239 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 235 ∈ step109wc214s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 235 (by decide)
    have hact : actionA (codeMat 477) (codeMat 351) (codeMat 235) = codeMat 52 := by
      unfold actionA
      rw [step109wc214s2_QtInv]
      show (codeMat 477 : Mat3).transpose * codeMat 235 * (codeMat 239 : Mat3).transpose = codeMat 52
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 284 ∈ step109wc214s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 284 (by decide)
    have hact : actionA (codeMat 477) (codeMat 351) (codeMat 284) = codeMat 10 := by
      unfold actionA
      rw [step109wc214s2_QtInv]
      show (codeMat 477 : Mat3).transpose * codeMat 284 * (codeMat 239 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 511 ∈ step109wc214s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 511 (by decide)
    have hact : actionA (codeMat 477) (codeMat 351) (codeMat 511) = codeMat 1 := by
      unfold actionA
      rw [step109wc214s2_QtInv]
      show (codeMat 477 : Mat3).transpose * codeMat 511 * (codeMat 239 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact

theorem step109wc214s2Dispatch :
    QuotientRankAtLeast (o214SourceU_wc ⟨2, by omega⟩) 14 := by
  have hP : Invertible (codeMat 477 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 351 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 477) (codeMat 351) step109wc214s2SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 477) (codeMat 351) hP hQ step109wc214s2SrcT 14
      step109wc214s2SrcT_lb
  exact quotientRankAtLeast_mono step109wc214s2_contain hAct


private theorem step109wc214s3_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = (codeMat 305 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * (codeMat 305 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc214s3_contain :
    (o214SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 266) (codeMat 305) orbit10W := by
  change spanCodes [260, 132, 96, 16, 8, 2, 1] ≤ actionW (codeMat 266) (codeMat 305) orbit10W
  apply step109wc214_spanCodes_le_of_gens [260, 132, 96, 16, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 305) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 432 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide)
    have hact : actionA (codeMat 266) (codeMat 305) (codeMat 432) = codeMat 260 := by
      unfold actionA
      rw [step109wc214s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 432 * (codeMat 305 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 176 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 176 (by decide)
    have hact : actionA (codeMat 266) (codeMat 305) (codeMat 176) = codeMat 132 := by
      unfold actionA
      rw [step109wc214s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 176 * (codeMat 305 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 70 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 70 (by decide)
    have hact : actionA (codeMat 266) (codeMat 305) (codeMat 70) = codeMat 96 := by
      unfold actionA
      rw [step109wc214s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 70 * (codeMat 305 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 305) (codeMat 2) = codeMat 16 := by
      unfold actionA
      rw [step109wc214s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 305 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 305) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step109wc214s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 305 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 305) (codeMat 16) = codeMat 2 := by
      unfold actionA
      rw [step109wc214s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 305 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 305) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc214s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 305 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact

theorem step109wc214s3Dispatch :
    QuotientRankAtLeast (o214SourceU_wc ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 305) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 305) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc214s3_contain hAct


private theorem step109wc214s4_QtInv :
    (codeMat 442 : Mat3).transpose⁻¹ = (codeMat 334 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 442 : Mat3).transpose * (codeMat 334 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc214s4_contain :
    (o214SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 142) (codeMat 442) orbit10W := by
  change spanCodes [272, 130, 66, 34, 10, 6, 1] ≤ actionW (codeMat 142) (codeMat 442) orbit10W
  apply step109wc214_spanCodes_le_of_gens [272, 130, 66, 34, 10, 6, 1]
    (actionW (codeMat 142) (codeMat 442) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 70 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 70 (by decide)
    have hact : actionA (codeMat 142) (codeMat 442) (codeMat 70) = codeMat 272 := by
      unfold actionA
      rw [step109wc214s4_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 70 * (codeMat 334 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 511 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 511 (by decide)
    have hact : actionA (codeMat 142) (codeMat 442) (codeMat 511) = codeMat 130 := by
      unfold actionA
      rw [step109wc214s4_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 511 * (codeMat 334 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 186 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 186 (by decide)
    have hact : actionA (codeMat 142) (codeMat 442) (codeMat 186) = codeMat 66 := by
      unfold actionA
      rw [step109wc214s4_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 186 * (codeMat 334 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 440 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 440 (by decide)
    have hact : actionA (codeMat 142) (codeMat 442) (codeMat 440) = codeMat 34 := by
      unfold actionA
      rw [step109wc214s4_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 440 * (codeMat 334 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 184 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 184 (by decide)
    have hact : actionA (codeMat 142) (codeMat 442) (codeMat 184) = codeMat 10 := by
      unfold actionA
      rw [step109wc214s4_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 184 * (codeMat 334 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 142) (codeMat 442) (codeMat 8) = codeMat 6 := by
      unfold actionA
      rw [step109wc214s4_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 8 * (codeMat 334 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 142) (codeMat 442) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc214s4_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 16 * (codeMat 334 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact

theorem step109wc214s4Dispatch :
    QuotientRankAtLeast (o214SourceU_wc ⟨4, by omega⟩) 12 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 442 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 442) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 442) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc214s4_contain hAct


private theorem step109wc214s5_QtInv :
    (codeMat 351 : Mat3).transpose⁻¹ = (codeMat 239 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 351 : Mat3).transpose * (codeMat 239 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc214s5_contain :
    (o214SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 342) (codeMat 351) orbit14W := by
  change spanCodes [258, 132, 70, 38, 20, 10, 1] ≤ actionW (codeMat 342) (codeMat 351) orbit14W
  apply step109wc214_spanCodes_le_of_gens [258, 132, 70, 38, 20, 10, 1]
    (actionW (codeMat 342) (codeMat 351) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 246 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 246 (by decide)
    have hact : actionA (codeMat 342) (codeMat 351) (codeMat 246) = codeMat 258 := by
      unfold actionA
      rw [step109wc214s5_QtInv]
      show (codeMat 342 : Mat3).transpose * codeMat 246 * (codeMat 239 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 374 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 374 (by decide)
    have hact : actionA (codeMat 342) (codeMat 351) (codeMat 374) = codeMat 132 := by
      unfold actionA
      rw [step109wc214s5_QtInv]
      show (codeMat 342 : Mat3).transpose * codeMat 374 * (codeMat 239 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 393 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 393 (by decide)
    have hact : actionA (codeMat 342) (codeMat 351) (codeMat 393) = codeMat 70 := by
      unfold actionA
      rw [step109wc214s5_QtInv]
      show (codeMat 342 : Mat3).transpose * codeMat 393 * (codeMat 239 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 414 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 414 (by decide)
    have hact : actionA (codeMat 342) (codeMat 351) (codeMat 414) = codeMat 38 := by
      unfold actionA
      rw [step109wc214s5_QtInv]
      show (codeMat 342 : Mat3).transpose * codeMat 414 * (codeMat 239 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 373 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 373 (by decide)
    have hact : actionA (codeMat 342) (codeMat 351) (codeMat 373) = codeMat 20 := by
      unfold actionA
      rw [step109wc214s5_QtInv]
      show (codeMat 342 : Mat3).transpose * codeMat 373 * (codeMat 239 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 227 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 227 (by decide)
    have hact : actionA (codeMat 342) (codeMat 351) (codeMat 227) = codeMat 10 := by
      unfold actionA
      rw [step109wc214s5_QtInv]
      show (codeMat 342 : Mat3).transpose * codeMat 227 * (codeMat 239 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 511 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 511 (by decide)
    have hact : actionA (codeMat 342) (codeMat 351) (codeMat 511) = codeMat 1 := by
      unfold actionA
      rw [step109wc214s5_QtInv]
      show (codeMat 342 : Mat3).transpose * codeMat 511 * (codeMat 239 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact

theorem step109wc214s5Dispatch :
    QuotientRankAtLeast (o214SourceU_wc ⟨5, by omega⟩) 12 := by
  have hP : Invertible (codeMat 342 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 351 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 342) (codeMat 351) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 342) (codeMat 351) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc214s5_contain hAct


private theorem step109wc214s6_QtInv :
    (codeMat 163 : Mat3).transpose⁻¹ = (codeMat 165 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 163 : Mat3).transpose * (codeMat 165 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc214s6_contain :
    (o214SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 396) (codeMat 163) orbit14W := by
  change spanCodes [256, 132, 64, 32, 22, 10, 1] ≤ actionW (codeMat 396) (codeMat 163) orbit14W
  apply step109wc214_spanCodes_le_of_gens [256, 132, 64, 32, 22, 10, 1]
    (actionW (codeMat 396) (codeMat 163) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 396) (codeMat 163) (codeMat 2) = codeMat 256 := by
      unfold actionA
      rw [step109wc214s6_QtInv]
      show (codeMat 396 : Mat3).transpose * codeMat 2 * (codeMat 165 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 21 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 21 (by decide)
    have hact : actionA (codeMat 396) (codeMat 163) (codeMat 21) = codeMat 132 := by
      unfold actionA
      rw [step109wc214s6_QtInv]
      show (codeMat 396 : Mat3).transpose * codeMat 21 * (codeMat 165 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 396) (codeMat 163) (codeMat 1) = codeMat 64 := by
      unfold actionA
      rw [step109wc214s6_QtInv]
      show (codeMat 396 : Mat3).transpose * codeMat 1 * (codeMat 165 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 130 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 130 (by decide)
    have hact : actionA (codeMat 396) (codeMat 163) (codeMat 130) = codeMat 32 := by
      unfold actionA
      rw [step109wc214s6_QtInv]
      show (codeMat 396 : Mat3).transpose * codeMat 130 * (codeMat 165 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 381 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 381 (by decide)
    have hact : actionA (codeMat 396) (codeMat 163) (codeMat 381) = codeMat 22 := by
      unfold actionA
      rw [step109wc214s6_QtInv]
      show (codeMat 396 : Mat3).transpose * codeMat 381 * (codeMat 165 : Mat3).transpose = codeMat 22
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 105 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 105 (by decide)
    have hact : actionA (codeMat 396) (codeMat 163) (codeMat 105) = codeMat 10 := by
      unfold actionA
      rw [step109wc214s6_QtInv]
      show (codeMat 396 : Mat3).transpose * codeMat 105 * (codeMat 165 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 396) (codeMat 163) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc214s6_QtInv]
      show (codeMat 396 : Mat3).transpose * codeMat 8 * (codeMat 165 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc214_codeMat_mem_actionW_of_witness hw hact

theorem step109wc214s6Dispatch :
    QuotientRankAtLeast (o214SourceU_wc ⟨6, by omega⟩) 12 := by
  have hP : Invertible (codeMat 396 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 163 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 396) (codeMat 163) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 396) (codeMat 163) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc214s6_contain hAct

theorem step109wc214_all_dispatch (i : Fin 7) :
    QuotientRankAtLeast (o214SourceU_wc i) (o214SourceLb_wc i) := by
  fin_cases i
  · exact step109wc214s0Dispatch
  · exact step109wc214s1Dispatch
  · exact step109wc214s2Dispatch
  · exact step109wc214s3Dispatch
  · exact step109wc214s4Dispatch
  · exact step109wc214s5Dispatch
  · exact step109wc214s6Dispatch

theorem step109_orbit214_lb16_wc : QuotientRankAtLeast o214W_wc 16 :=
  o214Lb16_wc step109wc214_all_dispatch

end QiushiMatmul
