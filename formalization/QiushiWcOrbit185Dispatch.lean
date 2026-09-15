import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit185Consumer
import QiushiStep99Orbit55Dispatch
import QiushiWcOrbit78Dispatch
import QiushiStep99Orbit56Dispatch
import QiushiWcOrbit83Dispatch
import QiushiOrbit41FP
import QiushiMonoOrbit39From13
import QiushiMonoOrbit44From14
import QiushiOrbit10FP
import QiushiOrbit14FP

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc185_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc185_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc185s0_QtInv :
    (codeMat 230 : Mat3).transpose⁻¹ = (codeMat 159 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 230 : Mat3).transpose * (codeMat 159 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc185s0_contain :
    (o185SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 330) (codeMat 230) o55W := by
  change spanCodes [386, 70, 32, 18, 10, 1] ≤ actionW (codeMat 330) (codeMat 230) o55W
  apply step109wc185_spanCodes_le_of_gens [386, 70, 32, 18, 10, 1]
    (actionW (codeMat 330) (codeMat 230) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 408 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 408 (by decide)
    have hact : actionA (codeMat 330) (codeMat 230) (codeMat 408) = codeMat 386 := by
      unfold actionA
      rw [step109wc185s0_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 408 * (codeMat 159 : Mat3).transpose = codeMat 386
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 272 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 272 (by decide)
    have hact : actionA (codeMat 330) (codeMat 230) (codeMat 272) = codeMat 70 := by
      unfold actionA
      rw [step109wc185s0_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 272 * (codeMat 159 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 3 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 330) (codeMat 230) (codeMat 3) = codeMat 32 := by
      unfold actionA
      rw [step109wc185s0_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 3 * (codeMat 159 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 45 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 45 (by decide)
    have hact : actionA (codeMat 330) (codeMat 230) (codeMat 45) = codeMat 18 := by
      unfold actionA
      rw [step109wc185s0_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 45 * (codeMat 159 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 44 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 44 (by decide)
    have hact : actionA (codeMat 330) (codeMat 230) (codeMat 44) = codeMat 10 := by
      unfold actionA
      rw [step109wc185s0_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 44 * (codeMat 159 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 330) (codeMat 230) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc185s0_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 32 * (codeMat 159 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact

theorem step109wc185s0Dispatch :
    QuotientRankAtLeast (o185SourceU_wc ⟨0, by omega⟩) 14 := by
  have hP : Invertible (codeMat 330 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 230 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 330) (codeMat 230) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 330) (codeMat 230) hP hQ o55W 14
      step99_orbit55_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc185s0_contain hAct

private def step109wc185s1SrcT : Submodule F2 Mat3 := spanCodes [272, 128, 66, 34, 8, 1]

private theorem step109wc185s1SrcT_lb : QuotientRankAtLeast step109wc185s1SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step99_orbit55_lb14_unconditional
  have hle : step109wc185s1SrcT ≤ transposeW o55W := by
    unfold step109wc185s1SrcT transposeW
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

private theorem step109wc185s1_QtInv :
    (codeMat 421 : Mat3).transpose⁻¹ = (codeMat 179 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 421 : Mat3).transpose * (codeMat 179 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc185s1_contain :
    (o185SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 205) (codeMat 421) step109wc185s1SrcT := by
  change spanCodes [388, 64, 32, 20, 10, 1] ≤ actionW (codeMat 205) (codeMat 421) step109wc185s1SrcT
  apply step109wc185_spanCodes_le_of_gens [388, 64, 32, 20, 10, 1]
    (actionW (codeMat 205) (codeMat 421) step109wc185s1SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 35 ∈ step109wc185s1SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 35 (by decide)
    have hact : actionA (codeMat 205) (codeMat 421) (codeMat 35) = codeMat 388 := by
      unfold actionA
      rw [step109wc185s1_QtInv]
      show (codeMat 205 : Mat3).transpose * codeMat 35 * (codeMat 179 : Mat3).transpose = codeMat 388
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 9 ∈ step109wc185s1SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 9 (by decide)
    have hact : actionA (codeMat 205) (codeMat 421) (codeMat 9) = codeMat 64 := by
      unfold actionA
      rw [step109wc185s1_QtInv]
      show (codeMat 205 : Mat3).transpose * codeMat 9 * (codeMat 179 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 504 ∈ step109wc185s1SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 504 (by decide)
    have hact : actionA (codeMat 205) (codeMat 421) (codeMat 504) = codeMat 32 := by
      unfold actionA
      rw [step109wc185s1_QtInv]
      show (codeMat 205 : Mat3).transpose * codeMat 504 * (codeMat 179 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 280 ∈ step109wc185s1SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 280 (by decide)
    have hact : actionA (codeMat 205) (codeMat 421) (codeMat 280) = codeMat 20 := by
      unfold actionA
      rw [step109wc185s1_QtInv]
      show (codeMat 205 : Mat3).transpose * codeMat 280 * (codeMat 179 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 104 ∈ step109wc185s1SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 104 (by decide)
    have hact : actionA (codeMat 205) (codeMat 421) (codeMat 104) = codeMat 10 := by
      unfold actionA
      rw [step109wc185s1_QtInv]
      show (codeMat 205 : Mat3).transpose * codeMat 104 * (codeMat 179 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ step109wc185s1SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 8 (by decide)
    have hact : actionA (codeMat 205) (codeMat 421) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc185s1_QtInv]
      show (codeMat 205 : Mat3).transpose * codeMat 8 * (codeMat 179 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact

theorem step109wc185s1Dispatch :
    QuotientRankAtLeast (o185SourceU_wc ⟨1, by omega⟩) 14 := by
  have hP : Invertible (codeMat 205 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 421 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 205) (codeMat 421) step109wc185s1SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 205) (codeMat 421) hP hQ step109wc185s1SrcT 14
      step109wc185s1SrcT_lb
  exact quotientRankAtLeast_mono step109wc185s1_contain hAct


private theorem step109wc185s2_QtInv :
    (codeMat 494 : Mat3).transpose⁻¹ = (codeMat 501 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 494 : Mat3).transpose * (codeMat 501 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc185s2_contain :
    (o185SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 423) (codeMat 494) o78W_wc := by
  change spanCodes [274, 130, 84, 32, 10, 1] ≤ actionW (codeMat 423) (codeMat 494) o78W_wc
  apply step109wc185_spanCodes_le_of_gens [274, 130, 84, 32, 10, 1]
    (actionW (codeMat 423) (codeMat 494) o78W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 21 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 21 (by decide)
    have hact : actionA (codeMat 423) (codeMat 494) (codeMat 21) = codeMat 274 := by
      unfold actionA
      rw [step109wc185s2_QtInv]
      show (codeMat 423 : Mat3).transpose * codeMat 21 * (codeMat 501 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 365 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 365 (by decide)
    have hact : actionA (codeMat 423) (codeMat 494) (codeMat 365) = codeMat 130 := by
      unfold actionA
      rw [step109wc185s2_QtInv]
      show (codeMat 423 : Mat3).transpose * codeMat 365 * (codeMat 501 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 159 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 159 (by decide)
    have hact : actionA (codeMat 423) (codeMat 494) (codeMat 159) = codeMat 84 := by
      unfold actionA
      rw [step109wc185s2_QtInv]
      show (codeMat 423 : Mat3).transpose * codeMat 159 * (codeMat 501 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 504 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 504 (by decide)
    have hact : actionA (codeMat 423) (codeMat 494) (codeMat 504) = codeMat 32 := by
      unfold actionA
      rw [step109wc185s2_QtInv]
      show (codeMat 423 : Mat3).transpose * codeMat 504 * (codeMat 501 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 245 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 245 (by decide)
    have hact : actionA (codeMat 423) (codeMat 494) (codeMat 245) = codeMat 10 := by
      unfold actionA
      rw [step109wc185s2_QtInv]
      show (codeMat 423 : Mat3).transpose * codeMat 245 * (codeMat 501 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 390 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 390 (by decide)
    have hact : actionA (codeMat 423) (codeMat 494) (codeMat 390) = codeMat 1 := by
      unfold actionA
      rw [step109wc185s2_QtInv]
      show (codeMat 423 : Mat3).transpose * codeMat 390 * (codeMat 501 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact

theorem step109wc185s2Dispatch :
    QuotientRankAtLeast (o185SourceU_wc ⟨2, by omega⟩) 14 := by
  have hP : Invertible (codeMat 423 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 494 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 423) (codeMat 494) o78W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 423) (codeMat 494) hP hQ o78W_wc 14
      step109_orbit78_lb14_wc
  exact quotientRankAtLeast_mono step109wc185s2_contain hAct


private theorem step109wc185s3_QtInv :
    (codeMat 396 : Mat3).transpose⁻¹ = (codeMat 106 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 396 : Mat3).transpose * (codeMat 106 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc185s3_contain :
    (o185SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 110) (codeMat 396) o78W_wc := by
  change spanCodes [276, 132, 84, 32, 10, 1] ≤ actionW (codeMat 110) (codeMat 396) o78W_wc
  apply step109wc185_spanCodes_le_of_gens [276, 132, 84, 32, 10, 1]
    (actionW (codeMat 110) (codeMat 396) o78W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 268 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 268 (by decide)
    have hact : actionA (codeMat 110) (codeMat 396) (codeMat 268) = codeMat 276 := by
      unfold actionA
      rw [step109wc185s3_QtInv]
      show (codeMat 110 : Mat3).transpose * codeMat 268 * (codeMat 106 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 96 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 96 (by decide)
    have hact : actionA (codeMat 110) (codeMat 396) (codeMat 96) = codeMat 132 := by
      unfold actionA
      rw [step109wc185s3_QtInv]
      show (codeMat 110 : Mat3).transpose * codeMat 96 * (codeMat 106 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 244 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 244 (by decide)
    have hact : actionA (codeMat 110) (codeMat 396) (codeMat 244) = codeMat 84 := by
      unfold actionA
      rw [step109wc185s3_QtInv]
      show (codeMat 110 : Mat3).transpose * codeMat 244 * (codeMat 106 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 365 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 365 (by decide)
    have hact : actionA (codeMat 110) (codeMat 396) (codeMat 365) = codeMat 32 := by
      unfold actionA
      rw [step109wc185s3_QtInv]
      show (codeMat 110 : Mat3).transpose * codeMat 365 * (codeMat 106 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 402 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 402 (by decide)
    have hact : actionA (codeMat 110) (codeMat 396) (codeMat 402) = codeMat 10 := by
      unfold actionA
      rw [step109wc185s3_QtInv]
      show (codeMat 110 : Mat3).transpose * codeMat 402 * (codeMat 106 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 110) (codeMat 396) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc185s3_QtInv]
      show (codeMat 110 : Mat3).transpose * codeMat 128 * (codeMat 106 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact

theorem step109wc185s3Dispatch :
    QuotientRankAtLeast (o185SourceU_wc ⟨3, by omega⟩) 14 := by
  have hP : Invertible (codeMat 110 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 396 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 110) (codeMat 396) o78W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 110) (codeMat 396) hP hQ o78W_wc 14
      step109_orbit78_lb14_wc
  exact quotientRankAtLeast_mono step109wc185s3_contain hAct


private theorem step109wc185s4_QtInv :
    (codeMat 459 : Mat3).transpose⁻¹ = (codeMat 346 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 459 : Mat3).transpose * (codeMat 346 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc185s4_contain :
    (o185SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 174) (codeMat 459) o56W := by
  change spanCodes [278, 134, 84, 32, 10, 1] ≤ actionW (codeMat 174) (codeMat 459) o56W
  apply step109wc185_spanCodes_le_of_gens [278, 134, 84, 32, 10, 1]
    (actionW (codeMat 174) (codeMat 459) o56W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 13 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 13 (by decide)
    have hact : actionA (codeMat 174) (codeMat 459) (codeMat 13) = codeMat 278 := by
      unfold actionA
      rw [step109wc185s4_QtInv]
      show (codeMat 174 : Mat3).transpose * codeMat 13 * (codeMat 346 : Mat3).transpose = codeMat 278
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 268 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 268 (by decide)
    have hact : actionA (codeMat 174) (codeMat 459) (codeMat 268) = codeMat 134 := by
      unfold actionA
      rw [step109wc185s4_QtInv]
      show (codeMat 174 : Mat3).transpose * codeMat 268 * (codeMat 346 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 419 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 419 (by decide)
    have hact : actionA (codeMat 174) (codeMat 459) (codeMat 419) = codeMat 84 := by
      unfold actionA
      rw [step109wc185s4_QtInv]
      show (codeMat 174 : Mat3).transpose * codeMat 419 * (codeMat 346 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 174) (codeMat 459) (codeMat 256) = codeMat 32 := by
      unfold actionA
      rw [step109wc185s4_QtInv]
      show (codeMat 174 : Mat3).transpose * codeMat 256 * (codeMat 346 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 173 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 173 (by decide)
    have hact : actionA (codeMat 174) (codeMat 459) (codeMat 173) = codeMat 10 := by
      unfold actionA
      rw [step109wc185s4_QtInv]
      show (codeMat 174 : Mat3).transpose * codeMat 173 * (codeMat 346 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 511 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 511 (by decide)
    have hact : actionA (codeMat 174) (codeMat 459) (codeMat 511) = codeMat 1 := by
      unfold actionA
      rw [step109wc185s4_QtInv]
      show (codeMat 174 : Mat3).transpose * codeMat 511 * (codeMat 346 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact

theorem step109wc185s4Dispatch :
    QuotientRankAtLeast (o185SourceU_wc ⟨4, by omega⟩) 14 := by
  have hP : Invertible (codeMat 174 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 459 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 174) (codeMat 459) o56W) 14 :=
    @quotientRankAtLeast_action (codeMat 174) (codeMat 459) hP hQ o56W 14
      step99_orbit56_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc185s4_contain hAct


private theorem step109wc185s5_QtInv :
    (codeMat 114 : Mat3).transpose⁻¹ = (codeMat 204 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 114 : Mat3).transpose * (codeMat 204 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc185s5_contain :
    (o185SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 206) (codeMat 114) o83W_wc := by
  change spanCodes [262, 150, 84, 32, 10, 1] ≤ actionW (codeMat 206) (codeMat 114) o83W_wc
  apply step109wc185_spanCodes_le_of_gens [262, 150, 84, 32, 10, 1]
    (actionW (codeMat 206) (codeMat 114) o83W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 154 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 154 (by decide)
    have hact : actionA (codeMat 206) (codeMat 114) (codeMat 154) = codeMat 262 := by
      unfold actionA
      rw [step109wc185s5_QtInv]
      show (codeMat 206 : Mat3).transpose * codeMat 154 * (codeMat 204 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 11 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 206) (codeMat 114) (codeMat 11) = codeMat 150 := by
      unfold actionA
      rw [step109wc185s5_QtInv]
      show (codeMat 206 : Mat3).transpose * codeMat 11 * (codeMat 204 : Mat3).transpose = codeMat 150
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 492 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 492 (by decide)
    have hact : actionA (codeMat 206) (codeMat 114) (codeMat 492) = codeMat 84 := by
      unfold actionA
      rw [step109wc185s5_QtInv]
      show (codeMat 206 : Mat3).transpose * codeMat 492 * (codeMat 204 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 144 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 144 (by decide)
    have hact : actionA (codeMat 206) (codeMat 114) (codeMat 144) = codeMat 32 := by
      unfold actionA
      rw [step109wc185s5_QtInv]
      show (codeMat 206 : Mat3).transpose * codeMat 144 * (codeMat 204 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 312 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 312 (by decide)
    have hact : actionA (codeMat 206) (codeMat 114) (codeMat 312) = codeMat 10 := by
      unfold actionA
      rw [step109wc185s5_QtInv]
      show (codeMat 206 : Mat3).transpose * codeMat 312 * (codeMat 204 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 206) (codeMat 114) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc185s5_QtInv]
      show (codeMat 206 : Mat3).transpose * codeMat 32 * (codeMat 204 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact

theorem step109wc185s5Dispatch :
    QuotientRankAtLeast (o185SourceU_wc ⟨5, by omega⟩) 14 := by
  have hP : Invertible (codeMat 206 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 114 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 206) (codeMat 114) o83W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 206) (codeMat 114) hP hQ o83W_wc 14
      step109_orbit83_lb14_wc
  exact quotientRankAtLeast_mono step109wc185s5_contain hAct


private theorem step109wc185s6_QtInv :
    (codeMat 163 : Mat3).transpose⁻¹ = (codeMat 165 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 163 : Mat3).transpose * (codeMat 165 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc185s6_contain :
    (o185SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 330) (codeMat 163) orbit41W := by
  change spanCodes [400, 84, 32, 8, 2, 1] ≤ actionW (codeMat 330) (codeMat 163) orbit41W
  apply step109wc185_spanCodes_le_of_gens [400, 84, 32, 8, 2, 1]
    (actionW (codeMat 330) (codeMat 163) orbit41W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 509 ∈ orbit41W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 384] 509 (by decide)
    have hact : actionA (codeMat 330) (codeMat 163) (codeMat 509) = codeMat 400 := by
      unfold actionA
      rw [step109wc185s6_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 509 * (codeMat 165 : Mat3).transpose = codeMat 400
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 93 ∈ orbit41W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 384] 93 (by decide)
    have hact : actionA (codeMat 330) (codeMat 163) (codeMat 93) = codeMat 84 := by
      unfold actionA
      rw [step109wc185s6_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 93 * (codeMat 165 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit41W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 384] 2 (by decide)
    have hact : actionA (codeMat 330) (codeMat 163) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [step109wc185s6_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 2 * (codeMat 165 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ orbit41W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 384] 1 (by decide)
    have hact : actionA (codeMat 330) (codeMat 163) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step109wc185s6_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 1 * (codeMat 165 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 40 ∈ orbit41W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 384] 40 (by decide)
    have hact : actionA (codeMat 330) (codeMat 163) (codeMat 40) = codeMat 2 := by
      unfold actionA
      rw [step109wc185s6_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 40 * (codeMat 165 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit41W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 384] 8 (by decide)
    have hact : actionA (codeMat 330) (codeMat 163) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc185s6_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 8 * (codeMat 165 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact

theorem step109wc185s6Dispatch :
    QuotientRankAtLeast (o185SourceU_wc ⟨6, by omega⟩) 12 := by
  have hP : Invertible (codeMat 330 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 163 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 330) (codeMat 163) orbit41W) 12 :=
    @quotientRankAtLeast_action (codeMat 330) (codeMat 163) hP hQ orbit41W 12
      orbit41_lb12
  exact quotientRankAtLeast_mono step109wc185s6_contain hAct


private theorem step109wc185s7_QtInv :
    (codeMat 158 : Mat3).transpose⁻¹ = (codeMat 358 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 158 : Mat3).transpose * (codeMat 358 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc185s7_contain :
    (o185SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 281) (codeMat 158) o39W_mono := by
  change spanCodes [400, 80, 32, 10, 4, 1] ≤ actionW (codeMat 281) (codeMat 158) o39W_mono
  apply step109wc185_spanCodes_le_of_gens [400, 80, 32, 10, 4, 1]
    (actionW (codeMat 281) (codeMat 158) o39W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 447 ∈ o39W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 20, 8, 2, 1] 447 (by decide)
    have hact : actionA (codeMat 281) (codeMat 158) (codeMat 447) = codeMat 400 := by
      unfold actionA
      rw [step109wc185s7_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 447 * (codeMat 358 : Mat3).transpose = codeMat 400
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 191 ∈ o39W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 20, 8, 2, 1] 191 (by decide)
    have hact : actionA (codeMat 281) (codeMat 158) (codeMat 191) = codeMat 80 := by
      unfold actionA
      rw [step109wc185s7_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 191 * (codeMat 358 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 9 ∈ o39W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 20, 8, 2, 1] 9 (by decide)
    have hact : actionA (codeMat 281) (codeMat 158) (codeMat 9) = codeMat 32 := by
      unfold actionA
      rw [step109wc185s7_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 9 * (codeMat 358 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 21 ∈ o39W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 20, 8, 2, 1] 21 (by decide)
    have hact : actionA (codeMat 281) (codeMat 158) (codeMat 21) = codeMat 10 := by
      unfold actionA
      rw [step109wc185s7_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 21 * (codeMat 358 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o39W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 281) (codeMat 158) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step109wc185s7_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 1 * (codeMat 358 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o39W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 281) (codeMat 158) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc185s7_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 2 * (codeMat 358 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact

theorem step109wc185s7Dispatch :
    QuotientRankAtLeast (o185SourceU_wc ⟨7, by omega⟩) 12 := by
  have hP : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 158 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 281) (codeMat 158) o39W_mono) 12 :=
    @quotientRankAtLeast_action (codeMat 281) (codeMat 158) hP hQ o39W_mono 12
      orbit39_lb12_mono
  exact quotientRankAtLeast_mono step109wc185s7_contain hAct

private def step109wc185s8SrcT : Submodule F2 Mat3 := spanCodes [272, 128, 96, 8, 2, 1]

private theorem step109wc185s8SrcT_lb : QuotientRankAtLeast step109wc185s8SrcT 12 := by
  have ht := quotientRankAtLeast_transpose orbit44_lb12_mono
  have hle : step109wc185s8SrcT ≤ transposeW o44W_mono := by
    unfold step109wc185s8SrcT transposeW
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

private theorem step109wc185s8_QtInv :
    (codeMat 444 : Mat3).transpose⁻¹ = (codeMat 110 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 444 : Mat3).transpose * (codeMat 110 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc185s8_contain :
    (o185SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 94) (codeMat 444) step109wc185s8SrcT := by
  change spanCodes [390, 66, 32, 22, 10, 1] ≤ actionW (codeMat 94) (codeMat 444) step109wc185s8SrcT
  apply step109wc185_spanCodes_le_of_gens [390, 66, 32, 22, 10, 1]
    (actionW (codeMat 94) (codeMat 444) step109wc185s8SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 9 ∈ step109wc185s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 96, 8, 2, 1] 9 (by decide)
    have hact : actionA (codeMat 94) (codeMat 444) (codeMat 9) = codeMat 390 := by
      unfold actionA
      rw [step109wc185s8_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 9 * (codeMat 110 : Mat3).transpose = codeMat 390
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 274 ∈ step109wc185s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 96, 8, 2, 1] 274 (by decide)
    have hact : actionA (codeMat 94) (codeMat 444) (codeMat 274) = codeMat 66 := by
      unfold actionA
      rw [step109wc185s8_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 274 * (codeMat 110 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 504 ∈ step109wc185s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 96, 8, 2, 1] 504 (by decide)
    have hact : actionA (codeMat 94) (codeMat 444) (codeMat 504) = codeMat 32 := by
      unfold actionA
      rw [step109wc185s8_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 504 * (codeMat 110 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 496 ∈ step109wc185s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 96, 8, 2, 1] 496 (by decide)
    have hact : actionA (codeMat 94) (codeMat 444) (codeMat 496) = codeMat 22 := by
      unfold actionA
      rw [step109wc185s8_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 496 * (codeMat 110 : Mat3).transpose = codeMat 22
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 272 ∈ step109wc185s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 96, 8, 2, 1] 272 (by decide)
    have hact : actionA (codeMat 94) (codeMat 444) (codeMat 272) = codeMat 10 := by
      unfold actionA
      rw [step109wc185s8_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 272 * (codeMat 110 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ step109wc185s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 96, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 94) (codeMat 444) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc185s8_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 128 * (codeMat 110 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact

theorem step109wc185s8Dispatch :
    QuotientRankAtLeast (o185SourceU_wc ⟨8, by omega⟩) 12 := by
  have hP : Invertible (codeMat 94 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 444 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 94) (codeMat 444) step109wc185s8SrcT) 12 :=
    @quotientRankAtLeast_action (codeMat 94) (codeMat 444) hP hQ step109wc185s8SrcT 12
      step109wc185s8SrcT_lb
  exact quotientRankAtLeast_mono step109wc185s8_contain hAct


private theorem step109wc185s9_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc185s9_contain :
    (o185SourceU_wc ⟨9, by omega⟩) ≤ actionW (codeMat 84) (codeMat 84) orbit10W := by
  change spanCodes [256, 128, 68, 32, 16, 10, 1] ≤ actionW (codeMat 84) (codeMat 84) orbit10W
  apply step109wc185_spanCodes_le_of_gens [256, 128, 68, 32, 16, 10, 1]
    (actionW (codeMat 84) (codeMat 84) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc185s9_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 2) = codeMat 128 := by
      unfold actionA
      rw [step109wc185s9_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step109wc185s9_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 68 * (codeMat 84 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc185s9_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 84 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 16) = codeMat 16 := by
      unfold actionA
      rw [step109wc185s9_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 16 * (codeMat 84 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc185s9_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 160 * (codeMat 84 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc185s9_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact

theorem step109wc185s9Dispatch :
    QuotientRankAtLeast (o185SourceU_wc ⟨9, by omega⟩) 12 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 84) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 84) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc185s9_contain hAct


private theorem step109wc185s10_QtInv :
    (codeMat 86 : Mat3).transpose⁻¹ = (codeMat 212 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 86 : Mat3).transpose * (codeMat 212 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc185s10_contain :
    (o185SourceU_wc ⟨10, by omega⟩) ≤ actionW (codeMat 87) (codeMat 86) orbit14W := by
  change spanCodes [258, 146, 82, 32, 10, 6, 1] ≤ actionW (codeMat 87) (codeMat 86) orbit14W
  apply step109wc185_spanCodes_le_of_gens [258, 146, 82, 32, 10, 6, 1]
    (actionW (codeMat 87) (codeMat 86) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 137 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 137 (by decide)
    have hact : actionA (codeMat 87) (codeMat 86) (codeMat 137) = codeMat 258 := by
      unfold actionA
      rw [step109wc185s10_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 137 * (codeMat 212 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 87) (codeMat 86) (codeMat 3) = codeMat 146 := by
      unfold actionA
      rw [step109wc185s10_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 3 * (codeMat 212 : Mat3).transpose = codeMat 146
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 508 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 508 (by decide)
    have hact : actionA (codeMat 87) (codeMat 86) (codeMat 508) = codeMat 82 := by
      unfold actionA
      rw [step109wc185s10_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 508 * (codeMat 212 : Mat3).transpose = codeMat 82
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 87) (codeMat 86) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc185s10_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 8 * (codeMat 212 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 224 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 224 (by decide)
    have hact : actionA (codeMat 87) (codeMat 86) (codeMat 224) = codeMat 10 := by
      unfold actionA
      rw [step109wc185s10_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 224 * (codeMat 212 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 87) (codeMat 86) (codeMat 128) = codeMat 6 := by
      unfold actionA
      rw [step109wc185s10_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 128 * (codeMat 212 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 87) (codeMat 86) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc185s10_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 256 * (codeMat 212 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc185_codeMat_mem_actionW_of_witness hw hact

theorem step109wc185s10Dispatch :
    QuotientRankAtLeast (o185SourceU_wc ⟨10, by omega⟩) 12 := by
  have hP : Invertible (codeMat 87 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 87) (codeMat 86) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 87) (codeMat 86) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc185s10_contain hAct

theorem step109wc185_all_dispatch (i : Fin 11) :
    QuotientRankAtLeast (o185SourceU_wc i) (o185SourceLb_wc i) := by
  fin_cases i
  · exact step109wc185s0Dispatch
  · exact step109wc185s1Dispatch
  · exact step109wc185s2Dispatch
  · exact step109wc185s3Dispatch
  · exact step109wc185s4Dispatch
  · exact step109wc185s5Dispatch
  · exact step109wc185s6Dispatch
  · exact step109wc185s7Dispatch
  · exact step109wc185s8Dispatch
  · exact step109wc185s9Dispatch
  · exact step109wc185s10Dispatch

theorem step109_orbit185_lb15_wc : QuotientRankAtLeast o185W_wc 15 :=
  o185Lb15_wc step109wc185_all_dispatch

end QiushiMatmul
