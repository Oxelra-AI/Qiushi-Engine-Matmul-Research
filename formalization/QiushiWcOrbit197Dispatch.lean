import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit197Consumer
import QiushiStep99Orbit55Dispatch
import QiushiWcOrbit78Dispatch
import QiushiMonoOrbit43From14
import QiushiOrbit40FP
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc197_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc197_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

private def step109wc197s0SrcT : Submodule F2 Mat3 := spanCodes [272, 128, 66, 34, 8, 1]

private theorem step109wc197s0SrcT_lb : QuotientRankAtLeast step109wc197s0SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step99_orbit55_lb14_unconditional
  have hle : step109wc197s0SrcT ≤ transposeW o55W := by
    unfold step109wc197s0SrcT transposeW
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

private theorem step109wc197s0_QtInv :
    (codeMat 167 : Mat3).transpose⁻¹ = (codeMat 167 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 167 : Mat3).transpose * (codeMat 167 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc197s0_contain :
    (o197SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 335) (codeMat 167) step109wc197s0SrcT := by
  change spanCodes [262, 132, 66, 32, 10, 1] ≤ actionW (codeMat 335) (codeMat 167) step109wc197s0SrcT
  apply step109wc197_spanCodes_le_of_gens [262, 132, 66, 32, 10, 1]
    (actionW (codeMat 335) (codeMat 167) step109wc197s0SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 232 ∈ step109wc197s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 232 (by decide)
    have hact : actionA (codeMat 335) (codeMat 167) (codeMat 232) = codeMat 262 := by
      unfold actionA
      rw [step109wc197s0_QtInv]
      show (codeMat 335 : Mat3).transpose * codeMat 232 * (codeMat 167 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 368 ∈ step109wc197s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 368 (by decide)
    have hact : actionA (codeMat 335) (codeMat 167) (codeMat 368) = codeMat 132 := by
      unfold actionA
      rw [step109wc197s0_QtInv]
      show (codeMat 335 : Mat3).transpose * codeMat 368 * (codeMat 167 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 96 ∈ step109wc197s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 96 (by decide)
    have hact : actionA (codeMat 335) (codeMat 167) (codeMat 96) = codeMat 66 := by
      unfold actionA
      rw [step109wc197s0_QtInv]
      show (codeMat 335 : Mat3).transpose * codeMat 96 * (codeMat 167 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 195 ∈ step109wc197s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 195 (by decide)
    have hact : actionA (codeMat 335) (codeMat 167) (codeMat 195) = codeMat 32 := by
      unfold actionA
      rw [step109wc197s0_QtInv]
      show (codeMat 335 : Mat3).transpose * codeMat 195 * (codeMat 167 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 105 ∈ step109wc197s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 105 (by decide)
    have hact : actionA (codeMat 335) (codeMat 167) (codeMat 105) = codeMat 10 := by
      unfold actionA
      rw [step109wc197s0_QtInv]
      show (codeMat 335 : Mat3).transpose * codeMat 105 * (codeMat 167 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ step109wc197s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 8 (by decide)
    have hact : actionA (codeMat 335) (codeMat 167) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc197s0_QtInv]
      show (codeMat 335 : Mat3).transpose * codeMat 8 * (codeMat 167 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact

theorem step109wc197s0Dispatch :
    QuotientRankAtLeast (o197SourceU_wc ⟨0, by omega⟩) 14 := by
  have hP : Invertible (codeMat 335 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 167 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 335) (codeMat 167) step109wc197s0SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 335) (codeMat 167) hP hQ step109wc197s0SrcT 14
      step109wc197s0SrcT_lb
  exact quotientRankAtLeast_mono step109wc197s0_contain hAct


private theorem step109wc197s1_QtInv :
    (codeMat 498 : Mat3).transpose⁻¹ = (codeMat 206 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 498 : Mat3).transpose * (codeMat 206 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc197s1_contain :
    (o197SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 397) (codeMat 498) o55W := by
  change spanCodes [258, 132, 70, 32, 10, 1] ≤ actionW (codeMat 397) (codeMat 498) o55W
  apply step109wc197_spanCodes_le_of_gens [258, 132, 70, 32, 10, 1]
    (actionW (codeMat 397) (codeMat 498) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 14 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 14 (by decide)
    have hact : actionA (codeMat 397) (codeMat 498) (codeMat 14) = codeMat 258 := by
      unfold actionA
      rw [step109wc197s1_QtInv]
      show (codeMat 397 : Mat3).transpose * codeMat 14 * (codeMat 206 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 15 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 15 (by decide)
    have hact : actionA (codeMat 397) (codeMat 498) (codeMat 15) = codeMat 132 := by
      unfold actionA
      rw [step109wc197s1_QtInv]
      show (codeMat 397 : Mat3).transpose * codeMat 15 * (codeMat 206 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 44 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 44 (by decide)
    have hact : actionA (codeMat 397) (codeMat 498) (codeMat 44) = codeMat 70 := by
      unfold actionA
      rw [step109wc197s1_QtInv]
      show (codeMat 397 : Mat3).transpose * codeMat 44 * (codeMat 206 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 438 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 438 (by decide)
    have hact : actionA (codeMat 397) (codeMat 498) (codeMat 438) = codeMat 32 := by
      unfold actionA
      rw [step109wc197s1_QtInv]
      show (codeMat 397 : Mat3).transpose * codeMat 438 * (codeMat 206 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 284 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 284 (by decide)
    have hact : actionA (codeMat 397) (codeMat 498) (codeMat 284) = codeMat 10 := by
      unfold actionA
      rw [step109wc197s1_QtInv]
      show (codeMat 397 : Mat3).transpose * codeMat 284 * (codeMat 206 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 397) (codeMat 498) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc197s1_QtInv]
      show (codeMat 397 : Mat3).transpose * codeMat 32 * (codeMat 206 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact

theorem step109wc197s1Dispatch :
    QuotientRankAtLeast (o197SourceU_wc ⟨1, by omega⟩) 14 := by
  have hP : Invertible (codeMat 397 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 498 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 397) (codeMat 498) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 397) (codeMat 498) hP hQ o55W 14
      step99_orbit55_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc197s1_contain hAct


private theorem step109wc197s2_QtInv :
    (codeMat 233 : Mat3).transpose⁻¹ = (codeMat 233 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 233 : Mat3).transpose * (codeMat 233 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc197s2_contain :
    (o197SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 156) (codeMat 233) o78W_wc := by
  change spanCodes [276, 132, 80, 32, 10, 1] ≤ actionW (codeMat 156) (codeMat 233) o78W_wc
  apply step109wc197_spanCodes_le_of_gens [276, 132, 80, 32, 10, 1]
    (actionW (codeMat 156) (codeMat 233) o78W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 402 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 402 (by decide)
    have hact : actionA (codeMat 156) (codeMat 233) (codeMat 402) = codeMat 276 := by
      unfold actionA
      rw [step109wc197s2_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 402 * (codeMat 233 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 148 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 148 (by decide)
    have hact : actionA (codeMat 156) (codeMat 233) (codeMat 148) = codeMat 132 := by
      unfold actionA
      rw [step109wc197s2_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 148 * (codeMat 233 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 263 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 263 (by decide)
    have hact : actionA (codeMat 156) (codeMat 233) (codeMat 263) = codeMat 80 := by
      unfold actionA
      rw [step109wc197s2_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 263 * (codeMat 233 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 156) (codeMat 233) (codeMat 128) = codeMat 32 := by
      unfold actionA
      rw [step109wc197s2_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 128 * (codeMat 233 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 224 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 224 (by decide)
    have hact : actionA (codeMat 156) (codeMat 233) (codeMat 224) = codeMat 10 := by
      unfold actionA
      rw [step109wc197s2_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 224 * (codeMat 233 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 504 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 504 (by decide)
    have hact : actionA (codeMat 156) (codeMat 233) (codeMat 504) = codeMat 1 := by
      unfold actionA
      rw [step109wc197s2_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 504 * (codeMat 233 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact

theorem step109wc197s2Dispatch :
    QuotientRankAtLeast (o197SourceU_wc ⟨2, by omega⟩) 14 := by
  have hP : Invertible (codeMat 156 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 156) (codeMat 233) o78W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 156) (codeMat 233) hP hQ o78W_wc 14
      step109_orbit78_lb14_wc
  exact quotientRankAtLeast_mono step109wc197s2_contain hAct


private theorem step109wc197s3_QtInv :
    (codeMat 382 : Mat3).transpose⁻¹ = (codeMat 499 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 382 : Mat3).transpose * (codeMat 499 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc197s3_contain :
    (o197SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 309) (codeMat 382) o78W_wc := by
  change spanCodes [272, 132, 84, 32, 10, 1] ≤ actionW (codeMat 309) (codeMat 382) o78W_wc
  apply step109wc197_spanCodes_le_of_gens [272, 132, 84, 32, 10, 1]
    (actionW (codeMat 309) (codeMat 382) o78W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 280 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 280 (by decide)
    have hact : actionA (codeMat 309) (codeMat 382) (codeMat 280) = codeMat 272 := by
      unfold actionA
      rw [step109wc197s3_QtInv]
      show (codeMat 309 : Mat3).transpose * codeMat 280 * (codeMat 499 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 263 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 263 (by decide)
    have hact : actionA (codeMat 309) (codeMat 382) (codeMat 263) = codeMat 132 := by
      unfold actionA
      rw [step109wc197s3_QtInv]
      show (codeMat 309 : Mat3).transpose * codeMat 263 * (codeMat 499 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 159 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 159 (by decide)
    have hact : actionA (codeMat 309) (codeMat 382) (codeMat 159) = codeMat 84 := by
      unfold actionA
      rw [step109wc197s3_QtInv]
      show (codeMat 309 : Mat3).transpose * codeMat 159 * (codeMat 499 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 504 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 504 (by decide)
    have hact : actionA (codeMat 309) (codeMat 382) (codeMat 504) = codeMat 32 := by
      unfold actionA
      rw [step109wc197s3_QtInv]
      show (codeMat 309 : Mat3).transpose * codeMat 504 * (codeMat 499 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 371 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 371 (by decide)
    have hact : actionA (codeMat 309) (codeMat 382) (codeMat 371) = codeMat 10 := by
      unfold actionA
      rw [step109wc197s3_QtInv]
      show (codeMat 309 : Mat3).transpose * codeMat 371 * (codeMat 499 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 390 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 390 (by decide)
    have hact : actionA (codeMat 309) (codeMat 382) (codeMat 390) = codeMat 1 := by
      unfold actionA
      rw [step109wc197s3_QtInv]
      show (codeMat 309 : Mat3).transpose * codeMat 390 * (codeMat 499 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact

theorem step109wc197s3Dispatch :
    QuotientRankAtLeast (o197SourceU_wc ⟨3, by omega⟩) 14 := by
  have hP : Invertible (codeMat 309 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 382 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 309) (codeMat 382) o78W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 309) (codeMat 382) hP hQ o78W_wc 14
      step109_orbit78_lb14_wc
  exact quotientRankAtLeast_mono step109wc197s3_contain hAct


private theorem step109wc197s4_QtInv :
    (codeMat 165 : Mat3).transpose⁻¹ = (codeMat 163 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 165 : Mat3).transpose * (codeMat 163 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc197s4_contain :
    (o197SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 330) (codeMat 165) o43W_mono := by
  change spanCodes [324, 132, 32, 8, 2, 1] ≤ actionW (codeMat 330) (codeMat 165) o43W_mono
  apply step109wc197_spanCodes_le_of_gens [324, 132, 32, 8, 2, 1]
    (actionW (codeMat 330) (codeMat 165) o43W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 136 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 136 (by decide)
    have hact : actionA (codeMat 330) (codeMat 165) (codeMat 136) = codeMat 324 := by
      unfold actionA
      rw [step109wc197s4_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 136 * (codeMat 163 : Mat3).transpose = codeMat 324
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 312 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 312 (by decide)
    have hact : actionA (codeMat 330) (codeMat 165) (codeMat 312) = codeMat 132 := by
      unfold actionA
      rw [step109wc197s4_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 312 * (codeMat 163 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 3 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 330) (codeMat 165) (codeMat 3) = codeMat 32 := by
      unfold actionA
      rw [step109wc197s4_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 3 * (codeMat 163 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 330) (codeMat 165) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step109wc197s4_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 1 * (codeMat 163 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 330) (codeMat 165) (codeMat 32) = codeMat 2 := by
      unfold actionA
      rw [step109wc197s4_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 32 * (codeMat 163 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 330) (codeMat 165) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc197s4_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 8 * (codeMat 163 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact

theorem step109wc197s4Dispatch :
    QuotientRankAtLeast (o197SourceU_wc ⟨4, by omega⟩) 12 := by
  have hP : Invertible (codeMat 330 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 165 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 330) (codeMat 165) o43W_mono) 12 :=
    @quotientRankAtLeast_action (codeMat 330) (codeMat 165) hP hQ o43W_mono 12
      orbit43_lb12_mono
  exact quotientRankAtLeast_mono step109wc197s4_contain hAct


private theorem step109wc197s5_QtInv :
    (codeMat 370 : Mat3).transpose⁻¹ = (codeMat 207 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 370 : Mat3).transpose * (codeMat 207 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc197s5_contain :
    (o197SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 205) (codeMat 370) o43W_mono := by
  change spanCodes [322, 130, 32, 10, 6, 1] ≤ actionW (codeMat 205) (codeMat 370) o43W_mono
  apply step109wc197_spanCodes_le_of_gens [322, 130, 32, 10, 6, 1]
    (actionW (codeMat 205) (codeMat 370) o43W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 10 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 10 (by decide)
    have hact : actionA (codeMat 205) (codeMat 370) (codeMat 10) = codeMat 322 := by
      unfold actionA
      rw [step109wc197s5_QtInv]
      show (codeMat 205 : Mat3).transpose * codeMat 10 * (codeMat 207 : Mat3).transpose = codeMat 322
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 3 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 205) (codeMat 370) (codeMat 3) = codeMat 130 := by
      unfold actionA
      rw [step109wc197s5_QtInv]
      show (codeMat 205 : Mat3).transpose * codeMat 3 * (codeMat 207 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 432 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 432 (by decide)
    have hact : actionA (codeMat 205) (codeMat 370) (codeMat 432) = codeMat 32 := by
      unfold actionA
      rw [step109wc197s5_QtInv]
      show (codeMat 205 : Mat3).transpose * codeMat 432 * (codeMat 207 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 312 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 312 (by decide)
    have hact : actionA (codeMat 205) (codeMat 370) (codeMat 312) = codeMat 10 := by
      unfold actionA
      rw [step109wc197s5_QtInv]
      show (codeMat 205 : Mat3).transpose * codeMat 312 * (codeMat 207 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 40 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 205) (codeMat 370) (codeMat 40) = codeMat 6 := by
      unfold actionA
      rw [step109wc197s5_QtInv]
      show (codeMat 205 : Mat3).transpose * codeMat 40 * (codeMat 207 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 205) (codeMat 370) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc197s5_QtInv]
      show (codeMat 205 : Mat3).transpose * codeMat 32 * (codeMat 207 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact

theorem step109wc197s5Dispatch :
    QuotientRankAtLeast (o197SourceU_wc ⟨5, by omega⟩) 12 := by
  have hP : Invertible (codeMat 205 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 370 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 205) (codeMat 370) o43W_mono) 12 :=
    @quotientRankAtLeast_action (codeMat 205) (codeMat 370) hP hQ o43W_mono 12
      orbit43_lb12_mono
  exact quotientRankAtLeast_mono step109wc197s5_contain hAct


private theorem step109wc197s6_QtInv :
    (codeMat 177 : Mat3).transpose⁻¹ = (codeMat 417 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 177 : Mat3).transpose * (codeMat 417 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc197s6_contain :
    (o197SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 165) (codeMat 177) orbit40W := by
  change spanCodes [260, 132, 64, 32, 10, 1] ≤ actionW (codeMat 165) (codeMat 177) orbit40W
  apply step109wc197_spanCodes_le_of_gens [260, 132, 64, 32, 10, 1]
    (actionW (codeMat 165) (codeMat 177) orbit40W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 2 ∈ orbit40W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 128] 2 (by decide)
    have hact : actionA (codeMat 165) (codeMat 177) (codeMat 2) = codeMat 260 := by
      unfold actionA
      rw [step109wc197s6_QtInv]
      show (codeMat 165 : Mat3).transpose * codeMat 2 * (codeMat 417 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 34 ∈ orbit40W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 128] 34 (by decide)
    have hact : actionA (codeMat 165) (codeMat 177) (codeMat 34) = codeMat 132 := by
      unfold actionA
      rw [step109wc197s6_QtInv]
      show (codeMat 165 : Mat3).transpose * codeMat 34 * (codeMat 417 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ orbit40W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 128] 8 (by decide)
    have hact : actionA (codeMat 165) (codeMat 177) (codeMat 8) = codeMat 64 := by
      unfold actionA
      rw [step109wc197s6_QtInv]
      show (codeMat 165 : Mat3).transpose * codeMat 8 * (codeMat 417 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ orbit40W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 128] 128 (by decide)
    have hact : actionA (codeMat 165) (codeMat 177) (codeMat 128) = codeMat 32 := by
      unfold actionA
      rw [step109wc197s6_QtInv]
      show (codeMat 165 : Mat3).transpose * codeMat 128 * (codeMat 417 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 118 ∈ orbit40W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 128] 118 (by decide)
    have hact : actionA (codeMat 165) (codeMat 177) (codeMat 118) = codeMat 10 := by
      unfold actionA
      rw [step109wc197s6_QtInv]
      show (codeMat 165 : Mat3).transpose * codeMat 118 * (codeMat 417 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 9 ∈ orbit40W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 128] 9 (by decide)
    have hact : actionA (codeMat 165) (codeMat 177) (codeMat 9) = codeMat 1 := by
      unfold actionA
      rw [step109wc197s6_QtInv]
      show (codeMat 165 : Mat3).transpose * codeMat 9 * (codeMat 417 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact

theorem step109wc197s6Dispatch :
    QuotientRankAtLeast (o197SourceU_wc ⟨6, by omega⟩) 12 := by
  have hP : Invertible (codeMat 165 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 165) (codeMat 177) orbit40W) 12 :=
    @quotientRankAtLeast_action (codeMat 165) (codeMat 177) hP hQ orbit40W 12
      orbit40_lb12
  exact quotientRankAtLeast_mono step109wc197s6_contain hAct


private theorem step109wc197s7_QtInv :
    (codeMat 212 : Mat3).transpose⁻¹ = (codeMat 86 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 212 : Mat3).transpose * (codeMat 86 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc197s7_contain :
    (o197SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 84) (codeMat 212) orbit10W := by
  change spanCodes [256, 132, 68, 32, 18, 10, 1] ≤ actionW (codeMat 84) (codeMat 212) orbit10W
  apply step109wc197_spanCodes_le_of_gens [256, 132, 68, 32, 18, 10, 1]
    (actionW (codeMat 84) (codeMat 212) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 212) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc197s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 86 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 70 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 70 (by decide)
    have hact : actionA (codeMat 84) (codeMat 212) (codeMat 70) = codeMat 132 := by
      unfold actionA
      rw [step109wc197s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 70 * (codeMat 86 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 84) (codeMat 212) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step109wc197s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 68 * (codeMat 86 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 212) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc197s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 86 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 432 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide)
    have hact : actionA (codeMat 84) (codeMat 212) (codeMat 432) = codeMat 18 := by
      unfold actionA
      rw [step109wc197s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 432 * (codeMat 86 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 416 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 416 (by decide)
    have hact : actionA (codeMat 84) (codeMat 212) (codeMat 416) = codeMat 10 := by
      unfold actionA
      rw [step109wc197s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 416 * (codeMat 86 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 212) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc197s7_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 86 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact

theorem step109wc197s7Dispatch :
    QuotientRankAtLeast (o197SourceU_wc ⟨7, by omega⟩) 12 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 212 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 212) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 212) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc197s7_contain hAct


private theorem step109wc197s8_QtInv :
    (codeMat 157 : Mat3).transpose⁻¹ = (codeMat 486 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 157 : Mat3).transpose * (codeMat 486 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc197s8_contain :
    (o197SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 273) (codeMat 157) orbit14W := by
  change spanCodes [274, 128, 82, 32, 10, 4, 1] ≤ actionW (codeMat 273) (codeMat 157) orbit14W
  apply step109wc197_spanCodes_le_of_gens [274, 128, 82, 32, 10, 4, 1]
    (actionW (codeMat 273) (codeMat 157) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 118 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 118 (by decide)
    have hact : actionA (codeMat 273) (codeMat 157) (codeMat 118) = codeMat 274 := by
      unfold actionA
      rw [step109wc197s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 118 * (codeMat 486 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 273) (codeMat 157) (codeMat 384) = codeMat 128 := by
      unfold actionA
      rw [step109wc197s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 384 * (codeMat 486 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 246 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 246 (by decide)
    have hact : actionA (codeMat 273) (codeMat 157) (codeMat 246) = codeMat 82 := by
      unfold actionA
      rw [step109wc197s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 246 * (codeMat 486 : Mat3).transpose = codeMat 82
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 157) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc197s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 486 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 30 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 30 (by decide)
    have hact : actionA (codeMat 273) (codeMat 157) (codeMat 30) = codeMat 10 := by
      unfold actionA
      rw [step109wc197s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 30 * (codeMat 486 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 157) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step109wc197s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 486 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 273) (codeMat 157) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step109wc197s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 3 * (codeMat 486 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact

theorem step109wc197s8Dispatch :
    QuotientRankAtLeast (o197SourceU_wc ⟨8, by omega⟩) 12 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 157 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 157) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 157) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc197s8_contain hAct


private theorem step109wc197s9_QtInv :
    (codeMat 212 : Mat3).transpose⁻¹ = (codeMat 86 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 212 : Mat3).transpose * (codeMat 86 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc197s9_contain :
    (o197SourceU_wc ⟨9, by omega⟩) ≤ actionW (codeMat 84) (codeMat 212) flatW_3 := by
  change spanCodes [256, 132, 68, 32, 20, 8, 2, 1] ≤ actionW (codeMat 84) (codeMat 212) flatW_3
  apply step109wc197_spanCodes_le_of_gens [256, 132, 68, 32, 20, 8, 2, 1]
    (actionW (codeMat 84) (codeMat 212) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 212) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc197s9_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 86 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 70 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 70 (by decide)
    have hact : actionA (codeMat 84) (codeMat 212) (codeMat 70) = codeMat 132 := by
      unfold actionA
      rw [step109wc197s9_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 70 * (codeMat 86 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 68 (by decide)
    have hact : actionA (codeMat 84) (codeMat 212) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step109wc197s9_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 68 * (codeMat 86 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 212) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc197s9_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 86 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 112 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 112 (by decide)
    have hact : actionA (codeMat 84) (codeMat 212) (codeMat 112) = codeMat 20 := by
      unfold actionA
      rw [step109wc197s9_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 112 * (codeMat 86 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 84) (codeMat 212) (codeMat 32) = codeMat 8 := by
      unfold actionA
      rw [step109wc197s9_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 32 * (codeMat 86 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 212) (codeMat 384) = codeMat 2 := by
      unfold actionA
      rw [step109wc197s9_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 86 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 256 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 212) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc197s9_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 86 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact

theorem step109wc197s9Dispatch :
    QuotientRankAtLeast (o197SourceU_wc ⟨9, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 212 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 212) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 212) hP hQ flatW_3 9
      flatSeed_3
  exact quotientRankAtLeast_mono step109wc197s9_contain hAct


private theorem step109wc197s10_QtInv :
    (codeMat 206 : Mat3).transpose⁻¹ = (codeMat 498 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 206 : Mat3).transpose * (codeMat 498 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc197s10_contain :
    (o197SourceU_wc ⟨10, by omega⟩) ≤ actionW (codeMat 84) (codeMat 206) flatW_3 := by
  change spanCodes [256, 130, 66, 32, 16, 10, 6, 1] ≤ actionW (codeMat 84) (codeMat 206) flatW_3
  apply step109wc197_spanCodes_le_of_gens [256, 130, 66, 32, 16, 10, 6, 1]
    (actionW (codeMat 84) (codeMat 206) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc197s10_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 498 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 325 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 325 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 325) = codeMat 130 := by
      unfold actionA
      rw [step109wc197s10_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 325 * (codeMat 498 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 326 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 326 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 326) = codeMat 66 := by
      unfold actionA
      rw [step109wc197s10_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 326 * (codeMat 498 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc197s10_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 498 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 40 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 40) = codeMat 16 := by
      unfold actionA
      rw [step109wc197s10_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 498 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 368 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 368 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 368) = codeMat 10 := by
      unfold actionA
      rw [step109wc197s10_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 368 * (codeMat 498 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 256) = codeMat 6 := by
      unfold actionA
      rw [step109wc197s10_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 498 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step109wc197s10_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 498 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact

theorem step109wc197s10Dispatch :
    QuotientRankAtLeast (o197SourceU_wc ⟨10, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 206 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 206) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 206) hP hQ flatW_3 9
      flatSeed_3
  exact quotientRankAtLeast_mono step109wc197s10_contain hAct


private theorem step109wc197s11_QtInv :
    (codeMat 330 : Mat3).transpose⁻¹ = (codeMat 394 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 330 : Mat3).transpose * (codeMat 394 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc197s11_contain :
    (o197SourceU_wc ⟨11, by omega⟩) ≤ actionW (codeMat 84) (codeMat 330) flatW_3 := by
  change spanCodes [258, 128, 66, 32, 16, 10, 4, 1] ≤ actionW (codeMat 84) (codeMat 330) flatW_3
  apply step109wc197_spanCodes_le_of_gens [258, 128, 66, 32, 16, 10, 4, 1]
    (actionW (codeMat 84) (codeMat 330) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 68 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 68 (by decide)
    have hact : actionA (codeMat 84) (codeMat 330) (codeMat 68) = codeMat 258 := by
      unfold actionA
      rw [step109wc197s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 68 * (codeMat 394 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 330) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step109wc197s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 394 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 70 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 70 (by decide)
    have hact : actionA (codeMat 84) (codeMat 330) (codeMat 70) = codeMat 66 := by
      unfold actionA
      rw [step109wc197s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 70 * (codeMat 394 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 84) (codeMat 330) (codeMat 32) = codeMat 32 := by
      unfold actionA
      rw [step109wc197s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 32 * (codeMat 394 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 330) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step109wc197s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 394 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 112 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 112 (by decide)
    have hact : actionA (codeMat 84) (codeMat 330) (codeMat 112) = codeMat 10 := by
      unfold actionA
      rw [step109wc197s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 112 * (codeMat 394 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 330) (codeMat 256) = codeMat 4 := by
      unfold actionA
      rw [step109wc197s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 394 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 330) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step109wc197s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 394 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact

theorem step109wc197s11Dispatch :
    QuotientRankAtLeast (o197SourceU_wc ⟨11, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 330 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 330) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 330) hP hQ flatW_3 9
      flatSeed_3
  exact quotientRankAtLeast_mono step109wc197s11_contain hAct


private theorem step109wc197s12_QtInv :
    (codeMat 330 : Mat3).transpose⁻¹ = (codeMat 394 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 330 : Mat3).transpose * (codeMat 394 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc197s12_contain :
    (o197SourceU_wc ⟨12, by omega⟩) ≤ actionW (codeMat 266) (codeMat 330) flatW_1 := by
  change spanCodes [320, 128, 32, 16, 8, 4, 2, 1] ≤ actionW (codeMat 266) (codeMat 330) flatW_1
  apply step109wc197_spanCodes_le_of_gens [320, 128, 32, 16, 8, 4, 2, 1]
    (actionW (codeMat 266) (codeMat 330) flatW_1)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 128 ∈ flatW_1 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 64, 32, 16, 8, 4, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 266) (codeMat 330) (codeMat 128) = codeMat 320 := by
      unfold actionA
      rw [step109wc197s12_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 128 * (codeMat 394 : Mat3).transpose = codeMat 320
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 64 ∈ flatW_1 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 64, 32, 16, 8, 4, 2, 1] 64 (by decide)
    have hact : actionA (codeMat 266) (codeMat 330) (codeMat 64) = codeMat 128 := by
      unfold actionA
      rw [step109wc197s12_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 64 * (codeMat 394 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 4 ∈ flatW_1 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 64, 32, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 266) (codeMat 330) (codeMat 4) = codeMat 32 := by
      unfold actionA
      rw [step109wc197s12_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 4 * (codeMat 394 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ flatW_1 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 64, 32, 16, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 330) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc197s12_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 394 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 6 ∈ flatW_1 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 64, 32, 16, 8, 4, 2, 1] 6 (by decide)
    have hact : actionA (codeMat 266) (codeMat 330) (codeMat 6) = codeMat 8 := by
      unfold actionA
      rw [step109wc197s12_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 6 * (codeMat 394 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ flatW_1 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 64, 32, 16, 8, 4, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 330) (codeMat 32) = codeMat 4 := by
      unfold actionA
      rw [step109wc197s12_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 394 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ flatW_1 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 64, 32, 16, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 330) (codeMat 8) = codeMat 2 := by
      unfold actionA
      rw [step109wc197s12_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 394 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 48 ∈ flatW_1 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 64, 32, 16, 8, 4, 2, 1] 48 (by decide)
    have hact : actionA (codeMat 266) (codeMat 330) (codeMat 48) = codeMat 1 := by
      unfold actionA
      rw [step109wc197s12_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 48 * (codeMat 394 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc197_codeMat_mem_actionW_of_witness hw hact

theorem step109wc197s12Dispatch :
    QuotientRankAtLeast (o197SourceU_wc ⟨12, by omega⟩) 3 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 330 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 330) flatW_1) 3 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 330) hP hQ flatW_1 3
      flatSeed_1
  exact quotientRankAtLeast_mono step109wc197s12_contain hAct

theorem step109wc197_all_dispatch (i : Fin 13) :
    QuotientRankAtLeast (o197SourceU_wc i) (o197SourceLb_wc i) := by
  fin_cases i
  · exact step109wc197s0Dispatch
  · exact step109wc197s1Dispatch
  · exact step109wc197s2Dispatch
  · exact step109wc197s3Dispatch
  · exact step109wc197s4Dispatch
  · exact step109wc197s5Dispatch
  · exact step109wc197s6Dispatch
  · exact step109wc197s7Dispatch
  · exact step109wc197s8Dispatch
  · exact step109wc197s9Dispatch
  · exact step109wc197s10Dispatch
  · exact step109wc197s11Dispatch
  · exact step109wc197s12Dispatch

theorem step109_orbit197_lb15_wc : QuotientRankAtLeast o197W_wc 15 :=
  o197Lb15_wc step109wc197_all_dispatch

end QiushiMatmul
