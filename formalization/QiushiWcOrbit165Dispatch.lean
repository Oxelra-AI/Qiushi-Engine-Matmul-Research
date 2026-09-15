import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit165Consumer
import QiushiStep99Orbit55Dispatch
import QiushiStep99Orbit56Dispatch
import QiushiWcOrbit78Dispatch
import QiushiStep99Orbit82Dispatch
import QiushiOrbit41FP
import QiushiMonoOrbit53From14
import QiushiMonoOrbit44From14
import QiushiOrbit14FP
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc165_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc165_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

private def step109wc165s0SrcT : Submodule F2 Mat3 := spanCodes [272, 128, 66, 34, 8, 1]

private theorem step109wc165s0SrcT_lb : QuotientRankAtLeast step109wc165s0SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step99_orbit55_lb14_unconditional
  have hle : step109wc165s0SrcT ≤ transposeW o55W := by
    unfold step109wc165s0SrcT transposeW
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

private theorem step109wc165s0_QtInv :
    (codeMat 156 : Mat3).transpose⁻¹ = (codeMat 102 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 156 : Mat3).transpose * (codeMat 102 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc165s0_contain :
    (o165SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 93) (codeMat 156) step109wc165s0SrcT := by
  change spanCodes [260, 68, 36, 20, 10, 1] ≤ actionW (codeMat 93) (codeMat 156) step109wc165s0SrcT
  apply step109wc165_spanCodes_le_of_gens [260, 68, 36, 20, 10, 1]
    (actionW (codeMat 93) (codeMat 156) step109wc165s0SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 1 ∈ step109wc165s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 1 (by decide)
    have hact : actionA (codeMat 93) (codeMat 156) (codeMat 1) = codeMat 260 := by
      unfold actionA
      rw [step109wc165s0_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 1 * (codeMat 102 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 194 ∈ step109wc165s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 194 (by decide)
    have hact : actionA (codeMat 93) (codeMat 156) (codeMat 194) = codeMat 68 := by
      unfold actionA
      rw [step109wc165s0_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 194 * (codeMat 102 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ step109wc165s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 8 (by decide)
    have hact : actionA (codeMat 93) (codeMat 156) (codeMat 8) = codeMat 36 := by
      unfold actionA
      rw [step109wc165s0_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 8 * (codeMat 102 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 496 ∈ step109wc165s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 496 (by decide)
    have hact : actionA (codeMat 93) (codeMat 156) (codeMat 496) = codeMat 20 := by
      unfold actionA
      rw [step109wc165s0_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 496 * (codeMat 102 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 272 ∈ step109wc165s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 272 (by decide)
    have hact : actionA (codeMat 93) (codeMat 156) (codeMat 272) = codeMat 10 := by
      unfold actionA
      rw [step109wc165s0_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 272 * (codeMat 102 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ step109wc165s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 128 (by decide)
    have hact : actionA (codeMat 93) (codeMat 156) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc165s0_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 128 * (codeMat 102 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact

theorem step109wc165s0Dispatch :
    QuotientRankAtLeast (o165SourceU_wc ⟨0, by omega⟩) 14 := by
  have hP : Invertible (codeMat 93 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 156 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 93) (codeMat 156) step109wc165s0SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 93) (codeMat 156) hP hQ step109wc165s0SrcT 14
      step109wc165s0SrcT_lb
  exact quotientRankAtLeast_mono step109wc165s0_contain hAct

private def step109wc165s1SrcT : Submodule F2 Mat3 := spanCodes [272, 128, 66, 34, 8, 1]

private theorem step109wc165s1SrcT_lb : QuotientRankAtLeast step109wc165s1SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step99_orbit55_lb14_unconditional
  have hle : step109wc165s1SrcT ≤ transposeW o55W := by
    unfold step109wc165s1SrcT transposeW
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

private theorem step109wc165s1_QtInv :
    (codeMat 188 : Mat3).transpose⁻¹ = (codeMat 103 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 188 : Mat3).transpose * (codeMat 103 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc165s1_contain :
    (o165SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 95) (codeMat 188) step109wc165s1SrcT := by
  change spanCodes [262, 70, 38, 20, 10, 1] ≤ actionW (codeMat 95) (codeMat 188) step109wc165s1SrcT
  apply step109wc165_spanCodes_le_of_gens [262, 70, 38, 20, 10, 1]
    (actionW (codeMat 95) (codeMat 188) step109wc165s1SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 347 ∈ step109wc165s1SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 347 (by decide)
    have hact : actionA (codeMat 95) (codeMat 188) (codeMat 347) = codeMat 262 := by
      unfold actionA
      rw [step109wc165s1_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 347 * (codeMat 103 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 338 ∈ step109wc165s1SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 338 (by decide)
    have hact : actionA (codeMat 95) (codeMat 188) (codeMat 338) = codeMat 70 := by
      unfold actionA
      rw [step109wc165s1_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 338 * (codeMat 103 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 408 ∈ step109wc165s1SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 408 (by decide)
    have hact : actionA (codeMat 95) (codeMat 188) (codeMat 408) = codeMat 38 := by
      unfold actionA
      rw [step109wc165s1_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 408 * (codeMat 103 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 368 ∈ step109wc165s1SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 368 (by decide)
    have hact : actionA (codeMat 95) (codeMat 188) (codeMat 368) = codeMat 20 := by
      unfold actionA
      rw [step109wc165s1_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 368 * (codeMat 103 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 272 ∈ step109wc165s1SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 272 (by decide)
    have hact : actionA (codeMat 95) (codeMat 188) (codeMat 272) = codeMat 10 := by
      unfold actionA
      rw [step109wc165s1_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 272 * (codeMat 103 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ step109wc165s1SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 128 (by decide)
    have hact : actionA (codeMat 95) (codeMat 188) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc165s1_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 128 * (codeMat 103 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact

theorem step109wc165s1Dispatch :
    QuotientRankAtLeast (o165SourceU_wc ⟨1, by omega⟩) 14 := by
  have hP : Invertible (codeMat 95 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 188 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 95) (codeMat 188) step109wc165s1SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 95) (codeMat 188) hP hQ step109wc165s1SrcT 14
      step109wc165s1SrcT_lb
  exact quotientRankAtLeast_mono step109wc165s1_contain hAct


private theorem step109wc165s2_QtInv :
    (codeMat 372 : Mat3).transpose⁻¹ = (codeMat 93 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 372 : Mat3).transpose * (codeMat 93 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc165s2_contain :
    (o165SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 92) (codeMat 372) o56W := by
  change spanCodes [288, 128, 96, 20, 10, 1] ≤ actionW (codeMat 92) (codeMat 372) o56W
  apply step109wc165_spanCodes_le_of_gens [288, 128, 96, 20, 10, 1]
    (actionW (codeMat 92) (codeMat 372) o56W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 511 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 511 (by decide)
    have hact : actionA (codeMat 92) (codeMat 372) (codeMat 511) = codeMat 288 := by
      unfold actionA
      rw [step109wc165s2_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 511 * (codeMat 93 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 92) (codeMat 372) (codeMat 2) = codeMat 128 := by
      unfold actionA
      rw [step109wc165s2_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 2 * (codeMat 93 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 508 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 508 (by decide)
    have hact : actionA (codeMat 92) (codeMat 372) (codeMat 508) = codeMat 96 := by
      unfold actionA
      rw [step109wc165s2_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 508 * (codeMat 93 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 336 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 336 (by decide)
    have hact : actionA (codeMat 92) (codeMat 372) (codeMat 336) = codeMat 20 := by
      unfold actionA
      rw [step109wc165s2_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 336 * (codeMat 93 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 416 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 416 (by decide)
    have hact : actionA (codeMat 92) (codeMat 372) (codeMat 416) = codeMat 10 := by
      unfold actionA
      rw [step109wc165s2_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 416 * (codeMat 93 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 92) (codeMat 372) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc165s2_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 256 * (codeMat 93 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact

theorem step109wc165s2Dispatch :
    QuotientRankAtLeast (o165SourceU_wc ⟨2, by omega⟩) 14 := by
  have hP : Invertible (codeMat 92 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 372 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 92) (codeMat 372) o56W) 14 :=
    @quotientRankAtLeast_action (codeMat 92) (codeMat 372) hP hQ o56W 14
      step99_orbit56_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc165s2_contain hAct


private theorem step109wc165s3_QtInv :
    (codeMat 309 : Mat3).transpose⁻¹ = (codeMat 309 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 309 : Mat3).transpose * (codeMat 309 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc165s3_contain :
    (o165SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 345) (codeMat 309) o78W_wc := by
  change spanCodes [288, 130, 96, 20, 10, 1] ≤ actionW (codeMat 345) (codeMat 309) o78W_wc
  apply step109wc165_spanCodes_le_of_gens [288, 130, 96, 20, 10, 1]
    (actionW (codeMat 345) (codeMat 309) o78W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 504 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 504 (by decide)
    have hact : actionA (codeMat 345) (codeMat 309) (codeMat 504) = codeMat 288 := by
      unfold actionA
      rw [step109wc165s3_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 504 * (codeMat 309 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 128 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 345) (codeMat 309) (codeMat 128) = codeMat 130 := by
      unfold actionA
      rw [step109wc165s3_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 128 * (codeMat 309 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 126 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 126 (by decide)
    have hact : actionA (codeMat 345) (codeMat 309) (codeMat 126) = codeMat 96 := by
      unfold actionA
      rw [step109wc165s3_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 126 * (codeMat 309 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 21 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 21 (by decide)
    have hact : actionA (codeMat 345) (codeMat 309) (codeMat 21) = codeMat 20 := by
      unfold actionA
      rw [step109wc165s3_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 21 * (codeMat 309 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 11 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 345) (codeMat 309) (codeMat 11) = codeMat 10 := by
      unfold actionA
      rw [step109wc165s3_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 11 * (codeMat 309 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 345) (codeMat 309) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc165s3_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 1 * (codeMat 309 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact

theorem step109wc165s3Dispatch :
    QuotientRankAtLeast (o165SourceU_wc ⟨3, by omega⟩) 14 := by
  have hP : Invertible (codeMat 345 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 309 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 345) (codeMat 309) o78W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 345) (codeMat 309) hP hQ o78W_wc 14
      step109_orbit78_lb14_wc
  exact quotientRankAtLeast_mono step109wc165s3_contain hAct


private theorem step109wc165s4_QtInv :
    (codeMat 116 : Mat3).transpose⁻¹ = (codeMat 92 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 116 : Mat3).transpose * (codeMat 92 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc165s4_contain :
    (o165SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 94) (codeMat 116) o56W := by
  change spanCodes [288, 132, 96, 20, 10, 1] ≤ actionW (codeMat 94) (codeMat 116) o56W
  apply step109wc165_spanCodes_le_of_gens [288, 132, 96, 20, 10, 1]
    (actionW (codeMat 94) (codeMat 116) o56W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 3 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 94) (codeMat 116) (codeMat 3) = codeMat 288 := by
      unfold actionA
      rw [step109wc165s4_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 3 * (codeMat 92 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 82 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 82 (by decide)
    have hact : actionA (codeMat 94) (codeMat 116) (codeMat 82) = codeMat 132 := by
      unfold actionA
      rw [step109wc165s4_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 82 * (codeMat 92 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 508 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 508 (by decide)
    have hact : actionA (codeMat 94) (codeMat 116) (codeMat 508) = codeMat 96 := by
      unfold actionA
      rw [step109wc165s4_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 508 * (codeMat 92 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 80 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 94) (codeMat 116) (codeMat 80) = codeMat 20 := by
      unfold actionA
      rw [step109wc165s4_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 80 * (codeMat 92 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 416 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 416 (by decide)
    have hact : actionA (codeMat 94) (codeMat 116) (codeMat 416) = codeMat 10 := by
      unfold actionA
      rw [step109wc165s4_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 416 * (codeMat 92 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 94) (codeMat 116) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc165s4_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 256 * (codeMat 92 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact

theorem step109wc165s4Dispatch :
    QuotientRankAtLeast (o165SourceU_wc ⟨4, by omega⟩) 14 := by
  have hP : Invertible (codeMat 94 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 116 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 94) (codeMat 116) o56W) 14 :=
    @quotientRankAtLeast_action (codeMat 94) (codeMat 116) hP hQ o56W 14
      step99_orbit56_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc165s4_contain hAct


private theorem step109wc165s5_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = (codeMat 305 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * (codeMat 305 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc165s5_contain :
    (o165SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 473) (codeMat 305) o78W_wc := by
  change spanCodes [288, 134, 96, 20, 10, 1] ≤ actionW (codeMat 473) (codeMat 305) o78W_wc
  apply step109wc165_spanCodes_le_of_gens [288, 134, 96, 20, 10, 1]
    (actionW (codeMat 473) (codeMat 305) o78W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 390 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 390 (by decide)
    have hact : actionA (codeMat 473) (codeMat 305) (codeMat 390) = codeMat 288 := by
      unfold actionA
      rw [step109wc165s5_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 390 * (codeMat 305 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 148 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 148 (by decide)
    have hact : actionA (codeMat 473) (codeMat 305) (codeMat 148) = codeMat 134 := by
      unfold actionA
      rw [step109wc165s5_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 148 * (codeMat 305 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 126 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 126 (by decide)
    have hact : actionA (codeMat 473) (codeMat 305) (codeMat 126) = codeMat 96 := by
      unfold actionA
      rw [step109wc165s5_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 126 * (codeMat 305 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 20 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 20 (by decide)
    have hact : actionA (codeMat 473) (codeMat 305) (codeMat 20) = codeMat 20 := by
      unfold actionA
      rw [step109wc165s5_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 20 * (codeMat 305 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 11 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 473) (codeMat 305) (codeMat 11) = codeMat 10 := by
      unfold actionA
      rw [step109wc165s5_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 11 * (codeMat 305 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 473) (codeMat 305) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc165s5_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 1 * (codeMat 305 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact

theorem step109wc165s5Dispatch :
    QuotientRankAtLeast (o165SourceU_wc ⟨5, by omega⟩) 14 := by
  have hP : Invertible (codeMat 473 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 473) (codeMat 305) o78W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 473) (codeMat 305) hP hQ o78W_wc 14
      step109_orbit78_lb14_wc
  exact quotientRankAtLeast_mono step109wc165s5_contain hAct


private theorem step109wc165s6_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc165s6_contain :
    (o165SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 337) (codeMat 273) o82W := by
  change spanCodes [288, 162, 96, 20, 10, 1] ≤ actionW (codeMat 337) (codeMat 273) o82W
  apply step109wc165_spanCodes_le_of_gens [288, 162, 96, 20, 10, 1]
    (actionW (codeMat 337) (codeMat 273) o82W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 292 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 292 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 292) = codeMat 288 := by
      unfold actionA
      rw [step109wc165s6_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 292 * (codeMat 273 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 160) = codeMat 162 := by
      unfold actionA
      rw [step109wc165s6_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 160 * (codeMat 273 : Mat3).transpose = codeMat 162
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 97 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 97 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 97) = codeMat 96 := by
      unfold actionA
      rw [step109wc165s6_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 97 * (codeMat 273 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 20 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 20 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 20) = codeMat 20 := by
      unfold actionA
      rw [step109wc165s6_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 20 * (codeMat 273 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step109wc165s6_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 10 * (codeMat 273 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 337) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc165s6_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact

theorem step109wc165s6Dispatch :
    QuotientRankAtLeast (o165SourceU_wc ⟨6, by omega⟩) 14 := by
  have hP : Invertible (codeMat 337 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 337) (codeMat 273) o82W) 14 :=
    @quotientRankAtLeast_action (codeMat 337) (codeMat 273) hP hQ o82W 14
      step99_orbit82_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc165s6_contain hAct


private theorem step109wc165s7_QtInv :
    (codeMat 277 : Mat3).transpose⁻¹ = (codeMat 277 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 277 : Mat3).transpose * (codeMat 277 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc165s7_contain :
    (o165SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 465) (codeMat 277) o82W := by
  change spanCodes [288, 164, 96, 20, 10, 1] ≤ actionW (codeMat 465) (codeMat 277) o82W
  apply step109wc165_spanCodes_le_of_gens [288, 164, 96, 20, 10, 1]
    (actionW (codeMat 465) (codeMat 277) o82W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 325 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 325 (by decide)
    have hact : actionA (codeMat 465) (codeMat 277) (codeMat 325) = codeMat 288 := by
      unfold actionA
      rw [step109wc165s7_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 325 * (codeMat 277 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 191 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 191 (by decide)
    have hact : actionA (codeMat 465) (codeMat 277) (codeMat 191) = codeMat 164 := by
      unfold actionA
      rw [step109wc165s7_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 191 * (codeMat 277 : Mat3).transpose = codeMat 164
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 97 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 97 (by decide)
    have hact : actionA (codeMat 465) (codeMat 277) (codeMat 97) = codeMat 96 := by
      unfold actionA
      rw [step109wc165s7_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 97 * (codeMat 277 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 21 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 21 (by decide)
    have hact : actionA (codeMat 465) (codeMat 277) (codeMat 21) = codeMat 20 := by
      unfold actionA
      rw [step109wc165s7_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 21 * (codeMat 277 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 10 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 465) (codeMat 277) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step109wc165s7_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 10 * (codeMat 277 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 465) (codeMat 277) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc165s7_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 1 * (codeMat 277 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact

theorem step109wc165s7Dispatch :
    QuotientRankAtLeast (o165SourceU_wc ⟨7, by omega⟩) 14 := by
  have hP : Invertible (codeMat 465 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 277 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 465) (codeMat 277) o82W) 14 :=
    @quotientRankAtLeast_action (codeMat 465) (codeMat 277) hP hQ o82W 14
      step99_orbit82_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc165s7_contain hAct

private def step109wc165s8SrcT : Submodule F2 Mat3 := spanCodes [288, 128, 84, 8, 2, 1]

private theorem step109wc165s8SrcT_lb : QuotientRankAtLeast step109wc165s8SrcT 12 := by
  have ht := quotientRankAtLeast_transpose orbit41_lb12
  have hle : step109wc165s8SrcT ≤ transposeW orbit41W := by
    unfold step109wc165s8SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4 | h5
    · subst h0
      show codeMat 288 ∈ Submodule.map transposeLinearMap orbit41W
      exact ⟨codeMat 384, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 384] 384 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 128 ∈ Submodule.map transposeLinearMap orbit41W
      exact ⟨codeMat 32, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 384] 32 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 84 ∈ Submodule.map transposeLinearMap orbit41W
      exact ⟨codeMat 84, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 384] 84 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 8 ∈ Submodule.map transposeLinearMap orbit41W
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 384] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 2 ∈ Submodule.map transposeLinearMap orbit41W
      exact ⟨codeMat 8, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 384] 8 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h5
      show codeMat 1 ∈ Submodule.map transposeLinearMap orbit41W
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 384] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc165s8_QtInv :
    (codeMat 141 : Mat3).transpose⁻¹ = (codeMat 226 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 141 : Mat3).transpose * (codeMat 226 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc165s8_contain :
    (o165SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 305) (codeMat 141) step109wc165s8SrcT := by
  change spanCodes [288, 96, 16, 10, 4, 1] ≤ actionW (codeMat 305) (codeMat 141) step109wc165s8SrcT
  apply step109wc165_spanCodes_le_of_gens [288, 96, 16, 10, 4, 1]
    (actionW (codeMat 305) (codeMat 141) step109wc165s8SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 8 ∈ step109wc165s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 128, 84, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 305) (codeMat 141) (codeMat 8) = codeMat 288 := by
      unfold actionA
      rw [step109wc165s8_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 8 * (codeMat 226 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 136 ∈ step109wc165s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 128, 84, 8, 2, 1] 136 (by decide)
    have hact : actionA (codeMat 305) (codeMat 141) (codeMat 136) = codeMat 96 := by
      unfold actionA
      rw [step109wc165s8_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 136 * (codeMat 226 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 288 ∈ step109wc165s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 128, 84, 8, 2, 1] 288 (by decide)
    have hact : actionA (codeMat 305) (codeMat 141) (codeMat 288) = codeMat 16 := by
      unfold actionA
      rw [step109wc165s8_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 288 * (codeMat 226 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 220 ∈ step109wc165s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 128, 84, 8, 2, 1] 220 (by decide)
    have hact : actionA (codeMat 305) (codeMat 141) (codeMat 220) = codeMat 10 := by
      unfold actionA
      rw [step109wc165s8_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 220 * (codeMat 226 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ step109wc165s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 128, 84, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 305) (codeMat 141) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step109wc165s8_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 1 * (codeMat 226 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ step109wc165s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 128, 84, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 305) (codeMat 141) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step109wc165s8_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 3 * (codeMat 226 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact

theorem step109wc165s8Dispatch :
    QuotientRankAtLeast (o165SourceU_wc ⟨8, by omega⟩) 12 := by
  have hP : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 141 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 305) (codeMat 141) step109wc165s8SrcT) 12 :=
    @quotientRankAtLeast_action (codeMat 305) (codeMat 141) hP hQ step109wc165s8SrcT 12
      step109wc165s8SrcT_lb
  exact quotientRankAtLeast_mono step109wc165s8_contain hAct


private theorem step109wc165s9_QtInv :
    (codeMat 421 : Mat3).transpose⁻¹ = (codeMat 179 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 421 : Mat3).transpose * (codeMat 179 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc165s9_contain :
    (o165SourceU_wc ⟨9, by omega⟩) ≤ actionW (codeMat 281) (codeMat 421) o53W_mono := by
  change spanCodes [288, 96, 18, 10, 6, 1] ≤ actionW (codeMat 281) (codeMat 421) o53W_mono
  apply step109wc165_spanCodes_le_of_gens [288, 96, 18, 10, 6, 1]
    (actionW (codeMat 281) (codeMat 421) o53W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 511 ∈ o53W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [384, 80, 32, 12, 2, 1] 511 (by decide)
    have hact : actionA (codeMat 281) (codeMat 421) (codeMat 511) = codeMat 288 := by
      unfold actionA
      rw [step109wc165s9_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 511 * (codeMat 179 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 127 ∈ o53W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [384, 80, 32, 12, 2, 1] 127 (by decide)
    have hact : actionA (codeMat 281) (codeMat 421) (codeMat 127) = codeMat 96 := by
      unfold actionA
      rw [step109wc165s9_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 127 * (codeMat 179 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ o53W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [384, 80, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 281) (codeMat 421) (codeMat 32) = codeMat 18 := by
      unfold actionA
      rw [step109wc165s9_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 32 * (codeMat 179 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 13 ∈ o53W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [384, 80, 32, 12, 2, 1] 13 (by decide)
    have hact : actionA (codeMat 281) (codeMat 421) (codeMat 13) = codeMat 10 := by
      unfold actionA
      rw [step109wc165s9_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 13 * (codeMat 179 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o53W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [384, 80, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 281) (codeMat 421) (codeMat 3) = codeMat 6 := by
      unfold actionA
      rw [step109wc165s9_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 3 * (codeMat 179 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o53W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [384, 80, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 281) (codeMat 421) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc165s9_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 1 * (codeMat 179 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact

theorem step109wc165s9Dispatch :
    QuotientRankAtLeast (o165SourceU_wc ⟨9, by omega⟩) 12 := by
  have hP : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 421 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 281) (codeMat 421) o53W_mono) 12 :=
    @quotientRankAtLeast_action (codeMat 281) (codeMat 421) hP hQ o53W_mono 12
      orbit53_lb12_mono
  exact quotientRankAtLeast_mono step109wc165s9_contain hAct

private def step109wc165s10SrcT : Submodule F2 Mat3 := spanCodes [272, 128, 96, 8, 2, 1]

private theorem step109wc165s10SrcT_lb : QuotientRankAtLeast step109wc165s10SrcT 12 := by
  have ht := quotientRankAtLeast_transpose orbit44_lb12_mono
  have hle : step109wc165s10SrcT ≤ transposeW o44W_mono := by
    unfold step109wc165s10SrcT transposeW
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

private theorem step109wc165s10_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc165s10_contain :
    (o165SourceU_wc ⟨10, by omega⟩) ≤ actionW (codeMat 84) (codeMat 140) step109wc165s10SrcT := by
  change spanCodes [256, 64, 32, 20, 10, 1] ≤ actionW (codeMat 84) (codeMat 140) step109wc165s10SrcT
  apply step109wc165_spanCodes_le_of_gens [256, 64, 32, 20, 10, 1]
    (actionW (codeMat 84) (codeMat 140) step109wc165s10SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 1 ∈ step109wc165s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 96, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc165s10_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ step109wc165s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 96, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 2) = codeMat 64 := by
      unfold actionA
      rw [step109wc165s10_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ step109wc165s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 96, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc165s10_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 96 ∈ step109wc165s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 96, 8, 2, 1] 96 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 96) = codeMat 20 := by
      unfold actionA
      rw [step109wc165s10_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 96 * (codeMat 98 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 272 ∈ step109wc165s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 96, 8, 2, 1] 272 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 272) = codeMat 10 := by
      unfold actionA
      rw [step109wc165s10_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 272 * (codeMat 98 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ step109wc165s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 96, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 140) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc165s10_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact

theorem step109wc165s10Dispatch :
    QuotientRankAtLeast (o165SourceU_wc ⟨10, by omega⟩) 12 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 140) step109wc165s10SrcT) 12 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 140) hP hQ step109wc165s10SrcT 12
      step109wc165s10SrcT_lb
  exact quotientRankAtLeast_mono step109wc165s10_contain hAct

private def step109wc165s11SrcT : Submodule F2 Mat3 := spanCodes [272, 128, 96, 8, 2, 1]

private theorem step109wc165s11SrcT_lb : QuotientRankAtLeast step109wc165s11SrcT 12 := by
  have ht := quotientRankAtLeast_transpose orbit44_lb12_mono
  have hle : step109wc165s11SrcT ≤ transposeW o44W_mono := by
    unfold step109wc165s11SrcT transposeW
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

private theorem step109wc165s11_QtInv :
    (codeMat 172 : Mat3).transpose⁻¹ = (codeMat 99 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 172 : Mat3).transpose * (codeMat 99 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc165s11_contain :
    (o165SourceU_wc ⟨11, by omega⟩) ≤ actionW (codeMat 86) (codeMat 172) step109wc165s11SrcT := by
  change spanCodes [258, 66, 34, 20, 10, 1] ≤ actionW (codeMat 86) (codeMat 172) step109wc165s11SrcT
  apply step109wc165_spanCodes_le_of_gens [258, 66, 34, 20, 10, 1]
    (actionW (codeMat 86) (codeMat 172) step109wc165s11SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 283 ∈ step109wc165s11SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 96, 8, 2, 1] 283 (by decide)
    have hact : actionA (codeMat 86) (codeMat 172) (codeMat 283) = codeMat 258 := by
      unfold actionA
      rw [step109wc165s11_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 283 * (codeMat 99 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 274 ∈ step109wc165s11SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 96, 8, 2, 1] 274 (by decide)
    have hact : actionA (codeMat 86) (codeMat 172) (codeMat 274) = codeMat 66 := by
      unfold actionA
      rw [step109wc165s11_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 274 * (codeMat 99 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 280 ∈ step109wc165s11SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 96, 8, 2, 1] 280 (by decide)
    have hact : actionA (codeMat 86) (codeMat 172) (codeMat 280) = codeMat 34 := by
      unfold actionA
      rw [step109wc165s11_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 280 * (codeMat 99 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 224 ∈ step109wc165s11SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 96, 8, 2, 1] 224 (by decide)
    have hact : actionA (codeMat 86) (codeMat 172) (codeMat 224) = codeMat 20 := by
      unfold actionA
      rw [step109wc165s11_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 224 * (codeMat 99 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 272 ∈ step109wc165s11SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 96, 8, 2, 1] 272 (by decide)
    have hact : actionA (codeMat 86) (codeMat 172) (codeMat 272) = codeMat 10 := by
      unfold actionA
      rw [step109wc165s11_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 272 * (codeMat 99 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ step109wc165s11SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 96, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 86) (codeMat 172) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc165s11_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 128 * (codeMat 99 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact

theorem step109wc165s11Dispatch :
    QuotientRankAtLeast (o165SourceU_wc ⟨11, by omega⟩) 12 := by
  have hP : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 172 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 86) (codeMat 172) step109wc165s11SrcT) 12 :=
    @quotientRankAtLeast_action (codeMat 86) (codeMat 172) hP hQ step109wc165s11SrcT 12
      step109wc165s11SrcT_lb
  exact quotientRankAtLeast_mono step109wc165s11_contain hAct


private theorem step109wc165s12_QtInv :
    (codeMat 279 : Mat3).transpose⁻¹ = (codeMat 279 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 279 : Mat3).transpose * (codeMat 279 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc165s12_contain :
    (o165SourceU_wc ⟨12, by omega⟩) ≤ actionW (codeMat 273) (codeMat 279) orbit14W := by
  change spanCodes [288, 160, 96, 20, 8, 2, 1] ≤ actionW (codeMat 273) (codeMat 279) orbit14W
  apply step109wc165_spanCodes_le_of_gens [288, 160, 96, 20, 8, 2, 1]
    (actionW (codeMat 273) (codeMat 279) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 273) (codeMat 279) (codeMat 360) = codeMat 288 := by
      unfold actionA
      rw [step109wc165s12_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 360 * (codeMat 279 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 232 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 232 (by decide)
    have hact : actionA (codeMat 273) (codeMat 279) (codeMat 232) = codeMat 160 := by
      unfold actionA
      rw [step109wc165s12_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 232 * (codeMat 279 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 104 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 104 (by decide)
    have hact : actionA (codeMat 273) (codeMat 279) (codeMat 104) = codeMat 96 := by
      unfold actionA
      rw [step109wc165s12_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 104 * (codeMat 279 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 29 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 29 (by decide)
    have hact : actionA (codeMat 273) (codeMat 279) (codeMat 29) = codeMat 20 := by
      unfold actionA
      rw [step109wc165s12_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 29 * (codeMat 279 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 279) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc165s12_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 279 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 273) (codeMat 279) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc165s12_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 3 * (codeMat 279 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 279) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc165s12_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 279 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact

theorem step109wc165s12Dispatch :
    QuotientRankAtLeast (o165SourceU_wc ⟨12, by omega⟩) 12 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 279 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 279) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 279) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc165s12_contain hAct


private theorem step109wc165s13_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = (codeMat 275 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * (codeMat 275 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc165s13_contain :
    (o165SourceU_wc ⟨13, by omega⟩) ≤ actionW (codeMat 401) (codeMat 275) orbit14W := by
  change spanCodes [288, 164, 96, 20, 8, 2, 1] ≤ actionW (codeMat 401) (codeMat 275) orbit14W
  apply step109wc165_spanCodes_le_of_gens [288, 164, 96, 20, 8, 2, 1]
    (actionW (codeMat 401) (codeMat 275) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 401) (codeMat 275) (codeMat 256) = codeMat 288 := by
      unfold actionA
      rw [step109wc165s13_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 256 * (codeMat 275 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 252 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 252 (by decide)
    have hact : actionA (codeMat 401) (codeMat 275) (codeMat 252) = codeMat 164 := by
      unfold actionA
      rw [step109wc165s13_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 252 * (codeMat 275 : Mat3).transpose = codeMat 164
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 104 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 104 (by decide)
    have hact : actionA (codeMat 401) (codeMat 275) (codeMat 104) = codeMat 96 := by
      unfold actionA
      rw [step109wc165s13_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 104 * (codeMat 275 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 28 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 28 (by decide)
    have hact : actionA (codeMat 401) (codeMat 275) (codeMat 28) = codeMat 20 := by
      unfold actionA
      rw [step109wc165s13_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 28 * (codeMat 275 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 401) (codeMat 275) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc165s13_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 8 * (codeMat 275 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 401) (codeMat 275) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc165s13_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 3 * (codeMat 275 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 401) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc165s13_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 1 * (codeMat 275 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact

theorem step109wc165s13Dispatch :
    QuotientRankAtLeast (o165SourceU_wc ⟨13, by omega⟩) 12 := by
  have hP : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 401) (codeMat 275) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 401) (codeMat 275) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc165s13_contain hAct


private theorem step109wc165s14_QtInv :
    (codeMat 254 : Mat3).transpose⁻¹ = (codeMat 443 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 254 : Mat3).transpose * (codeMat 443 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc165s14_contain :
    (o165SourceU_wc ⟨14, by omega⟩) ≤ actionW (codeMat 102) (codeMat 254) flatW_15 := by
  change spanCodes [288, 160, 96, 18, 10, 6, 1] ≤ actionW (codeMat 102) (codeMat 254) flatW_15
  apply step109wc165_spanCodes_le_of_gens [288, 160, 96, 18, 10, 6, 1]
    (actionW (codeMat 102) (codeMat 254) flatW_15)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 3 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 102) (codeMat 254) (codeMat 3) = codeMat 288 := by
      unfold actionA
      rw [step109wc165s14_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 3 * (codeMat 443 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 35 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 35 (by decide)
    have hact : actionA (codeMat 102) (codeMat 254) (codeMat 35) = codeMat 160 := by
      unfold actionA
      rw [step109wc165s14_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 35 * (codeMat 443 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 43 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 43 (by decide)
    have hact : actionA (codeMat 102) (codeMat 254) (codeMat 43) = codeMat 96 := by
      unfold actionA
      rw [step109wc165s14_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 43 * (codeMat 443 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 511 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 511 (by decide)
    have hact : actionA (codeMat 102) (codeMat 254) (codeMat 511) = codeMat 18 := by
      unfold actionA
      rw [step109wc165s14_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 511 * (codeMat 443 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 502 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 502 (by decide)
    have hact : actionA (codeMat 102) (codeMat 254) (codeMat 502) = codeMat 10 := by
      unfold actionA
      rw [step109wc165s14_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 502 * (codeMat 443 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 102) (codeMat 254) (codeMat 256) = codeMat 6 := by
      unfold actionA
      rw [step109wc165s14_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 256 * (codeMat 443 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 384 ∈ flatW_15 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 102) (codeMat 254) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step109wc165s14_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 384 * (codeMat 443 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc165_codeMat_mem_actionW_of_witness hw hact

theorem step109wc165s14Dispatch :
    QuotientRankAtLeast (o165SourceU_wc ⟨14, by omega⟩) 9 := by
  have hP : Invertible (codeMat 102 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 254 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 102) (codeMat 254) flatW_15) 9 :=
    @quotientRankAtLeast_action (codeMat 102) (codeMat 254) hP hQ flatW_15 9
      flatSeed_15
  exact quotientRankAtLeast_mono step109wc165s14_contain hAct

theorem step109wc165_all_dispatch (i : Fin 15) :
    QuotientRankAtLeast (o165SourceU_wc i) (o165SourceLb_wc i) := by
  fin_cases i
  · exact step109wc165s0Dispatch
  · exact step109wc165s1Dispatch
  · exact step109wc165s2Dispatch
  · exact step109wc165s3Dispatch
  · exact step109wc165s4Dispatch
  · exact step109wc165s5Dispatch
  · exact step109wc165s6Dispatch
  · exact step109wc165s7Dispatch
  · exact step109wc165s8Dispatch
  · exact step109wc165s9Dispatch
  · exact step109wc165s10Dispatch
  · exact step109wc165s11Dispatch
  · exact step109wc165s12Dispatch
  · exact step109wc165s13Dispatch
  · exact step109wc165s14Dispatch

theorem step109_orbit165_lb15_wc : QuotientRankAtLeast o165W_wc 15 :=
  o165Lb15_wc step109wc165_all_dispatch

end QiushiMatmul
