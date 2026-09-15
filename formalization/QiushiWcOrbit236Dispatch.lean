import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit236Consumer
import QiushiStep99Orbit76Dispatch
import QiushiStep99Orbit77Dispatch
import QiushiWcOrbit80Dispatch
import QiushiStep99Orbit56Dispatch
import QiushiWcOrbit78Dispatch
import QiushiWcOrbit57Dispatch
import QiushiStep99Orbit82Dispatch
import QiushiWcOrbit79Dispatch
import QiushiOrbit14FP

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc236_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc236_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc236s0_QtInv :
    (codeMat 468 : Mat3).transpose⁻¹ = (codeMat 87 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 468 : Mat3).transpose * (codeMat 87 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc236s0_contain :
    (o236SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 359) (codeMat 468) o76W := by
  change spanCodes [262, 130, 96, 20, 10, 1] ≤ actionW (codeMat 359) (codeMat 468) o76W
  apply step109wc236_spanCodes_le_of_gens [262, 130, 96, 20, 10, 1]
    (actionW (codeMat 359) (codeMat 468) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 240 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 240 (by decide)
    have hact : actionA (codeMat 359) (codeMat 468) (codeMat 240) = codeMat 262 := by
      unfold actionA
      rw [step109wc236s0_QtInv]
      show (codeMat 359 : Mat3).transpose * codeMat 240 * (codeMat 87 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 384 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 384 (by decide)
    have hact : actionA (codeMat 359) (codeMat 468) (codeMat 384) = codeMat 130 := by
      unfold actionA
      rw [step109wc236s0_QtInv]
      show (codeMat 359 : Mat3).transpose * codeMat 384 * (codeMat 87 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 357 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 357 (by decide)
    have hact : actionA (codeMat 359) (codeMat 468) (codeMat 357) = codeMat 96 := by
      unfold actionA
      rw [step109wc236s0_QtInv]
      show (codeMat 359 : Mat3).transpose * codeMat 357 * (codeMat 87 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 238 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 238 (by decide)
    have hact : actionA (codeMat 359) (codeMat 468) (codeMat 238) = codeMat 20 := by
      unfold actionA
      rw [step109wc236s0_QtInv]
      show (codeMat 359 : Mat3).transpose * codeMat 238 * (codeMat 87 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 180 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 180 (by decide)
    have hact : actionA (codeMat 359) (codeMat 468) (codeMat 180) = codeMat 10 := by
      unfold actionA
      rw [step109wc236s0_QtInv]
      show (codeMat 359 : Mat3).transpose * codeMat 180 * (codeMat 87 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 288 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 359) (codeMat 468) (codeMat 288) = codeMat 1 := by
      unfold actionA
      rw [step109wc236s0_QtInv]
      show (codeMat 359 : Mat3).transpose * codeMat 288 * (codeMat 87 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact

theorem step109wc236s0Dispatch :
    QuotientRankAtLeast (o236SourceU_wc ⟨0, by omega⟩) 15 := by
  have hP : Invertible (codeMat 359 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 468 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 359) (codeMat 468) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 359) (codeMat 468) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc236s0_contain hAct

private def step109wc236s1SrcT : Submodule F2 Mat3 := spanCodes [272, 132, 80, 32, 10, 1]

private theorem step109wc236s1SrcT_lb : QuotientRankAtLeast step109wc236s1SrcT 15 := by
  have ht := quotientRankAtLeast_transpose step99_orbit77_lb15_unconditional
  have hle : step109wc236s1SrcT ≤ transposeW o77W := by
    unfold step109wc236s1SrcT transposeW
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

private theorem step109wc236s1_QtInv :
    (codeMat 485 : Mat3).transpose⁻¹ = (codeMat 171 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 485 : Mat3).transpose * (codeMat 171 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc236s1_contain :
    (o236SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 114) (codeMat 485) step109wc236s1SrcT := by
  change spanCodes [262, 132, 96, 20, 12, 1] ≤ actionW (codeMat 114) (codeMat 485) step109wc236s1SrcT
  apply step109wc236_spanCodes_le_of_gens [262, 132, 96, 20, 12, 1]
    (actionW (codeMat 114) (codeMat 485) step109wc236s1SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 255 ∈ step109wc236s1SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 255 (by decide)
    have hact : actionA (codeMat 114) (codeMat 485) (codeMat 255) = codeMat 262 := by
      unfold actionA
      rw [step109wc236s1_QtInv]
      show (codeMat 114 : Mat3).transpose * codeMat 255 * (codeMat 171 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 484 ∈ step109wc236s1SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 484 (by decide)
    have hact : actionA (codeMat 114) (codeMat 485) (codeMat 484) = codeMat 132 := by
      unfold actionA
      rw [step109wc236s1_QtInv]
      show (codeMat 114 : Mat3).transpose * codeMat 484 * (codeMat 171 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 42 ∈ step109wc236s1SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 42 (by decide)
    have hact : actionA (codeMat 114) (codeMat 485) (codeMat 42) = codeMat 96 := by
      unfold actionA
      rw [step109wc236s1_QtInv]
      show (codeMat 114 : Mat3).transpose * codeMat 42 * (codeMat 171 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 452 ∈ step109wc236s1SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 452 (by decide)
    have hact : actionA (codeMat 114) (codeMat 485) (codeMat 452) = codeMat 20 := by
      unfold actionA
      rw [step109wc236s1_QtInv]
      show (codeMat 114 : Mat3).transpose * codeMat 452 * (codeMat 171 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 453 ∈ step109wc236s1SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 453 (by decide)
    have hact : actionA (codeMat 114) (codeMat 485) (codeMat 453) = codeMat 12 := by
      unfold actionA
      rw [step109wc236s1_QtInv]
      show (codeMat 114 : Mat3).transpose * codeMat 453 * (codeMat 171 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 320 ∈ step109wc236s1SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 320 (by decide)
    have hact : actionA (codeMat 114) (codeMat 485) (codeMat 320) = codeMat 1 := by
      unfold actionA
      rw [step109wc236s1_QtInv]
      show (codeMat 114 : Mat3).transpose * codeMat 320 * (codeMat 171 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact

theorem step109wc236s1Dispatch :
    QuotientRankAtLeast (o236SourceU_wc ⟨1, by omega⟩) 15 := by
  have hP : Invertible (codeMat 114 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 485 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 114) (codeMat 485) step109wc236s1SrcT) 15 :=
    @quotientRankAtLeast_action (codeMat 114) (codeMat 485) hP hQ step109wc236s1SrcT 15
      step109wc236s1SrcT_lb
  exact quotientRankAtLeast_mono step109wc236s1_contain hAct

private def step109wc236s2SrcT : Submodule F2 Mat3 := spanCodes [272, 132, 80, 36, 10, 1]

private theorem step109wc236s2SrcT_lb : QuotientRankAtLeast step109wc236s2SrcT 15 := by
  have ht := quotientRankAtLeast_transpose step109_orbit80_lb15_wc
  have hle : step109wc236s2SrcT ≤ transposeW o80W_wc := by
    unfold step109wc236s2SrcT transposeW
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

private theorem step109wc236s2_QtInv :
    (codeMat 337 : Mat3).transpose⁻¹ = (codeMat 337 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 337 : Mat3).transpose * (codeMat 337 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc236s2_contain :
    (o236SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 85) (codeMat 337) step109wc236s2SrcT := by
  change spanCodes [262, 136, 66, 34, 20, 1] ≤ actionW (codeMat 85) (codeMat 337) step109wc236s2SrcT
  apply step109wc236_spanCodes_le_of_gens [262, 136, 66, 34, 20, 1]
    (actionW (codeMat 85) (codeMat 337) step109wc236s2SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 132 ∈ step109wc236s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 36, 10, 1] 132 (by decide)
    have hact : actionA (codeMat 85) (codeMat 337) (codeMat 132) = codeMat 262 := by
      unfold actionA
      rw [step109wc236s2_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 132 * (codeMat 337 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 170 ∈ step109wc236s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 36, 10, 1] 170 (by decide)
    have hact : actionA (codeMat 85) (codeMat 337) (codeMat 170) = codeMat 136 := by
      unfold actionA
      rw [step109wc236s2_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 170 * (codeMat 337 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 453 ∈ step109wc236s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 36, 10, 1] 453 (by decide)
    have hact : actionA (codeMat 85) (codeMat 337) (codeMat 453) = codeMat 66 := by
      unfold actionA
      rw [step109wc236s2_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 453 * (codeMat 337 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 160 ∈ step109wc236s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 36, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 85) (codeMat 337) (codeMat 160) = codeMat 34 := by
      unfold actionA
      rw [step109wc236s2_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 160 * (codeMat 337 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 272 ∈ step109wc236s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 36, 10, 1] 272 (by decide)
    have hact : actionA (codeMat 85) (codeMat 337) (codeMat 272) = codeMat 20 := by
      unfold actionA
      rw [step109wc236s2_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 272 * (codeMat 337 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 320 ∈ step109wc236s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 36, 10, 1] 320 (by decide)
    have hact : actionA (codeMat 85) (codeMat 337) (codeMat 320) = codeMat 1 := by
      unfold actionA
      rw [step109wc236s2_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 320 * (codeMat 337 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact

theorem step109wc236s2Dispatch :
    QuotientRankAtLeast (o236SourceU_wc ⟨2, by omega⟩) 15 := by
  have hP : Invertible (codeMat 85 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 337 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 85) (codeMat 337) step109wc236s2SrcT) 15 :=
    @quotientRankAtLeast_action (codeMat 85) (codeMat 337) hP hQ step109wc236s2SrcT 15
      step109wc236s2SrcT_lb
  exact quotientRankAtLeast_mono step109wc236s2_contain hAct


private theorem step109wc236s3_QtInv :
    (codeMat 395 : Mat3).transpose⁻¹ = (codeMat 474 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 395 : Mat3).transpose * (codeMat 474 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc236s3_contain :
    (o236SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 122) (codeMat 395) o80W_wc := by
  change spanCodes [262, 136, 68, 36, 20, 1] ≤ actionW (codeMat 122) (codeMat 395) o80W_wc
  apply step109wc236_spanCodes_le_of_gens [262, 136, 68, 36, 20, 1]
    (actionW (codeMat 122) (codeMat 395) o80W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 356 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 356 (by decide)
    have hact : actionA (codeMat 122) (codeMat 395) (codeMat 356) = codeMat 262 := by
      unfold actionA
      rw [step109wc236s3_QtInv]
      show (codeMat 122 : Mat3).transpose * codeMat 356 * (codeMat 474 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 366 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 366 (by decide)
    have hact : actionA (codeMat 122) (codeMat 395) (codeMat 366) = codeMat 136 := by
      unfold actionA
      rw [step109wc236s3_QtInv]
      show (codeMat 122 : Mat3).transpose * codeMat 366 * (codeMat 474 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 475 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 475 (by decide)
    have hact : actionA (codeMat 122) (codeMat 395) (codeMat 475) = codeMat 68 := by
      unfold actionA
      rw [step109wc236s3_QtInv]
      show (codeMat 122 : Mat3).transpose * codeMat 475 * (codeMat 474 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 260 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 122) (codeMat 395) (codeMat 260) = codeMat 36 := by
      unfold actionA
      rw [step109wc236s3_QtInv]
      show (codeMat 122 : Mat3).transpose * codeMat 260 * (codeMat 474 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 261 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 261 (by decide)
    have hact : actionA (codeMat 122) (codeMat 395) (codeMat 261) = codeMat 20 := by
      unfold actionA
      rw [step109wc236s3_QtInv]
      show (codeMat 122 : Mat3).transpose * codeMat 261 * (codeMat 474 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 192 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 192 (by decide)
    have hact : actionA (codeMat 122) (codeMat 395) (codeMat 192) = codeMat 1 := by
      unfold actionA
      rw [step109wc236s3_QtInv]
      show (codeMat 122 : Mat3).transpose * codeMat 192 * (codeMat 474 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact

theorem step109wc236s3Dispatch :
    QuotientRankAtLeast (o236SourceU_wc ⟨3, by omega⟩) 15 := by
  have hP : Invertible (codeMat 122 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 395 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 122) (codeMat 395) o80W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 122) (codeMat 395) hP hQ o80W_wc 15
      step109_orbit80_lb15_wc
  exact quotientRankAtLeast_mono step109wc236s3_contain hAct


private theorem step109wc236s4_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc236s4_contain :
    (o236SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 337) (codeMat 266) o56W := by
  change spanCodes [260, 136, 96, 20, 2, 1] ≤ actionW (codeMat 337) (codeMat 266) o56W
  apply step109wc236_spanCodes_le_of_gens [260, 136, 96, 20, 2, 1]
    (actionW (codeMat 337) (codeMat 266) o56W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 256 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 337) (codeMat 266) (codeMat 256) = codeMat 260 := by
      unfold actionA
      rw [step109wc236s4_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 256 * (codeMat 266 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 81 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 81 (by decide)
    have hact : actionA (codeMat 337) (codeMat 266) (codeMat 81) = codeMat 136 := by
      unfold actionA
      rw [step109wc236s4_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 81 * (codeMat 266 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 162 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 162 (by decide)
    have hact : actionA (codeMat 337) (codeMat 266) (codeMat 162) = codeMat 96 := by
      unfold actionA
      rw [step109wc236s4_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 162 * (codeMat 266 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 12 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 337) (codeMat 266) (codeMat 12) = codeMat 20 := by
      unfold actionA
      rw [step109wc236s4_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 12 * (codeMat 266 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 337) (codeMat 266) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step109wc236s4_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 337) (codeMat 266) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc236s4_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact

theorem step109wc236s4Dispatch :
    QuotientRankAtLeast (o236SourceU_wc ⟨4, by omega⟩) 14 := by
  have hP : Invertible (codeMat 337 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 337) (codeMat 266) o56W) 14 :=
    @quotientRankAtLeast_action (codeMat 337) (codeMat 266) hP hQ o56W 14
      step99_orbit56_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc236s4_contain hAct


private theorem step109wc236s5_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc236s5_contain :
    (o236SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 161) (codeMat 140) o56W := by
  change spanCodes [258, 136, 96, 16, 4, 1] ≤ actionW (codeMat 161) (codeMat 140) o56W
  apply step109wc236_spanCodes_le_of_gens [258, 136, 96, 16, 4, 1]
    (actionW (codeMat 161) (codeMat 140) o56W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 12 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 161) (codeMat 140) (codeMat 12) = codeMat 258 := by
      unfold actionA
      rw [step109wc236s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 12 * (codeMat 98 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 140) (codeMat 160) = codeMat 136 := by
      unfold actionA
      rw [step109wc236s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * (codeMat 98 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 80 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 161) (codeMat 140) (codeMat 80) = codeMat 96 := by
      unfold actionA
      rw [step109wc236s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 80 * (codeMat 98 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 140) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step109wc236s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 98 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 140) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step109wc236s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 140) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc236s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact

theorem step109wc236s5Dispatch :
    QuotientRankAtLeast (o236SourceU_wc ⟨5, by omega⟩) 14 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 140) o56W) 14 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 140) hP hQ o56W 14
      step99_orbit56_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc236s5_contain hAct

private def step109wc236s6SrcT : Submodule F2 Mat3 := spanCodes [256, 160, 66, 20, 8, 1]

private theorem step109wc236s6SrcT_lb : QuotientRankAtLeast step109wc236s6SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step99_orbit56_lb14_unconditional
  have hle : step109wc236s6SrcT ≤ transposeW o56W := by
    unfold step109wc236s6SrcT transposeW
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

private theorem step109wc236s6_QtInv :
    (codeMat 183 : Mat3).transpose⁻¹ = (codeMat 419 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 183 : Mat3).transpose * (codeMat 419 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc236s6_contain :
    (o236SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 346) (codeMat 183) step109wc236s6SrcT := by
  change spanCodes [262, 128, 96, 20, 8, 1] ≤ actionW (codeMat 346) (codeMat 183) step109wc236s6SrcT
  apply step109wc236_spanCodes_le_of_gens [262, 128, 96, 20, 8, 1]
    (actionW (codeMat 346) (codeMat 183) step109wc236s6SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 255 ∈ step109wc236s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 255 (by decide)
    have hact : actionA (codeMat 346) (codeMat 183) (codeMat 255) = codeMat 262 := by
      unfold actionA
      rw [step109wc236s6_QtInv]
      show (codeMat 346 : Mat3).transpose * codeMat 255 * (codeMat 419 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 511 ∈ step109wc236s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 511 (by decide)
    have hact : actionA (codeMat 346) (codeMat 183) (codeMat 511) = codeMat 128 := by
      unfold actionA
      rw [step109wc236s6_QtInv]
      show (codeMat 346 : Mat3).transpose * codeMat 511 * (codeMat 419 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 74 ∈ step109wc236s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 74 (by decide)
    have hact : actionA (codeMat 346) (codeMat 183) (codeMat 74) = codeMat 96 := by
      unfold actionA
      rw [step109wc236s6_QtInv]
      show (codeMat 346 : Mat3).transpose * codeMat 74 * (codeMat 419 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 28 ∈ step109wc236s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 28 (by decide)
    have hact : actionA (codeMat 346) (codeMat 183) (codeMat 28) = codeMat 20 := by
      unfold actionA
      rw [step109wc236s6_QtInv]
      show (codeMat 346 : Mat3).transpose * codeMat 28 * (codeMat 419 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ step109wc236s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 1 (by decide)
    have hact : actionA (codeMat 346) (codeMat 183) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step109wc236s6_QtInv]
      show (codeMat 346 : Mat3).transpose * codeMat 1 * (codeMat 419 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 9 ∈ step109wc236s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 9 (by decide)
    have hact : actionA (codeMat 346) (codeMat 183) (codeMat 9) = codeMat 1 := by
      unfold actionA
      rw [step109wc236s6_QtInv]
      show (codeMat 346 : Mat3).transpose * codeMat 9 * (codeMat 419 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact

theorem step109wc236s6Dispatch :
    QuotientRankAtLeast (o236SourceU_wc ⟨6, by omega⟩) 14 := by
  have hP : Invertible (codeMat 346 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 183 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 346) (codeMat 183) step109wc236s6SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 346) (codeMat 183) hP hQ step109wc236s6SrcT 14
      step109wc236s6SrcT_lb
  exact quotientRankAtLeast_mono step109wc236s6_contain hAct


private theorem step109wc236s7_QtInv :
    (codeMat 330 : Mat3).transpose⁻¹ = (codeMat 394 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 330 : Mat3).transpose * (codeMat 394 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc236s7_contain :
    (o236SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 431) (codeMat 330) o78W_wc := by
  change spanCodes [262, 134, 96, 20, 14, 1] ≤ actionW (codeMat 431) (codeMat 330) o78W_wc
  apply step109wc236_spanCodes_le_of_gens [262, 134, 96, 20, 14, 1]
    (actionW (codeMat 431) (codeMat 330) o78W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 97 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 97 (by decide)
    have hact : actionA (codeMat 431) (codeMat 330) (codeMat 97) = codeMat 262 := by
      unfold actionA
      rw [step109wc236s7_QtInv]
      show (codeMat 431 : Mat3).transpose * codeMat 97 * (codeMat 394 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 268 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 268 (by decide)
    have hact : actionA (codeMat 431) (codeMat 330) (codeMat 268) = codeMat 134 := by
      unfold actionA
      rw [step109wc236s7_QtInv]
      show (codeMat 431 : Mat3).transpose * codeMat 268 * (codeMat 394 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 402 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 402 (by decide)
    have hact : actionA (codeMat 431) (codeMat 330) (codeMat 402) = codeMat 96 := by
      unfold actionA
      rw [step109wc236s7_QtInv]
      show (codeMat 431 : Mat3).transpose * codeMat 402 * (codeMat 394 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 269 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 269 (by decide)
    have hact : actionA (codeMat 431) (codeMat 330) (codeMat 269) = codeMat 20 := by
      unfold actionA
      rw [step109wc236s7_QtInv]
      show (codeMat 431 : Mat3).transpose * codeMat 269 * (codeMat 394 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 371 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 371 (by decide)
    have hact : actionA (codeMat 431) (codeMat 330) (codeMat 371) = codeMat 14 := by
      unfold actionA
      rw [step109wc236s7_QtInv]
      show (codeMat 431 : Mat3).transpose * codeMat 371 * (codeMat 394 : Mat3).transpose = codeMat 14
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 390 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 390 (by decide)
    have hact : actionA (codeMat 431) (codeMat 330) (codeMat 390) = codeMat 1 := by
      unfold actionA
      rw [step109wc236s7_QtInv]
      show (codeMat 431 : Mat3).transpose * codeMat 390 * (codeMat 394 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact

theorem step109wc236s7Dispatch :
    QuotientRankAtLeast (o236SourceU_wc ⟨7, by omega⟩) 14 := by
  have hP : Invertible (codeMat 431 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 330 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 431) (codeMat 330) o78W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 431) (codeMat 330) hP hQ o78W_wc 14
      step109_orbit78_lb14_wc
  exact quotientRankAtLeast_mono step109wc236s7_contain hAct

private def step109wc236s8SrcT : Submodule F2 Mat3 := spanCodes [272, 132, 66, 34, 8, 1]

private theorem step109wc236s8SrcT_lb : QuotientRankAtLeast step109wc236s8SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step109_orbit57_lb14_wc
  have hle : step109wc236s8SrcT ≤ transposeW o57W_wc := by
    unfold step109wc236s8SrcT transposeW
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

private theorem step109wc236s8_QtInv :
    (codeMat 419 : Mat3).transpose⁻¹ = (codeMat 183 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 419 : Mat3).transpose * (codeMat 183 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc236s8_contain :
    (o236SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 229) (codeMat 419) step109wc236s8SrcT := by
  change spanCodes [262, 136, 64, 32, 20, 1] ≤ actionW (codeMat 229) (codeMat 419) step109wc236s8SrcT
  apply step109wc236_spanCodes_le_of_gens [262, 136, 64, 32, 20, 1]
    (actionW (codeMat 229) (codeMat 419) step109wc236s8SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 43 ∈ step109wc236s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 66, 34, 8, 1] 43 (by decide)
    have hact : actionA (codeMat 229) (codeMat 419) (codeMat 43) = codeMat 262 := by
      unfold actionA
      rw [step109wc236s8_QtInv]
      show (codeMat 229 : Mat3).transpose * codeMat 43 * (codeMat 183 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 97 ∈ step109wc236s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 66, 34, 8, 1] 97 (by decide)
    have hact : actionA (codeMat 229) (codeMat 419) (codeMat 97) = codeMat 136 := by
      unfold actionA
      rw [step109wc236s8_QtInv]
      show (codeMat 229 : Mat3).transpose * codeMat 97 * (codeMat 183 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ step109wc236s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 66, 34, 8, 1] 8 (by decide)
    have hact : actionA (codeMat 229) (codeMat 419) (codeMat 8) = codeMat 64 := by
      unfold actionA
      rw [step109wc236s8_QtInv]
      show (codeMat 229 : Mat3).transpose * codeMat 8 * (codeMat 183 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 438 ∈ step109wc236s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 66, 34, 8, 1] 438 (by decide)
    have hact : actionA (codeMat 229) (codeMat 419) (codeMat 438) = codeMat 32 := by
      unfold actionA
      rw [step109wc236s8_QtInv]
      show (codeMat 229 : Mat3).transpose * codeMat 438 * (codeMat 183 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 347 ∈ step109wc236s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 66, 34, 8, 1] 347 (by decide)
    have hact : actionA (codeMat 229) (codeMat 419) (codeMat 347) = codeMat 20 := by
      unfold actionA
      rw [step109wc236s8_QtInv]
      show (codeMat 229 : Mat3).transpose * codeMat 347 * (codeMat 183 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 9 ∈ step109wc236s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 66, 34, 8, 1] 9 (by decide)
    have hact : actionA (codeMat 229) (codeMat 419) (codeMat 9) = codeMat 1 := by
      unfold actionA
      rw [step109wc236s8_QtInv]
      show (codeMat 229 : Mat3).transpose * codeMat 9 * (codeMat 183 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact

theorem step109wc236s8Dispatch :
    QuotientRankAtLeast (o236SourceU_wc ⟨8, by omega⟩) 14 := by
  have hP : Invertible (codeMat 229 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 419 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 229) (codeMat 419) step109wc236s8SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 229) (codeMat 419) hP hQ step109wc236s8SrcT 14
      step109wc236s8SrcT_lb
  exact quotientRankAtLeast_mono step109wc236s8_contain hAct


private theorem step109wc236s9_QtInv :
    (codeMat 213 : Mat3).transpose⁻¹ = (codeMat 470 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 213 : Mat3).transpose * (codeMat 470 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc236s9_contain :
    (o236SourceU_wc ⟨9, by omega⟩) ≤ actionW (codeMat 494) (codeMat 213) o82W := by
  change spanCodes [262, 136, 70, 38, 20, 1] ≤ actionW (codeMat 494) (codeMat 213) o82W
  apply step109wc236_spanCodes_le_of_gens [262, 136, 70, 38, 20, 1]
    (actionW (codeMat 494) (codeMat 213) o82W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 398 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 398 (by decide)
    have hact : actionA (codeMat 494) (codeMat 213) (codeMat 398) = codeMat 262 := by
      unfold actionA
      rw [step109wc236s9_QtInv]
      show (codeMat 494 : Mat3).transpose * codeMat 398 * (codeMat 470 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 222 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 222 (by decide)
    have hact : actionA (codeMat 494) (codeMat 213) (codeMat 222) = codeMat 136 := by
      unfold actionA
      rw [step109wc236s9_QtInv]
      show (codeMat 494 : Mat3).transpose * codeMat 222 * (codeMat 470 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 170 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 170 (by decide)
    have hact : actionA (codeMat 494) (codeMat 213) (codeMat 170) = codeMat 70 := by
      unfold actionA
      rw [step109wc236s9_QtInv]
      show (codeMat 494 : Mat3).transpose * codeMat 170 * (codeMat 470 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 399 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 399 (by decide)
    have hact : actionA (codeMat 494) (codeMat 213) (codeMat 399) = codeMat 38 := by
      unfold actionA
      rw [step109wc236s9_QtInv]
      show (codeMat 494 : Mat3).transpose * codeMat 399 * (codeMat 470 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 497 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 497 (by decide)
    have hact : actionA (codeMat 494) (codeMat 213) (codeMat 497) = codeMat 20 := by
      unfold actionA
      rw [step109wc236s9_QtInv]
      show (codeMat 494 : Mat3).transpose * codeMat 497 * (codeMat 470 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 325 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 325 (by decide)
    have hact : actionA (codeMat 494) (codeMat 213) (codeMat 325) = codeMat 1 := by
      unfold actionA
      rw [step109wc236s9_QtInv]
      show (codeMat 494 : Mat3).transpose * codeMat 325 * (codeMat 470 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact

theorem step109wc236s9Dispatch :
    QuotientRankAtLeast (o236SourceU_wc ⟨9, by omega⟩) 14 := by
  have hP : Invertible (codeMat 494 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 213 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 494) (codeMat 213) o82W) 14 :=
    @quotientRankAtLeast_action (codeMat 494) (codeMat 213) hP hQ o82W 14
      step99_orbit82_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc236s9_contain hAct


private theorem step109wc236s10_QtInv :
    (codeMat 498 : Mat3).transpose⁻¹ = (codeMat 206 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 498 : Mat3).transpose * (codeMat 206 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc236s10_contain :
    (o236SourceU_wc ⟨10, by omega⟩) ≤ actionW (codeMat 342) (codeMat 498) o82W := by
  change spanCodes [262, 136, 74, 42, 20, 1] ≤ actionW (codeMat 342) (codeMat 498) o82W
  apply step109wc236_spanCodes_le_of_gens [262, 136, 74, 42, 20, 1]
    (actionW (codeMat 342) (codeMat 498) o82W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 127 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 127 (by decide)
    have hact : actionA (codeMat 342) (codeMat 498) (codeMat 127) = codeMat 262 := by
      unfold actionA
      rw [step109wc236s10_QtInv]
      show (codeMat 342 : Mat3).transpose * codeMat 127 * (codeMat 206 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 31 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 31 (by decide)
    have hact : actionA (codeMat 342) (codeMat 498) (codeMat 31) = codeMat 136 := by
      unfold actionA
      rw [step109wc236s10_QtInv]
      show (codeMat 342 : Mat3).transpose * codeMat 31 * (codeMat 206 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 507 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 507 (by decide)
    have hact : actionA (codeMat 342) (codeMat 498) (codeMat 507) = codeMat 74 := by
      unfold actionA
      rw [step109wc236s10_QtInv]
      show (codeMat 342 : Mat3).transpose * codeMat 507 * (codeMat 206 : Mat3).transpose = codeMat 74
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 495 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 495 (by decide)
    have hact : actionA (codeMat 342) (codeMat 498) (codeMat 495) = codeMat 42 := by
      unfold actionA
      rw [step109wc236s10_QtInv]
      show (codeMat 342 : Mat3).transpose * codeMat 495 * (codeMat 206 : Mat3).transpose = codeMat 42
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 398 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 398 (by decide)
    have hact : actionA (codeMat 342) (codeMat 498) (codeMat 398) = codeMat 20 := by
      unfold actionA
      rw [step109wc236s10_QtInv]
      show (codeMat 342 : Mat3).transpose * codeMat 398 * (codeMat 206 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 292 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 292 (by decide)
    have hact : actionA (codeMat 342) (codeMat 498) (codeMat 292) = codeMat 1 := by
      unfold actionA
      rw [step109wc236s10_QtInv]
      show (codeMat 342 : Mat3).transpose * codeMat 292 * (codeMat 206 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact

theorem step109wc236s10Dispatch :
    QuotientRankAtLeast (o236SourceU_wc ⟨10, by omega⟩) 14 := by
  have hP : Invertible (codeMat 342 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 498 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 342) (codeMat 498) o82W) 14 :=
    @quotientRankAtLeast_action (codeMat 342) (codeMat 498) hP hQ o82W 14
      step99_orbit82_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc236s10_contain hAct


private theorem step109wc236s11_QtInv :
    (codeMat 492 : Mat3).transpose⁻¹ = (codeMat 115 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 492 : Mat3).transpose * (codeMat 115 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc236s11_contain :
    (o236SourceU_wc ⟨11, by omega⟩) ≤ actionW (codeMat 491) (codeMat 492) o79W_wc := by
  change spanCodes [262, 136, 76, 44, 20, 1] ≤ actionW (codeMat 491) (codeMat 492) o79W_wc
  apply step109wc236_spanCodes_le_of_gens [262, 136, 76, 44, 20, 1]
    (actionW (codeMat 491) (codeMat 492) o79W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 284 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 284 (by decide)
    have hact : actionA (codeMat 491) (codeMat 492) (codeMat 284) = codeMat 262 := by
      unfold actionA
      rw [step109wc236s11_QtInv]
      show (codeMat 491 : Mat3).transpose * codeMat 284 * (codeMat 115 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 180 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 180 (by decide)
    have hact : actionA (codeMat 491) (codeMat 492) (codeMat 180) = codeMat 136 := by
      unfold actionA
      rw [step109wc236s11_QtInv]
      show (codeMat 491 : Mat3).transpose * codeMat 180 * (codeMat 115 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 457 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 457 (by decide)
    have hact : actionA (codeMat 491) (codeMat 492) (codeMat 457) = codeMat 76 := by
      unfold actionA
      rw [step109wc236s11_QtInv]
      show (codeMat 491 : Mat3).transpose * codeMat 457 * (codeMat 115 : Mat3).transpose = codeMat 76
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 439 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 439 (by decide)
    have hact : actionA (codeMat 491) (codeMat 492) (codeMat 439) = codeMat 44 := by
      unfold actionA
      rw [step109wc236s11_QtInv]
      show (codeMat 491 : Mat3).transpose * codeMat 439 * (codeMat 115 : Mat3).transpose = codeMat 44
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 223 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 223 (by decide)
    have hact : actionA (codeMat 491) (codeMat 492) (codeMat 223) = codeMat 20 := by
      unfold actionA
      rw [step109wc236s11_QtInv]
      show (codeMat 491 : Mat3).transpose * codeMat 223 * (codeMat 115 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 438 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 438 (by decide)
    have hact : actionA (codeMat 491) (codeMat 492) (codeMat 438) = codeMat 1 := by
      unfold actionA
      rw [step109wc236s11_QtInv]
      show (codeMat 491 : Mat3).transpose * codeMat 438 * (codeMat 115 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact

theorem step109wc236s11Dispatch :
    QuotientRankAtLeast (o236SourceU_wc ⟨11, by omega⟩) 14 := by
  have hP : Invertible (codeMat 491 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 492 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 491) (codeMat 492) o79W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 491) (codeMat 492) hP hQ o79W_wc 14
      step109_orbit79_lb14_wc
  exact quotientRankAtLeast_mono step109wc236s11_contain hAct


private theorem step109wc236s12_QtInv :
    (codeMat 403 : Mat3).transpose⁻¹ = (codeMat 403 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 403 : Mat3).transpose * (codeMat 403 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc236s12_contain :
    (o236SourceU_wc ⟨12, by omega⟩) ≤ actionW (codeMat 305) (codeMat 403) orbit14W := by
  change spanCodes [256, 136, 72, 40, 18, 6, 1] ≤ actionW (codeMat 305) (codeMat 403) orbit14W
  apply step109wc236_spanCodes_le_of_gens [256, 136, 72, 40, 18, 6, 1]
    (actionW (codeMat 305) (codeMat 403) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 305) (codeMat 403) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step109wc236s12_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 256 * (codeMat 403 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 392 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 392 (by decide)
    have hact : actionA (codeMat 305) (codeMat 403) (codeMat 392) = codeMat 136 := by
      unfold actionA
      rw [step109wc236s12_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 392 * (codeMat 403 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 305) (codeMat 403) (codeMat 8) = codeMat 72 := by
      unfold actionA
      rw [step109wc236s12_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 8 * (codeMat 403 : Mat3).transpose = codeMat 72
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 305) (codeMat 403) (codeMat 360) = codeMat 40 := by
      unfold actionA
      rw [step109wc236s12_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 360 * (codeMat 403 : Mat3).transpose = codeMat 40
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 511 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 511 (by decide)
    have hact : actionA (codeMat 305) (codeMat 403) (codeMat 511) = codeMat 18 := by
      unfold actionA
      rw [step109wc236s12_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 511 * (codeMat 403 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 305) (codeMat 403) (codeMat 3) = codeMat 6 := by
      unfold actionA
      rw [step109wc236s12_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 3 * (codeMat 403 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 305) (codeMat 403) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc236s12_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 1 * (codeMat 403 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc236_codeMat_mem_actionW_of_witness hw hact

theorem step109wc236s12Dispatch :
    QuotientRankAtLeast (o236SourceU_wc ⟨12, by omega⟩) 12 := by
  have hP : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 403 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 305) (codeMat 403) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 305) (codeMat 403) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc236s12_contain hAct

theorem step109wc236_all_dispatch (i : Fin 13) :
    QuotientRankAtLeast (o236SourceU_wc i) (o236SourceLb_wc i) := by
  fin_cases i
  · exact step109wc236s0Dispatch
  · exact step109wc236s1Dispatch
  · exact step109wc236s2Dispatch
  · exact step109wc236s3Dispatch
  · exact step109wc236s4Dispatch
  · exact step109wc236s5Dispatch
  · exact step109wc236s6Dispatch
  · exact step109wc236s7Dispatch
  · exact step109wc236s8Dispatch
  · exact step109wc236s9Dispatch
  · exact step109wc236s10Dispatch
  · exact step109wc236s11Dispatch
  · exact step109wc236s12Dispatch

theorem step109_orbit236_lb16_wc : QuotientRankAtLeast o236W_wc 16 :=
  o236Lb16_wc step109wc236_all_dispatch

end QiushiMatmul
