import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit96Consumer
import QiushiOrbit31FP
import QiushiStep99Orbit34Dispatch
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc96_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc96_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc96s0_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc96s0_contain :
    (o96SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 266) (codeMat 161) orbit31W := by
  change spanCodes [68, 32, 20, 8, 2, 1] ≤ actionW (codeMat 266) (codeMat 161) orbit31W
  apply step109wc96_spanCodes_le_of_gens [68, 32, 20, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 161) orbit31W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 80 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 80 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 80) = codeMat 68 := by
      unfold actionA
      rw [step109wc96s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 80 * (codeMat 161 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [step109wc96s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 20 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 20 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 20) = codeMat 20 := by
      unfold actionA
      rw [step109wc96s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 20 * (codeMat 161 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step109wc96s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 32) = codeMat 2 := by
      unfold actionA
      rw [step109wc96s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 161 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc96s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact

theorem step109wc96s0Dispatch :
    QuotientRankAtLeast (o96SourceU_wc ⟨0, by omega⟩) 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 161) orbit31W) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 161) hP hQ orbit31W 15
      orbit31_lb15
  exact quotientRankAtLeast_mono step109wc96s0_contain hAct


private theorem step109wc96s1_QtInv :
    (codeMat 417 : Mat3).transpose⁻¹ = (codeMat 177 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 417 : Mat3).transpose * (codeMat 177 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc96s1_contain :
    (o96SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 266) (codeMat 417) orbit31W := by
  change spanCodes [68, 36, 20, 8, 2, 1] ≤ actionW (codeMat 266) (codeMat 417) orbit31W
  apply step109wc96_spanCodes_le_of_gens [68, 36, 20, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 417) orbit31W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 112 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 112 (by decide)
    have hact : actionA (codeMat 266) (codeMat 417) (codeMat 112) = codeMat 68 := by
      unfold actionA
      rw [step109wc96s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 112 * (codeMat 177 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 54 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 54 (by decide)
    have hact : actionA (codeMat 266) (codeMat 417) (codeMat 54) = codeMat 36 := by
      unfold actionA
      rw [step109wc96s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 54 * (codeMat 177 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 52 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 52 (by decide)
    have hact : actionA (codeMat 266) (codeMat 417) (codeMat 52) = codeMat 20 := by
      unfold actionA
      rw [step109wc96s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 52 * (codeMat 177 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 417) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step109wc96s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 177 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 417) (codeMat 32) = codeMat 2 := by
      unfold actionA
      rw [step109wc96s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 177 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 417) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc96s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 177 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact

theorem step109wc96s1Dispatch :
    QuotientRankAtLeast (o96SourceU_wc ⟨1, by omega⟩) 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 417) orbit31W) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 417) hP hQ orbit31W 15
      orbit31_lb15
  exact quotientRankAtLeast_mono step109wc96s1_contain hAct

private def step109wc96s2SrcT : Submodule F2 Mat3 := spanCodes [128, 68, 20, 8, 2, 1]

private theorem step109wc96s2SrcT_lb : QuotientRankAtLeast step109wc96s2SrcT 15 := by
  have ht := quotientRankAtLeast_transpose orbit31_lb15
  have hle : step109wc96s2SrcT ≤ transposeW orbit31W := by
    unfold step109wc96s2SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4 | h5
    · subst h0
      show codeMat 128 ∈ Submodule.map transposeLinearMap orbit31W
      exact ⟨codeMat 32, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 32 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 68 ∈ Submodule.map transposeLinearMap orbit31W
      exact ⟨codeMat 68, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 68 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 20 ∈ Submodule.map transposeLinearMap orbit31W
      exact ⟨codeMat 80, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 80 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 8 ∈ Submodule.map transposeLinearMap orbit31W
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 2 ∈ Submodule.map transposeLinearMap orbit31W
      exact ⟨codeMat 8, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 8 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h5
      show codeMat 1 ∈ Submodule.map transposeLinearMap orbit31W
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc96s2_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc96s2_contain :
    (o96SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 161) (codeMat 266) step109wc96s2SrcT := by
  change spanCodes [128, 68, 20, 8, 2, 1] ≤ actionW (codeMat 161) (codeMat 266) step109wc96s2SrcT
  apply step109wc96_spanCodes_le_of_gens [128, 68, 20, 8, 2, 1]
    (actionW (codeMat 161) (codeMat 266) step109wc96s2SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 8 ∈ step109wc96s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 8) = codeMat 128 := by
      unfold actionA
      rw [step109wc96s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 20 ∈ step109wc96s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 20, 8, 2, 1] 20 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 20) = codeMat 68 := by
      unfold actionA
      rw [step109wc96s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 20 * (codeMat 266 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ step109wc96s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 20, 8, 2, 1] 68 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 68) = codeMat 20 := by
      unfold actionA
      rw [step109wc96s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 68 * (codeMat 266 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ step109wc96s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 128) = codeMat 8 := by
      unfold actionA
      rw [step109wc96s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 128 * (codeMat 266 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ step109wc96s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step109wc96s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ step109wc96s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc96s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact

theorem step109wc96s2Dispatch :
    QuotientRankAtLeast (o96SourceU_wc ⟨2, by omega⟩) 15 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 266) step109wc96s2SrcT) 15 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 266) hP hQ step109wc96s2SrcT 15
      step109wc96s2SrcT_lb
  exact quotientRankAtLeast_mono step109wc96s2_contain hAct

private def step109wc96s3SrcT : Submodule F2 Mat3 := spanCodes [128, 68, 20, 8, 2, 1]

private theorem step109wc96s3SrcT_lb : QuotientRankAtLeast step109wc96s3SrcT 15 := by
  have ht := quotientRankAtLeast_transpose orbit31_lb15
  have hle : step109wc96s3SrcT ≤ transposeW orbit31W := by
    unfold step109wc96s3SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4 | h5
    · subst h0
      show codeMat 128 ∈ Submodule.map transposeLinearMap orbit31W
      exact ⟨codeMat 32, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 32 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 68 ∈ Submodule.map transposeLinearMap orbit31W
      exact ⟨codeMat 68, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 68 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 20 ∈ Submodule.map transposeLinearMap orbit31W
      exact ⟨codeMat 80, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 80 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 8 ∈ Submodule.map transposeLinearMap orbit31W
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 2 ∈ Submodule.map transposeLinearMap orbit31W
      exact ⟨codeMat 8, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 8 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h5
      show codeMat 1 ∈ Submodule.map transposeLinearMap orbit31W
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc96s3_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = (codeMat 267 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * (codeMat 267 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc96s3_contain :
    (o96SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 161) (codeMat 282) step109wc96s3SrcT := by
  change spanCodes [132, 68, 20, 8, 2, 1] ≤ actionW (codeMat 161) (codeMat 282) step109wc96s3SrcT
  apply step109wc96_spanCodes_le_of_gens [132, 68, 20, 8, 2, 1]
    (actionW (codeMat 161) (codeMat 282) step109wc96s3SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 28 ∈ step109wc96s3SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 20, 8, 2, 1] 28 (by decide)
    have hact : actionA (codeMat 161) (codeMat 282) (codeMat 28) = codeMat 132 := by
      unfold actionA
      rw [step109wc96s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 28 * (codeMat 267 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 20 ∈ step109wc96s3SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 20, 8, 2, 1] 20 (by decide)
    have hact : actionA (codeMat 161) (codeMat 282) (codeMat 20) = codeMat 68 := by
      unfold actionA
      rw [step109wc96s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 20 * (codeMat 267 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 196 ∈ step109wc96s3SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 20, 8, 2, 1] 196 (by decide)
    have hact : actionA (codeMat 161) (codeMat 282) (codeMat 196) = codeMat 20 := by
      unfold actionA
      rw [step109wc96s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 196 * (codeMat 267 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ step109wc96s3SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 161) (codeMat 282) (codeMat 128) = codeMat 8 := by
      unfold actionA
      rw [step109wc96s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 128 * (codeMat 267 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ step109wc96s3SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 20, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 161) (codeMat 282) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc96s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 3 * (codeMat 267 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ step109wc96s3SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 282) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc96s3_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 267 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact

theorem step109wc96s3Dispatch :
    QuotientRankAtLeast (o96SourceU_wc ⟨3, by omega⟩) 15 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 282) step109wc96s3SrcT) 15 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 282) hP hQ step109wc96s3SrcT 15
      step109wc96s3SrcT_lb
  exact quotientRankAtLeast_mono step109wc96s3_contain hAct


private theorem step109wc96s4_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc96s4_contain :
    (o96SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 401) (codeMat 273) o34W := by
  change spanCodes [288, 68, 20, 8, 2, 1] ≤ actionW (codeMat 401) (codeMat 273) o34W
  apply step109wc96_spanCodes_le_of_gens [288, 68, 20, 8, 2, 1]
    (actionW (codeMat 401) (codeMat 273) o34W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 256 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 401) (codeMat 273) (codeMat 256) = codeMat 288 := by
      unfold actionA
      rw [step109wc96s4_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 256 * (codeMat 273 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 76 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 76 (by decide)
    have hact : actionA (codeMat 401) (codeMat 273) (codeMat 76) = codeMat 68 := by
      unfold actionA
      rw [step109wc96s4_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 76 * (codeMat 273 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 20 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 20 (by decide)
    have hact : actionA (codeMat 401) (codeMat 273) (codeMat 20) = codeMat 20 := by
      unfold actionA
      rw [step109wc96s4_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 20 * (codeMat 273 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 401) (codeMat 273) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc96s4_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 401) (codeMat 273) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc96s4_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 401) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc96s4_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact

theorem step109wc96s4Dispatch :
    QuotientRankAtLeast (o96SourceU_wc ⟨4, by omega⟩) 14 := by
  have hP : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 401) (codeMat 273) o34W) 14 :=
    @quotientRankAtLeast_action (codeMat 401) (codeMat 273) hP hQ o34W 14
      step99_orbit34_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc96s4_contain hAct


private theorem step109wc96s5_QtInv :
    (codeMat 277 : Mat3).transpose⁻¹ = (codeMat 277 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 277 : Mat3).transpose * (codeMat 277 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc96s5_contain :
    (o96SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 401) (codeMat 277) o34W := by
  change spanCodes [292, 68, 20, 8, 2, 1] ≤ actionW (codeMat 401) (codeMat 277) o34W
  apply step109wc96_spanCodes_le_of_gens [292, 68, 20, 8, 2, 1]
    (actionW (codeMat 401) (codeMat 277) o34W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 325 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 325 (by decide)
    have hact : actionA (codeMat 401) (codeMat 277) (codeMat 325) = codeMat 292 := by
      unfold actionA
      rw [step109wc96s5_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 325 * (codeMat 277 : Mat3).transpose = codeMat 292
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 77 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 77 (by decide)
    have hact : actionA (codeMat 401) (codeMat 277) (codeMat 77) = codeMat 68 := by
      unfold actionA
      rw [step109wc96s5_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 77 * (codeMat 277 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 21 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 21 (by decide)
    have hact : actionA (codeMat 401) (codeMat 277) (codeMat 21) = codeMat 20 := by
      unfold actionA
      rw [step109wc96s5_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 21 * (codeMat 277 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 401) (codeMat 277) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc96s5_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 8 * (codeMat 277 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 401) (codeMat 277) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc96s5_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 2 * (codeMat 277 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 401) (codeMat 277) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc96s5_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 1 * (codeMat 277 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact

theorem step109wc96s5Dispatch :
    QuotientRankAtLeast (o96SourceU_wc ⟨5, by omega⟩) 14 := by
  have hP : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 277 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 401) (codeMat 277) o34W) 14 :=
    @quotientRankAtLeast_action (codeMat 401) (codeMat 277) hP hQ o34W 14
      step99_orbit34_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc96s5_contain hAct


private theorem step109wc96s6_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = (codeMat 305 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * (codeMat 305 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc96s6_contain :
    (o96SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 273) (codeMat 305) o34W := by
  change spanCodes [384, 68, 20, 8, 2, 1] ≤ actionW (codeMat 273) (codeMat 305) o34W
  apply step109wc96_spanCodes_le_of_gens [384, 68, 20, 8, 2, 1]
    (actionW (codeMat 273) (codeMat 305) o34W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 256 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 305) (codeMat 256) = codeMat 384 := by
      unfold actionA
      rw [step109wc96s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 305 : Mat3).transpose = codeMat 384
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 70 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 70 (by decide)
    have hact : actionA (codeMat 273) (codeMat 305) (codeMat 70) = codeMat 68 := by
      unfold actionA
      rw [step109wc96s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 70 * (codeMat 305 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 22 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 22 (by decide)
    have hact : actionA (codeMat 273) (codeMat 305) (codeMat 22) = codeMat 20 := by
      unfold actionA
      rw [step109wc96s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 22 * (codeMat 305 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 305) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc96s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 305 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 305) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc96s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 305 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 305) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc96s6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 305 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact

theorem step109wc96s6Dispatch :
    QuotientRankAtLeast (o96SourceU_wc ⟨6, by omega⟩) 14 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 305) o34W) 14 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 305) hP hQ o34W 14
      step99_orbit34_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc96s6_contain hAct


private theorem step109wc96s7_QtInv :
    (codeMat 307 : Mat3).transpose⁻¹ = (codeMat 311 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 307 : Mat3).transpose * (codeMat 311 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc96s7_contain :
    (o96SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 273) (codeMat 307) o34W := by
  change spanCodes [388, 68, 20, 8, 2, 1] ≤ actionW (codeMat 273) (codeMat 307) o34W
  apply step109wc96_spanCodes_le_of_gens [388, 68, 20, 8, 2, 1]
    (actionW (codeMat 273) (codeMat 307) o34W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 326 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 326 (by decide)
    have hact : actionA (codeMat 273) (codeMat 307) (codeMat 326) = codeMat 388 := by
      unfold actionA
      rw [step109wc96s7_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 326 * (codeMat 311 : Mat3).transpose = codeMat 388
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 70 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 70 (by decide)
    have hact : actionA (codeMat 273) (codeMat 307) (codeMat 70) = codeMat 68 := by
      unfold actionA
      rw [step109wc96s7_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 70 * (codeMat 311 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 30 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 30 (by decide)
    have hact : actionA (codeMat 273) (codeMat 307) (codeMat 30) = codeMat 20 := by
      unfold actionA
      rw [step109wc96s7_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 30 * (codeMat 311 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 307) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc96s7_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 311 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 273) (codeMat 307) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc96s7_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 3 * (codeMat 311 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 307) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc96s7_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 311 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact

theorem step109wc96s7Dispatch :
    QuotientRankAtLeast (o96SourceU_wc ⟨7, by omega⟩) 14 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 307 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 307) o34W) 14 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 307) hP hQ o34W 14
      step99_orbit34_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc96s7_contain hAct


private theorem step109wc96s8_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc96s8_contain :
    (o96SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 161) (codeMat 161) flatW_2 := by
  change spanCodes [256, 160, 64, 16, 8, 4, 2, 1] ≤ actionW (codeMat 161) (codeMat 161) flatW_2
  apply step109wc96_spanCodes_le_of_gens [256, 160, 64, 16, 8, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 161) flatW_2)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 16 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 16) = codeMat 256 := by
      unfold actionA
      rw [step109wc96s8_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 16 * (codeMat 161 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 160) = codeMat 160 := by
      unfold actionA
      rw [step109wc96s8_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * (codeMat 161 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 8) = codeMat 64 := by
      unfold actionA
      rw [step109wc96s8_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step109wc96s8_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 161 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 64 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 64 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 64) = codeMat 8 := by
      unfold actionA
      rw [step109wc96s8_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 64 * (codeMat 161 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 2) = codeMat 4 := by
      unfold actionA
      rw [step109wc96s8_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 4 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 4) = codeMat 2 := by
      unfold actionA
      rw [step109wc96s8_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 4 * (codeMat 161 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 1 ∈ flatW_2 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc96s8_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc96_codeMat_mem_actionW_of_witness hw hact

theorem step109wc96s8Dispatch :
    QuotientRankAtLeast (o96SourceU_wc ⟨8, by omega⟩) 6 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 161) flatW_2) 6 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 161) hP hQ flatW_2 6
      flatSeed_2
  exact quotientRankAtLeast_mono step109wc96s8_contain hAct

theorem step109wc96_all_dispatch (i : Fin 9) :
    QuotientRankAtLeast (o96SourceU_wc i) (o96SourceLb_wc i) := by
  fin_cases i
  · exact step109wc96s0Dispatch
  · exact step109wc96s1Dispatch
  · exact step109wc96s2Dispatch
  · exact step109wc96s3Dispatch
  · exact step109wc96s4Dispatch
  · exact step109wc96s5Dispatch
  · exact step109wc96s6Dispatch
  · exact step109wc96s7Dispatch
  · exact step109wc96s8Dispatch

theorem step109_orbit96_lb16_wc : QuotientRankAtLeast o96W_wc 16 :=
  o96Lb16_wc step109wc96_all_dispatch

end QiushiMatmul
