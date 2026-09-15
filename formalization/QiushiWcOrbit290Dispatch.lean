import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit290Consumer
import QiushiWcOrbit156Dispatch
import QiushiMonoOrbit98From31T
import QiushiWcOrbit80Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiStep99Orbit65Dispatch
import QiushiOrbit10FP
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc290_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc290_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc290s0_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc290s0_contain :
    (o290SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 273) (codeMat 273) o156W_wc := by
  change spanCodes [68, 32, 20, 10, 1] ≤ actionW (codeMat 273) (codeMat 273) o156W_wc
  apply step109wc290_spanCodes_le_of_gens [68, 32, 20, 10, 1]
    (actionW (codeMat 273) (codeMat 273) o156W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 68 ∈ o156W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [68, 32, 20, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step109wc290s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 68 * (codeMat 273 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 32 ∈ o156W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [68, 32, 20, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 32) = codeMat 32 := by
      unfold actionA
      rw [step109wc290s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 32 * (codeMat 273 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 20 ∈ o156W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [68, 32, 20, 10, 1] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 20) = codeMat 20 := by
      unfold actionA
      rw [step109wc290s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * (codeMat 273 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 10 ∈ o156W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [68, 32, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step109wc290s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 10 * (codeMat 273 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o156W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [68, 32, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc290s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact

theorem step109wc290s0Dispatch :
    QuotientRankAtLeast (o290SourceU_wc ⟨0, by omega⟩) 16 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 273) o156W_wc) 16 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 273) hP hQ o156W_wc 16
      step109_orbit156_lb16_wc
  exact quotientRankAtLeast_mono step109wc290s0_contain hAct


private theorem step109wc290s1_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = (codeMat 275 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * (codeMat 275 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc290s1_contain :
    (o290SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 273) (codeMat 275) o156W_wc := by
  change spanCodes [68, 32, 22, 10, 1] ≤ actionW (codeMat 273) (codeMat 275) o156W_wc
  apply step109wc290_spanCodes_le_of_gens [68, 32, 22, 10, 1]
    (actionW (codeMat 273) (codeMat 275) o156W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 68 ∈ o156W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [68, 32, 20, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step109wc290s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 68 * (codeMat 275 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 32 ∈ o156W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [68, 32, 20, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 32) = codeMat 32 := by
      unfold actionA
      rw [step109wc290s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 32 * (codeMat 275 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 31 ∈ o156W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [68, 32, 20, 10, 1] 31 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 31) = codeMat 22 := by
      unfold actionA
      rw [step109wc290s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 31 * (codeMat 275 : Mat3).transpose = codeMat 22
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 11 ∈ o156W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [68, 32, 20, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 11) = codeMat 10 := by
      unfold actionA
      rw [step109wc290s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 11 * (codeMat 275 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o156W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [68, 32, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc290s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 275 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact

theorem step109wc290s1Dispatch :
    QuotientRankAtLeast (o290SourceU_wc ⟨1, by omega⟩) 16 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 275) o156W_wc) 16 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 275) hP hQ o156W_wc 16
      step109_orbit156_lb16_wc
  exact quotientRankAtLeast_mono step109wc290s1_contain hAct

private def step109wc290s2SrcT : Submodule F2 Mat3 := spanCodes [128, 68, 20, 10, 1]

private theorem step109wc290s2SrcT_lb : QuotientRankAtLeast step109wc290s2SrcT 16 := by
  have ht := quotientRankAtLeast_transpose step109_orbit156_lb16_wc
  have hle : step109wc290s2SrcT ≤ transposeW o156W_wc := by
    unfold step109wc290s2SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4
    · subst h0
      show codeMat 128 ∈ Submodule.map transposeLinearMap o156W_wc
      exact ⟨codeMat 32, spanContainsCodeCore_implies_mem_spanCodes [68, 32, 20, 10, 1] 32 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 68 ∈ Submodule.map transposeLinearMap o156W_wc
      exact ⟨codeMat 68, spanContainsCodeCore_implies_mem_spanCodes [68, 32, 20, 10, 1] 68 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 20 ∈ Submodule.map transposeLinearMap o156W_wc
      exact ⟨codeMat 80, spanContainsCodeCore_implies_mem_spanCodes [68, 32, 20, 10, 1] 80 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 10 ∈ Submodule.map transposeLinearMap o156W_wc
      exact ⟨codeMat 10, spanContainsCodeCore_implies_mem_spanCodes [68, 32, 20, 10, 1] 10 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 1 ∈ Submodule.map transposeLinearMap o156W_wc
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [68, 32, 20, 10, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc290s2_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc290s2_contain :
    (o290SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 161) (codeMat 161) step109wc290s2SrcT := by
  change spanCodes [258, 68, 32, 10, 1] ≤ actionW (codeMat 161) (codeMat 161) step109wc290s2SrcT
  apply step109wc290_spanCodes_le_of_gens [258, 68, 32, 10, 1]
    (actionW (codeMat 161) (codeMat 161) step109wc290s2SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 20 ∈ step109wc290s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 20, 10, 1] 20 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 20) = codeMat 258 := by
      unfold actionA
      rw [step109wc290s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 20 * (codeMat 161 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 10 ∈ step109wc290s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 10) = codeMat 68 := by
      unfold actionA
      rw [step109wc290s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 10 * (codeMat 161 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 128 ∈ step109wc290s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 128) = codeMat 32 := by
      unfold actionA
      rw [step109wc290s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 128 * (codeMat 161 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 68 ∈ step109wc290s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 20, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 68) = codeMat 10 := by
      unfold actionA
      rw [step109wc290s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 68 * (codeMat 161 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ step109wc290s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc290s2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact

theorem step109wc290s2Dispatch :
    QuotientRankAtLeast (o290SourceU_wc ⟨2, by omega⟩) 16 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 161) step109wc290s2SrcT) 16 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 161) hP hQ step109wc290s2SrcT 16
      step109wc290s2SrcT_lb
  exact quotientRankAtLeast_mono step109wc290s2_contain hAct

private def step109wc290s3SrcT : Submodule F2 Mat3 := spanCodes [128, 68, 20, 10, 1]

private theorem step109wc290s3SrcT_lb : QuotientRankAtLeast step109wc290s3SrcT 16 := by
  have ht := quotientRankAtLeast_transpose step109_orbit156_lb16_wc
  have hle : step109wc290s3SrcT ≤ transposeW o156W_wc := by
    unfold step109wc290s3SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4
    · subst h0
      show codeMat 128 ∈ Submodule.map transposeLinearMap o156W_wc
      exact ⟨codeMat 32, spanContainsCodeCore_implies_mem_spanCodes [68, 32, 20, 10, 1] 32 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 68 ∈ Submodule.map transposeLinearMap o156W_wc
      exact ⟨codeMat 68, spanContainsCodeCore_implies_mem_spanCodes [68, 32, 20, 10, 1] 68 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 20 ∈ Submodule.map transposeLinearMap o156W_wc
      exact ⟨codeMat 80, spanContainsCodeCore_implies_mem_spanCodes [68, 32, 20, 10, 1] 80 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 10 ∈ Submodule.map transposeLinearMap o156W_wc
      exact ⟨codeMat 10, spanContainsCodeCore_implies_mem_spanCodes [68, 32, 20, 10, 1] 10 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 1 ∈ Submodule.map transposeLinearMap o156W_wc
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [68, 32, 20, 10, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc290s3_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc290s3_contain :
    (o290SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 169) (codeMat 161) step109wc290s3SrcT := by
  change spanCodes [262, 68, 32, 10, 1] ≤ actionW (codeMat 169) (codeMat 161) step109wc290s3SrcT
  apply step109wc290_spanCodes_le_of_gens [262, 68, 32, 10, 1]
    (actionW (codeMat 169) (codeMat 161) step109wc290s3SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 20 ∈ step109wc290s3SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 20, 10, 1] 20 (by decide)
    have hact : actionA (codeMat 169) (codeMat 161) (codeMat 20) = codeMat 262 := by
      unfold actionA
      rw [step109wc290s3_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 20 * (codeMat 161 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 11 ∈ step109wc290s3SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 20, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 169) (codeMat 161) (codeMat 11) = codeMat 68 := by
      unfold actionA
      rw [step109wc290s3_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 11 * (codeMat 161 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 128 ∈ step109wc290s3SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 169) (codeMat 161) (codeMat 128) = codeMat 32 := by
      unfold actionA
      rw [step109wc290s3_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 128 * (codeMat 161 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 68 ∈ step109wc290s3SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 20, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 169) (codeMat 161) (codeMat 68) = codeMat 10 := by
      unfold actionA
      rw [step109wc290s3_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 68 * (codeMat 161 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ step109wc290s3SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc290s3_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact

theorem step109wc290s3Dispatch :
    QuotientRankAtLeast (o290SourceU_wc ⟨3, by omega⟩) 16 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 161) step109wc290s3SrcT) 16 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 161) hP hQ step109wc290s3SrcT 16
      step109wc290s3SrcT_lb
  exact quotientRankAtLeast_mono step109wc290s3_contain hAct

private def step109wc290s4SrcT : Submodule F2 Mat3 := spanCodes [80, 32, 8, 2, 1]

private theorem step109wc290s4SrcT_lb : QuotientRankAtLeast step109wc290s4SrcT 15 := by
  have ht := quotientRankAtLeast_transpose orbit98_lb15_mono
  have hle : step109wc290s4SrcT ≤ transposeW o98W_mono := by
    unfold step109wc290s4SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4
    · subst h0
      show codeMat 80 ∈ Submodule.map transposeLinearMap o98W_mono
      exact ⟨codeMat 20, spanContainsCodeCore_implies_mem_spanCodes [128, 20, 8, 2, 1] 20 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 32 ∈ Submodule.map transposeLinearMap o98W_mono
      exact ⟨codeMat 128, spanContainsCodeCore_implies_mem_spanCodes [128, 20, 8, 2, 1] 128 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 8 ∈ Submodule.map transposeLinearMap o98W_mono
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [128, 20, 8, 2, 1] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 2 ∈ Submodule.map transposeLinearMap o98W_mono
      exact ⟨codeMat 8, spanContainsCodeCore_implies_mem_spanCodes [128, 20, 8, 2, 1] 8 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 1 ∈ Submodule.map transposeLinearMap o98W_mono
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [128, 20, 8, 2, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc290s4_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc290s4_contain :
    (o290SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 266) (codeMat 161) step109wc290s4SrcT := by
  change spanCodes [68, 32, 8, 2, 1] ≤ actionW (codeMat 266) (codeMat 161) step109wc290s4SrcT
  apply step109wc290_spanCodes_le_of_gens [68, 32, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 161) step109wc290s4SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 80 ∈ step109wc290s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [80, 32, 8, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 80) = codeMat 68 := by
      unfold actionA
      rw [step109wc290s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 80 * (codeMat 161 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ step109wc290s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [80, 32, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [step109wc290s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ step109wc290s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [80, 32, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step109wc290s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ step109wc290s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [80, 32, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 32) = codeMat 2 := by
      unfold actionA
      rw [step109wc290s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 161 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ step109wc290s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [80, 32, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc290s4_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact

theorem step109wc290s4Dispatch :
    QuotientRankAtLeast (o290SourceU_wc ⟨4, by omega⟩) 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 161) step109wc290s4SrcT) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 161) hP hQ step109wc290s4SrcT 15
      step109wc290s4SrcT_lb
  exact quotientRankAtLeast_mono step109wc290s4_contain hAct


private theorem step109wc290s5_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc290s5_contain :
    (o290SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 273) (codeMat 140) o98W_mono := by
  change spanCodes [64, 32, 10, 4, 1] ≤ actionW (codeMat 273) (codeMat 140) o98W_mono
  apply step109wc290_spanCodes_le_of_gens [64, 32, 10, 4, 1]
    (actionW (codeMat 273) (codeMat 140) o98W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 128 ∈ o98W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 128) = codeMat 64 := by
      unfold actionA
      rw [step109wc290s5_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 128 * (codeMat 98 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ o98W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc290s5_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 20 ∈ o98W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 20, 8, 2, 1] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 20) = codeMat 10 := by
      unfold actionA
      rw [step109wc290s5_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * (codeMat 98 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o98W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step109wc290s5_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o98W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc290s5_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact

theorem step109wc290s5Dispatch :
    QuotientRankAtLeast (o290SourceU_wc ⟨5, by omega⟩) 15 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 140) o98W_mono) 15 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 140) hP hQ o98W_mono 15
      orbit98_lb15_mono
  exact quotientRankAtLeast_mono step109wc290s5_contain hAct


private theorem step109wc290s6_QtInv :
    (codeMat 236 : Mat3).transpose⁻¹ = (codeMat 123 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 236 : Mat3).transpose * (codeMat 123 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc290s6_contain :
    (o290SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 157) (codeMat 236) o80W_wc := by
  change spanCodes [272, 146, 68, 32, 10, 1] ≤ actionW (codeMat 157) (codeMat 236) o80W_wc
  apply step109wc290_spanCodes_le_of_gens [272, 146, 68, 32, 10, 1]
    (actionW (codeMat 157) (codeMat 236) o80W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 475 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 475 (by decide)
    have hact : actionA (codeMat 157) (codeMat 236) (codeMat 475) = codeMat 272 := by
      unfold actionA
      rw [step109wc290s6_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 475 * (codeMat 123 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 260 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 157) (codeMat 236) (codeMat 260) = codeMat 146 := by
      unfold actionA
      rw [step109wc290s6_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 260 * (codeMat 123 : Mat3).transpose = codeMat 146
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 366 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 366 (by decide)
    have hact : actionA (codeMat 157) (codeMat 236) (codeMat 366) = codeMat 68 := by
      unfold actionA
      rw [step109wc290s6_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 366 * (codeMat 123 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 192 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 192 (by decide)
    have hact : actionA (codeMat 157) (codeMat 236) (codeMat 192) = codeMat 32 := by
      unfold actionA
      rw [step109wc290s6_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 192 * (codeMat 123 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 157) (codeMat 236) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc290s6_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 160 * (codeMat 123 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 432 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 432 (by decide)
    have hact : actionA (codeMat 157) (codeMat 236) (codeMat 432) = codeMat 1 := by
      unfold actionA
      rw [step109wc290s6_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 432 * (codeMat 123 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact

theorem step109wc290s6Dispatch :
    QuotientRankAtLeast (o290SourceU_wc ⟨6, by omega⟩) 15 := by
  have hP : Invertible (codeMat 157 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 236 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 157) (codeMat 236) o80W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 157) (codeMat 236) hP hQ o80W_wc 15
      step109_orbit80_lb15_wc
  exact quotientRankAtLeast_mono step109wc290s6_contain hAct


private theorem step109wc290s7_QtInv :
    (codeMat 226 : Mat3).transpose⁻¹ = (codeMat 141 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 226 : Mat3).transpose * (codeMat 141 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc290s7_contain :
    (o290SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 86) (codeMat 226) o69W := by
  change spanCodes [274, 150, 68, 32, 10, 1] ≤ actionW (codeMat 86) (codeMat 226) o69W
  apply step109wc290_spanCodes_le_of_gens [274, 150, 68, 32, 10, 1]
    (actionW (codeMat 86) (codeMat 226) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 378 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 378 (by decide)
    have hact : actionA (codeMat 86) (codeMat 226) (codeMat 378) = codeMat 274 := by
      unfold actionA
      rw [step109wc290s7_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 378 * (codeMat 141 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 453 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 453 (by decide)
    have hact : actionA (codeMat 86) (codeMat 226) (codeMat 453) = codeMat 150 := by
      unfold actionA
      rw [step109wc290s7_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 453 * (codeMat 141 : Mat3).transpose = codeMat 150
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 164 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 164 (by decide)
    have hact : actionA (codeMat 86) (codeMat 226) (codeMat 164) = codeMat 68 := by
      unfold actionA
      rw [step109wc290s7_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 164 * (codeMat 141 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 86) (codeMat 226) (codeMat 16) = codeMat 32 := by
      unfold actionA
      rw [step109wc290s7_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 16 * (codeMat 141 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 352 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 352 (by decide)
    have hact : actionA (codeMat 86) (codeMat 226) (codeMat 352) = codeMat 10 := by
      unfold actionA
      rw [step109wc290s7_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 352 * (codeMat 141 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 256 (by decide)
    have hact : actionA (codeMat 86) (codeMat 226) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc290s7_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 256 * (codeMat 141 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact

theorem step109wc290s7Dispatch :
    QuotientRankAtLeast (o290SourceU_wc ⟨7, by omega⟩) 15 := by
  have hP : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 226 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 86) (codeMat 226) o69W) 15 :=
    @quotientRankAtLeast_action (codeMat 86) (codeMat 226) hP hQ o69W 15
      step99_orbit69_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc290s7_contain hAct

private def step109wc290s8SrcT : Submodule F2 Mat3 := spanCodes [272, 132, 80, 36, 10, 1]

private theorem step109wc290s8SrcT_lb : QuotientRankAtLeast step109wc290s8SrcT 15 := by
  have ht := quotientRankAtLeast_transpose step109_orbit80_lb15_wc
  have hle : step109wc290s8SrcT ≤ transposeW o80W_wc := by
    unfold step109wc290s8SrcT transposeW
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

private theorem step109wc290s8_QtInv :
    (codeMat 460 : Mat3).transpose⁻¹ = (codeMat 122 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 460 : Mat3).transpose * (codeMat 122 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc290s8_contain :
    (o290SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 157) (codeMat 460) step109wc290s8SrcT := by
  change spanCodes [278, 144, 68, 32, 10, 1] ≤ actionW (codeMat 157) (codeMat 460) step109wc290s8SrcT
  apply step109wc290_spanCodes_le_of_gens [278, 144, 68, 32, 10, 1]
    (actionW (codeMat 157) (codeMat 460) step109wc290s8SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 37 ∈ step109wc290s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 36, 10, 1] 37 (by decide)
    have hact : actionA (codeMat 157) (codeMat 460) (codeMat 37) = codeMat 278 := by
      unfold actionA
      rw [step109wc290s8_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 37 * (codeMat 122 : Mat3).transpose = codeMat 278
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 36 ∈ step109wc290s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 36, 10, 1] 36 (by decide)
    have hact : actionA (codeMat 157) (codeMat 460) (codeMat 36) = codeMat 144 := by
      unfold actionA
      rw [step109wc290s8_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 36 * (codeMat 122 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 222 ∈ step109wc290s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 36, 10, 1] 222 (by decide)
    have hact : actionA (codeMat 157) (codeMat 460) (codeMat 222) = codeMat 68 := by
      unfold actionA
      rw [step109wc290s8_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 222 * (codeMat 122 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 320 ∈ step109wc290s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 36, 10, 1] 320 (by decide)
    have hact : actionA (codeMat 157) (codeMat 460) (codeMat 320) = codeMat 32 := by
      unfold actionA
      rw [step109wc290s8_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 320 * (codeMat 122 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ step109wc290s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 36, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 157) (codeMat 460) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc290s8_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 160 * (codeMat 122 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 432 ∈ step109wc290s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 36, 10, 1] 432 (by decide)
    have hact : actionA (codeMat 157) (codeMat 460) (codeMat 432) = codeMat 1 := by
      unfold actionA
      rw [step109wc290s8_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 432 * (codeMat 122 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact

theorem step109wc290s8Dispatch :
    QuotientRankAtLeast (o290SourceU_wc ⟨8, by omega⟩) 15 := by
  have hP : Invertible (codeMat 157 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 460 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 157) (codeMat 460) step109wc290s8SrcT) 15 :=
    @quotientRankAtLeast_action (codeMat 157) (codeMat 460) hP hQ step109wc290s8SrcT 15
      step109wc290s8SrcT_lb
  exact quotientRankAtLeast_mono step109wc290s8_contain hAct


private theorem step109wc290s9_QtInv :
    (codeMat 396 : Mat3).transpose⁻¹ = (codeMat 106 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 396 : Mat3).transpose * (codeMat 106 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc290s9_contain :
    (o290SourceU_wc ⟨9, by omega⟩) ≤ actionW (codeMat 142) (codeMat 396) o65W := by
  change spanCodes [272, 128, 68, 32, 10, 1] ≤ actionW (codeMat 142) (codeMat 396) o65W
  apply step109wc290_spanCodes_le_of_gens [272, 128, 68, 32, 10, 1]
    (actionW (codeMat 142) (codeMat 396) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 69 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 69) = codeMat 272 := by
      unfold actionA
      rw [step109wc290s9_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 69 * (codeMat 106 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 260 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 260) = codeMat 128 := by
      unfold actionA
      rw [step109wc290s9_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 260 * (codeMat 106 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 170 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 170 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 170) = codeMat 68 := by
      unfold actionA
      rw [step109wc290s9_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 170 * (codeMat 106 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 320 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 320 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 320) = codeMat 32 := by
      unfold actionA
      rw [step109wc290s9_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 320 * (codeMat 106 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc290s9_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 160 * (codeMat 106 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc290s9_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 16 * (codeMat 106 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact

theorem step109wc290s9Dispatch :
    QuotientRankAtLeast (o290SourceU_wc ⟨9, by omega⟩) 15 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 396 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 396) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 396) hP hQ o65W 15
      step99_orbit65_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc290s9_contain hAct


private theorem step109wc290s10_QtInv :
    (codeMat 412 : Mat3).transpose⁻¹ = (codeMat 111 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 412 : Mat3).transpose * (codeMat 111 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc290s10_contain :
    (o290SourceU_wc ⟨10, by omega⟩) ≤ actionW (codeMat 143) (codeMat 412) o65W := by
  change spanCodes [278, 134, 68, 32, 10, 1] ≤ actionW (codeMat 143) (codeMat 412) o65W
  apply step109wc290_spanCodes_le_of_gens [278, 134, 68, 32, 10, 1]
    (actionW (codeMat 143) (codeMat 412) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 245 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 245 (by decide)
    have hact : actionA (codeMat 143) (codeMat 412) (codeMat 245) = codeMat 278 := by
      unfold actionA
      rw [step109wc290s10_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 245 * (codeMat 111 : Mat3).transpose = codeMat 278
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 430 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 430 (by decide)
    have hact : actionA (codeMat 143) (codeMat 412) (codeMat 430) = codeMat 134 := by
      unfold actionA
      rw [step109wc290s10_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 430 * (codeMat 111 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 186 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 186 (by decide)
    have hact : actionA (codeMat 143) (codeMat 412) (codeMat 186) = codeMat 68 := by
      unfold actionA
      rw [step109wc290s10_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 186 * (codeMat 111 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 320 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 320 (by decide)
    have hact : actionA (codeMat 143) (codeMat 412) (codeMat 320) = codeMat 32 := by
      unfold actionA
      rw [step109wc290s10_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 320 * (codeMat 111 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 176 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 176 (by decide)
    have hact : actionA (codeMat 143) (codeMat 412) (codeMat 176) = codeMat 10 := by
      unfold actionA
      rw [step109wc290s10_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 176 * (codeMat 111 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 143) (codeMat 412) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc290s10_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 16 * (codeMat 111 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact

theorem step109wc290s10Dispatch :
    QuotientRankAtLeast (o290SourceU_wc ⟨10, by omega⟩) 15 := by
  have hP : Invertible (codeMat 143 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 412 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 143) (codeMat 412) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 143) (codeMat 412) hP hQ o65W 15
      step99_orbit65_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc290s10_contain hAct


private theorem step109wc290s11_QtInv :
    (codeMat 412 : Mat3).transpose⁻¹ = (codeMat 111 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 412 : Mat3).transpose * (codeMat 111 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc290s11_contain :
    (o290SourceU_wc ⟨11, by omega⟩) ≤ actionW (codeMat 142) (codeMat 412) o65W := by
  change spanCodes [274, 132, 68, 32, 10, 1] ≤ actionW (codeMat 142) (codeMat 412) o65W
  apply step109wc290_spanCodes_le_of_gens [274, 132, 68, 32, 10, 1]
    (actionW (codeMat 142) (codeMat 412) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 245 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 245 (by decide)
    have hact : actionA (codeMat 142) (codeMat 412) (codeMat 245) = codeMat 274 := by
      unfold actionA
      rw [step109wc290s11_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 245 * (codeMat 111 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 430 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 430 (by decide)
    have hact : actionA (codeMat 142) (codeMat 412) (codeMat 430) = codeMat 132 := by
      unfold actionA
      rw [step109wc290s11_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 430 * (codeMat 111 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 170 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 170 (by decide)
    have hact : actionA (codeMat 142) (codeMat 412) (codeMat 170) = codeMat 68 := by
      unfold actionA
      rw [step109wc290s11_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 170 * (codeMat 111 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 320 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 320 (by decide)
    have hact : actionA (codeMat 142) (codeMat 412) (codeMat 320) = codeMat 32 := by
      unfold actionA
      rw [step109wc290s11_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 320 * (codeMat 111 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 176 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 176 (by decide)
    have hact : actionA (codeMat 142) (codeMat 412) (codeMat 176) = codeMat 10 := by
      unfold actionA
      rw [step109wc290s11_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 176 * (codeMat 111 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 142) (codeMat 412) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc290s11_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 16 * (codeMat 111 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact

theorem step109wc290s11Dispatch :
    QuotientRankAtLeast (o290SourceU_wc ⟨11, by omega⟩) 15 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 412 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 412) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 412) hP hQ o65W 15
      step99_orbit65_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc290s11_contain hAct


private theorem step109wc290s12_QtInv :
    (codeMat 396 : Mat3).transpose⁻¹ = (codeMat 106 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 396 : Mat3).transpose * (codeMat 106 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc290s12_contain :
    (o290SourceU_wc ⟨12, by omega⟩) ≤ actionW (codeMat 143) (codeMat 396) o65W := by
  change spanCodes [276, 130, 68, 32, 10, 1] ≤ actionW (codeMat 143) (codeMat 396) o65W
  apply step109wc290_spanCodes_le_of_gens [276, 130, 68, 32, 10, 1]
    (actionW (codeMat 143) (codeMat 396) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 69 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 143) (codeMat 396) (codeMat 69) = codeMat 276 := by
      unfold actionA
      rw [step109wc290s12_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 69 * (codeMat 106 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 260 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 143) (codeMat 396) (codeMat 260) = codeMat 130 := by
      unfold actionA
      rw [step109wc290s12_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 260 * (codeMat 106 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 186 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 186 (by decide)
    have hact : actionA (codeMat 143) (codeMat 396) (codeMat 186) = codeMat 68 := by
      unfold actionA
      rw [step109wc290s12_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 186 * (codeMat 106 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 320 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 320 (by decide)
    have hact : actionA (codeMat 143) (codeMat 396) (codeMat 320) = codeMat 32 := by
      unfold actionA
      rw [step109wc290s12_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 320 * (codeMat 106 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 143) (codeMat 396) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc290s12_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 160 * (codeMat 106 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 143) (codeMat 396) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc290s12_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 16 * (codeMat 106 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact

theorem step109wc290s12Dispatch :
    QuotientRankAtLeast (o290SourceU_wc ⟨12, by omega⟩) 15 := by
  have hP : Invertible (codeMat 143 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 396 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 143) (codeMat 396) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 143) (codeMat 396) hP hQ o65W 15
      step99_orbit65_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc290s12_contain hAct


private theorem step109wc290s13_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc290s13_contain :
    (o290SourceU_wc ⟨13, by omega⟩) ≤ actionW (codeMat 84) (codeMat 84) orbit10W := by
  change spanCodes [256, 128, 68, 32, 16, 10, 1] ≤ actionW (codeMat 84) (codeMat 84) orbit10W
  apply step109wc290_spanCodes_le_of_gens [256, 128, 68, 32, 16, 10, 1]
    (actionW (codeMat 84) (codeMat 84) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc290s13_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 2) = codeMat 128 := by
      unfold actionA
      rw [step109wc290s13_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step109wc290s13_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 68 * (codeMat 84 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc290s13_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 84 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 16) = codeMat 16 := by
      unfold actionA
      rw [step109wc290s13_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 16 * (codeMat 84 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc290s13_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 160 * (codeMat 84 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc290s13_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact

theorem step109wc290s13Dispatch :
    QuotientRankAtLeast (o290SourceU_wc ⟨13, by omega⟩) 12 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 84) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 84) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc290s13_contain hAct


private theorem step109wc290s14_QtInv :
    (codeMat 212 : Mat3).transpose⁻¹ = (codeMat 86 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 212 : Mat3).transpose * (codeMat 86 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc290s14_contain :
    (o290SourceU_wc ⟨14, by omega⟩) ≤ actionW (codeMat 85) (codeMat 212) orbit10W := by
  change spanCodes [260, 134, 68, 32, 18, 10, 1] ≤ actionW (codeMat 85) (codeMat 212) orbit10W
  apply step109wc290_spanCodes_le_of_gens [260, 134, 68, 32, 18, 10, 1]
    (actionW (codeMat 85) (codeMat 212) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 85) (codeMat 212) (codeMat 1) = codeMat 260 := by
      unfold actionA
      rw [step109wc290s14_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 1 * (codeMat 86 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 70 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 70 (by decide)
    have hact : actionA (codeMat 85) (codeMat 212) (codeMat 70) = codeMat 134 := by
      unfold actionA
      rw [step109wc290s14_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 70 * (codeMat 86 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 324 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 324 (by decide)
    have hact : actionA (codeMat 85) (codeMat 212) (codeMat 324) = codeMat 68 := by
      unfold actionA
      rw [step109wc290s14_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 324 * (codeMat 86 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 85) (codeMat 212) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc290s14_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 8 * (codeMat 86 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 432 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide)
    have hact : actionA (codeMat 85) (codeMat 212) (codeMat 432) = codeMat 18 := by
      unfold actionA
      rw [step109wc290s14_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 432 * (codeMat 86 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 416 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 416 (by decide)
    have hact : actionA (codeMat 85) (codeMat 212) (codeMat 416) = codeMat 10 := by
      unfold actionA
      rw [step109wc290s14_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 416 * (codeMat 86 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 85) (codeMat 212) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc290s14_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 256 * (codeMat 86 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact

theorem step109wc290s14Dispatch :
    QuotientRankAtLeast (o290SourceU_wc ⟨14, by omega⟩) 12 := by
  have hP : Invertible (codeMat 85 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 212 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 85) (codeMat 212) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 85) (codeMat 212) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc290s14_contain hAct


private theorem step109wc290s15_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc290s15_contain :
    (o290SourceU_wc ⟨15, by omega⟩) ≤ actionW (codeMat 85) (codeMat 84) orbit10W := by
  change spanCodes [260, 130, 68, 32, 16, 10, 1] ≤ actionW (codeMat 85) (codeMat 84) orbit10W
  apply step109wc290_spanCodes_le_of_gens [260, 130, 68, 32, 16, 10, 1]
    (actionW (codeMat 85) (codeMat 84) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 85) (codeMat 84) (codeMat 1) = codeMat 260 := by
      unfold actionA
      rw [step109wc290s15_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 85) (codeMat 84) (codeMat 2) = codeMat 130 := by
      unfold actionA
      rw [step109wc290s15_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 324 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 324 (by decide)
    have hact : actionA (codeMat 85) (codeMat 84) (codeMat 324) = codeMat 68 := by
      unfold actionA
      rw [step109wc290s15_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 324 * (codeMat 84 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 85) (codeMat 84) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc290s15_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 8 * (codeMat 84 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 85) (codeMat 84) (codeMat 16) = codeMat 16 := by
      unfold actionA
      rw [step109wc290s15_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 16 * (codeMat 84 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 85) (codeMat 84) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc290s15_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 160 * (codeMat 84 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 85) (codeMat 84) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc290s15_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 256 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact

theorem step109wc290s15Dispatch :
    QuotientRankAtLeast (o290SourceU_wc ⟨15, by omega⟩) 12 := by
  have hP : Invertible (codeMat 85 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 85) (codeMat 84) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 85) (codeMat 84) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc290s15_contain hAct


private theorem step109wc290s16_QtInv :
    (codeMat 334 : Mat3).transpose⁻¹ = (codeMat 442 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 334 : Mat3).transpose * (codeMat 442 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc290s16_contain :
    (o290SourceU_wc ⟨16, by omega⟩) ≤ actionW (codeMat 84) (codeMat 334) flatW_3 := by
  change spanCodes [258, 128, 66, 32, 16, 10, 6, 1] ≤ actionW (codeMat 84) (codeMat 334) flatW_3
  apply step109wc290_spanCodes_le_of_gens [258, 128, 66, 32, 16, 10, 6, 1]
    (actionW (codeMat 84) (codeMat 334) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 69 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 69 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 69) = codeMat 258 := by
      unfold actionA
      rw [step109wc290s16_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 69 * (codeMat 442 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step109wc290s16_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 442 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 70 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 70 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 70) = codeMat 66 := by
      unfold actionA
      rw [step109wc290s16_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 70 * (codeMat 442 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 40 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 40) = codeMat 32 := by
      unfold actionA
      rw [step109wc290s16_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 442 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step109wc290s16_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 442 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 112 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 112 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 112) = codeMat 10 := by
      unfold actionA
      rw [step109wc290s16_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 112 * (codeMat 442 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 256) = codeMat 6 := by
      unfold actionA
      rw [step109wc290s16_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 442 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step109wc290s16_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 442 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact

theorem step109wc290s16Dispatch :
    QuotientRankAtLeast (o290SourceU_wc ⟨16, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 334 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 334) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 334) hP hQ flatW_3 9
      flatSeed_3
  exact quotientRankAtLeast_mono step109wc290s16_contain hAct


private theorem step109wc290s17_QtInv :
    (codeMat 206 : Mat3).transpose⁻¹ = (codeMat 498 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 206 : Mat3).transpose * (codeMat 498 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc290s17_contain :
    (o290SourceU_wc ⟨17, by omega⟩) ≤ actionW (codeMat 84) (codeMat 206) flatW_3 := by
  change spanCodes [256, 130, 66, 32, 16, 10, 6, 1] ≤ actionW (codeMat 84) (codeMat 206) flatW_3
  apply step109wc290_spanCodes_le_of_gens [256, 130, 66, 32, 16, 10, 6, 1]
    (actionW (codeMat 84) (codeMat 206) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc290s17_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 498 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 325 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 325 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 325) = codeMat 130 := by
      unfold actionA
      rw [step109wc290s17_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 325 * (codeMat 498 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 326 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 326 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 326) = codeMat 66 := by
      unfold actionA
      rw [step109wc290s17_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 326 * (codeMat 498 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc290s17_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 498 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 40 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 40) = codeMat 16 := by
      unfold actionA
      rw [step109wc290s17_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 498 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 368 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 368 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 368) = codeMat 10 := by
      unfold actionA
      rw [step109wc290s17_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 368 * (codeMat 498 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 256) = codeMat 6 := by
      unfold actionA
      rw [step109wc290s17_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 498 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 206) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step109wc290s17_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 498 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact

theorem step109wc290s17Dispatch :
    QuotientRankAtLeast (o290SourceU_wc ⟨17, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 206 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 206) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 206) hP hQ flatW_3 9
      flatSeed_3
  exact quotientRankAtLeast_mono step109wc290s17_contain hAct


private theorem step109wc290s18_QtInv :
    (codeMat 94 : Mat3).transpose⁻¹ = (codeMat 500 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 94 : Mat3).transpose * (codeMat 500 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc290s18_contain :
    (o290SourceU_wc ⟨18, by omega⟩) ≤ actionW (codeMat 84) (codeMat 94) flatW_3 := by
  change spanCodes [256, 128, 66, 32, 18, 10, 6, 1] ≤ actionW (codeMat 84) (codeMat 94) flatW_3
  apply step109wc290_spanCodes_le_of_gens [256, 128, 66, 32, 18, 10, 6, 1]
    (actionW (codeMat 84) (codeMat 94) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 94) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc290s18_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 500 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 3 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 84) (codeMat 94) (codeMat 3) = codeMat 128 := by
      unfold actionA
      rw [step109wc290s18_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 3 * (codeMat 500 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 198 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 198 (by decide)
    have hact : actionA (codeMat 84) (codeMat 94) (codeMat 198) = codeMat 66 := by
      unfold actionA
      rw [step109wc290s18_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 198 * (codeMat 500 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 94) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc290s18_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 500 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 216 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 216 (by decide)
    have hact : actionA (codeMat 84) (codeMat 94) (codeMat 216) = codeMat 18 := by
      unfold actionA
      rw [step109wc290s18_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 216 * (codeMat 500 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 240 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 240 (by decide)
    have hact : actionA (codeMat 84) (codeMat 94) (codeMat 240) = codeMat 10 := by
      unfold actionA
      rw [step109wc290s18_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 240 * (codeMat 500 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 94) (codeMat 128) = codeMat 6 := by
      unfold actionA
      rw [step109wc290s18_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 500 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 94) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step109wc290s18_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 500 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact

theorem step109wc290s18Dispatch :
    QuotientRankAtLeast (o290SourceU_wc ⟨18, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 94 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 94) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 94) hP hQ flatW_3 9
      flatSeed_3
  exact quotientRankAtLeast_mono step109wc290s18_contain hAct


private theorem step109wc290s19_QtInv :
    (codeMat 478 : Mat3).transpose⁻¹ = (codeMat 445 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 478 : Mat3).transpose * (codeMat 445 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc290s19_contain :
    (o290SourceU_wc ⟨19, by omega⟩) ≤ actionW (codeMat 84) (codeMat 478) flatW_3 := by
  change spanCodes [258, 130, 66, 32, 18, 10, 6, 1] ≤ actionW (codeMat 84) (codeMat 478) flatW_3
  apply step109wc290_spanCodes_le_of_gens [258, 130, 66, 32, 18, 10, 6, 1]
    (actionW (codeMat 84) (codeMat 478) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 453 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 453 (by decide)
    have hact : actionA (codeMat 84) (codeMat 478) (codeMat 453) = codeMat 258 := by
      unfold actionA
      rw [step109wc290s19_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 453 * (codeMat 445 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 455 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 455 (by decide)
    have hact : actionA (codeMat 84) (codeMat 478) (codeMat 455) = codeMat 130 := by
      unfold actionA
      rw [step109wc290s19_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 455 * (codeMat 445 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 454 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 454 (by decide)
    have hact : actionA (codeMat 84) (codeMat 478) (codeMat 454) = codeMat 66 := by
      unfold actionA
      rw [step109wc290s19_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 454 * (codeMat 445 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 40 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 84) (codeMat 478) (codeMat 40) = codeMat 32 := by
      unfold actionA
      rw [step109wc290s19_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 445 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 504 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 504 (by decide)
    have hact : actionA (codeMat 84) (codeMat 478) (codeMat 504) = codeMat 18 := by
      unfold actionA
      rw [step109wc290s19_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 504 * (codeMat 445 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 496 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 496 (by decide)
    have hact : actionA (codeMat 84) (codeMat 478) (codeMat 496) = codeMat 10 := by
      unfold actionA
      rw [step109wc290s19_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 496 * (codeMat 445 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 478) (codeMat 128) = codeMat 6 := by
      unfold actionA
      rw [step109wc290s19_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 445 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 478) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step109wc290s19_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 445 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc290_codeMat_mem_actionW_of_witness hw hact

theorem step109wc290s19Dispatch :
    QuotientRankAtLeast (o290SourceU_wc ⟨19, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 478 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 478) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 478) hP hQ flatW_3 9
      flatSeed_3
  exact quotientRankAtLeast_mono step109wc290s19_contain hAct

theorem step109wc290_all_dispatch (i : Fin 20) :
    QuotientRankAtLeast (o290SourceU_wc i) (o290SourceLb_wc i) := by
  fin_cases i
  · exact step109wc290s0Dispatch
  · exact step109wc290s1Dispatch
  · exact step109wc290s2Dispatch
  · exact step109wc290s3Dispatch
  · exact step109wc290s4Dispatch
  · exact step109wc290s5Dispatch
  · exact step109wc290s6Dispatch
  · exact step109wc290s7Dispatch
  · exact step109wc290s8Dispatch
  · exact step109wc290s9Dispatch
  · exact step109wc290s10Dispatch
  · exact step109wc290s11Dispatch
  · exact step109wc290s12Dispatch
  · exact step109wc290s13Dispatch
  · exact step109wc290s14Dispatch
  · exact step109wc290s15Dispatch
  · exact step109wc290s16Dispatch
  · exact step109wc290s17Dispatch
  · exact step109wc290s18Dispatch
  · exact step109wc290s19Dispatch

theorem step109_orbit290_lb17_wc : QuotientRankAtLeast o290W_wc 17 :=
  o290Lb17_wc step109wc290_all_dispatch

end QiushiMatmul
