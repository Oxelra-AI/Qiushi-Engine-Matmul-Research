import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit374Consumer
import QiushiWcOrbit214Dispatch
import QiushiStep99Orbit237Dispatch
import QiushiWcOrbit63Dispatch
import QiushiOrbit10FP

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc374_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc374_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

private def step109wc374s0SrcT : Submodule F2 Mat3 := spanCodes [306, 132, 96, 10, 1]

private theorem step109wc374s0SrcT_lb : QuotientRankAtLeast step109wc374s0SrcT 16 := by
  have ht := quotientRankAtLeast_transpose step109_orbit214_lb16_wc
  have hle : step109wc374s0SrcT ≤ transposeW o214W_wc := by
    unfold step109wc374s0SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4
    · subst h0
      show codeMat 306 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 408, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 408 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 132 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 96, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 96 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 96 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 132, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 132 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 10 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 10, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 10 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 1 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc374s0_QtInv :
    (codeMat 167 : Mat3).transpose⁻¹ = (codeMat 167 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 167 : Mat3).transpose * (codeMat 167 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc374s0_contain :
    (o374SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 273) (codeMat 167) step109wc374s0SrcT := by
  change spanCodes [278, 160, 84, 12, 1] ≤ actionW (codeMat 273) (codeMat 167) step109wc374s0SrcT
  apply step109wc374_spanCodes_le_of_gens [278, 160, 84, 12, 1]
    (actionW (codeMat 273) (codeMat 167) step109wc374s0SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 238 ∈ step109wc374s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 238 (by decide)
    have hact : actionA (codeMat 273) (codeMat 167) (codeMat 238) = codeMat 278 := by
      unfold actionA
      rw [step109wc374s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 238 * (codeMat 167 : Mat3).transpose = codeMat 278
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 344 ∈ step109wc374s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 344 (by decide)
    have hact : actionA (codeMat 273) (codeMat 167) (codeMat 344) = codeMat 160 := by
      unfold actionA
      rw [step109wc374s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 344 * (codeMat 167 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 107 ∈ step109wc374s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 107 (by decide)
    have hact : actionA (codeMat 273) (codeMat 167) (codeMat 107) = codeMat 84 := by
      unfold actionA
      rw [step109wc374s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 107 * (codeMat 167 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 11 ∈ step109wc374s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 273) (codeMat 167) (codeMat 11) = codeMat 12 := by
      unfold actionA
      rw [step109wc374s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 11 * (codeMat 167 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ step109wc374s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 167) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc374s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 167 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact

theorem step109wc374s0Dispatch :
    QuotientRankAtLeast (o374SourceU_wc ⟨0, by omega⟩) 16 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 167 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 167) step109wc374s0SrcT) 16 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 167) hP hQ step109wc374s0SrcT 16
      step109wc374s0SrcT_lb
  exact quotientRankAtLeast_mono step109wc374s0_contain hAct


private theorem step109wc374s1_QtInv :
    (codeMat 417 : Mat3).transpose⁻¹ = (codeMat 177 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 417 : Mat3).transpose * (codeMat 177 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc374s1_contain :
    (o374SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 473) (codeMat 417) o214W_wc := by
  change spanCodes [276, 160, 84, 14, 1] ≤ actionW (codeMat 473) (codeMat 417) o214W_wc
  apply step109wc374_spanCodes_le_of_gens [276, 160, 84, 14, 1]
    (actionW (codeMat 473) (codeMat 417) o214W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 402 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 402 (by decide)
    have hact : actionA (codeMat 473) (codeMat 417) (codeMat 402) = codeMat 276 := by
      unfold actionA
      rw [step109wc374s1_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 402 * (codeMat 177 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 278 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 278 (by decide)
    have hact : actionA (codeMat 473) (codeMat 417) (codeMat 278) = codeMat 160 := by
      unfold actionA
      rw [step109wc374s1_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 278 * (codeMat 177 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 106 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 106 (by decide)
    have hact : actionA (codeMat 473) (codeMat 417) (codeMat 106) = codeMat 84 := by
      unfold actionA
      rw [step109wc374s1_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 106 * (codeMat 177 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 11 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 473) (codeMat 417) (codeMat 11) = codeMat 14 := by
      unfold actionA
      rw [step109wc374s1_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 11 * (codeMat 177 : Mat3).transpose = codeMat 14
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 473) (codeMat 417) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc374s1_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 1 * (codeMat 177 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact

theorem step109wc374s1Dispatch :
    QuotientRankAtLeast (o374SourceU_wc ⟨1, by omega⟩) 16 := by
  have hP : Invertible (codeMat 473 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 473) (codeMat 417) o214W_wc) 16 :=
    @quotientRankAtLeast_action (codeMat 473) (codeMat 417) hP hQ o214W_wc 16
      step109_orbit214_lb16_wc
  exact quotientRankAtLeast_mono step109wc374s1_contain hAct

private def step109wc374s2SrcT : Submodule F2 Mat3 := spanCodes [306, 132, 96, 10, 1]

private theorem step109wc374s2SrcT_lb : QuotientRankAtLeast step109wc374s2SrcT 16 := by
  have ht := quotientRankAtLeast_transpose step109_orbit214_lb16_wc
  have hle : step109wc374s2SrcT ≤ transposeW o214W_wc := by
    unfold step109wc374s2SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4
    · subst h0
      show codeMat 306 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 408, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 408 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 132 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 96, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 96 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 96 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 132, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 132 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 10 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 10, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 10 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 1 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc374s2_QtInv :
    (codeMat 405 : Mat3).transpose⁻¹ = (codeMat 407 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 405 : Mat3).transpose * (codeMat 407 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc374s2_contain :
    (o374SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 417) (codeMat 405) step109wc374s2SrcT := by
  change spanCodes [264, 160, 70, 18, 1] ≤ actionW (codeMat 417) (codeMat 405) step109wc374s2SrcT
  apply step109wc374_spanCodes_le_of_gens [264, 160, 70, 18, 1]
    (actionW (codeMat 417) (codeMat 405) step109wc374s2SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 96 ∈ step109wc374s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 96 (by decide)
    have hact : actionA (codeMat 417) (codeMat 405) (codeMat 96) = codeMat 264 := by
      unfold actionA
      rw [step109wc374s2_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 96 * (codeMat 407 : Mat3).transpose = codeMat 264
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 344 ∈ step109wc374s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 344 (by decide)
    have hact : actionA (codeMat 417) (codeMat 405) (codeMat 344) = codeMat 160 := by
      unfold actionA
      rw [step109wc374s2_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 344 * (codeMat 407 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 11 ∈ step109wc374s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 417) (codeMat 405) (codeMat 11) = codeMat 70 := by
      unfold actionA
      rw [step109wc374s2_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 11 * (codeMat 407 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 438 ∈ step109wc374s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 438 (by decide)
    have hact : actionA (codeMat 417) (codeMat 405) (codeMat 438) = codeMat 18 := by
      unfold actionA
      rw [step109wc374s2_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 438 * (codeMat 407 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ step109wc374s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 417) (codeMat 405) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc374s2_QtInv]
      show (codeMat 417 : Mat3).transpose * codeMat 1 * (codeMat 407 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact

theorem step109wc374s2Dispatch :
    QuotientRankAtLeast (o374SourceU_wc ⟨2, by omega⟩) 16 := by
  have hP : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 405 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 417) (codeMat 405) step109wc374s2SrcT) 16 :=
    @quotientRankAtLeast_action (codeMat 417) (codeMat 405) hP hQ step109wc374s2SrcT 16
      step109wc374s2SrcT_lb
  exact quotientRankAtLeast_mono step109wc374s2_contain hAct


private theorem step109wc374s3_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc374s3_contain :
    (o374SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 233) (codeMat 273) o214W_wc := by
  change spanCodes [268, 160, 66, 22, 1] ≤ actionW (codeMat 233) (codeMat 273) o214W_wc
  apply step109wc374_spanCodes_le_of_gens [268, 160, 66, 22, 1]
    (actionW (codeMat 233) (codeMat 273) o214W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 97 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 97 (by decide)
    have hact : actionA (codeMat 233) (codeMat 273) (codeMat 97) = codeMat 268 := by
      unfold actionA
      rw [step109wc374s3_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 97 * (codeMat 273 : Mat3).transpose = codeMat 268
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 278 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 278 (by decide)
    have hact : actionA (codeMat 233) (codeMat 273) (codeMat 278) = codeMat 160 := by
      unfold actionA
      rw [step109wc374s3_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 278 * (codeMat 273 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 11 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 233) (codeMat 273) (codeMat 11) = codeMat 66 := by
      unfold actionA
      rw [step109wc374s3_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 11 * (codeMat 273 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 132 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 132 (by decide)
    have hact : actionA (codeMat 233) (codeMat 273) (codeMat 132) = codeMat 22 := by
      unfold actionA
      rw [step109wc374s3_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 132 * (codeMat 273 : Mat3).transpose = codeMat 22
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc374s3_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact

theorem step109wc374s3Dispatch :
    QuotientRankAtLeast (o374SourceU_wc ⟨3, by omega⟩) 16 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 273) o214W_wc) 16 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 273) hP hQ o214W_wc 16
      step109_orbit214_lb16_wc
  exact quotientRankAtLeast_mono step109wc374s3_contain hAct


private theorem step109wc374s4_QtInv :
    (codeMat 177 : Mat3).transpose⁻¹ = (codeMat 417 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 177 : Mat3).transpose * (codeMat 417 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc374s4_contain :
    (o374SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 377) (codeMat 177) o214W_wc := by
  change spanCodes [258, 160, 76, 24, 1] ≤ actionW (codeMat 377) (codeMat 177) o214W_wc
  apply step109wc374_spanCodes_le_of_gens [258, 160, 76, 24, 1]
    (actionW (codeMat 377) (codeMat 177) o214W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 132 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 132 (by decide)
    have hact : actionA (codeMat 377) (codeMat 177) (codeMat 132) = codeMat 258 := by
      unfold actionA
      rw [step109wc374s4_QtInv]
      show (codeMat 377 : Mat3).transpose * codeMat 132 * (codeMat 417 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 278 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 278 (by decide)
    have hact : actionA (codeMat 377) (codeMat 177) (codeMat 278) = codeMat 160 := by
      unfold actionA
      rw [step109wc374s4_QtInv]
      show (codeMat 377 : Mat3).transpose * codeMat 278 * (codeMat 417 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 11 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 377) (codeMat 177) (codeMat 11) = codeMat 76 := by
      unfold actionA
      rw [step109wc374s4_QtInv]
      show (codeMat 377 : Mat3).transpose * codeMat 11 * (codeMat 417 : Mat3).transpose = codeMat 76
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 504 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 504 (by decide)
    have hact : actionA (codeMat 377) (codeMat 177) (codeMat 504) = codeMat 24 := by
      unfold actionA
      rw [step109wc374s4_QtInv]
      show (codeMat 377 : Mat3).transpose * codeMat 504 * (codeMat 417 : Mat3).transpose = codeMat 24
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 377) (codeMat 177) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc374s4_QtInv]
      show (codeMat 377 : Mat3).transpose * codeMat 1 * (codeMat 417 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact

theorem step109wc374s4Dispatch :
    QuotientRankAtLeast (o374SourceU_wc ⟨4, by omega⟩) 16 := by
  have hP : Invertible (codeMat 377 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 377) (codeMat 177) o214W_wc) 16 :=
    @quotientRankAtLeast_action (codeMat 377) (codeMat 177) hP hQ o214W_wc 16
      step109_orbit214_lb16_wc
  exact quotientRankAtLeast_mono step109wc374s4_contain hAct

private def step109wc374s5SrcT : Submodule F2 Mat3 := spanCodes [306, 132, 96, 10, 1]

private theorem step109wc374s5SrcT_lb : QuotientRankAtLeast step109wc374s5SrcT 16 := by
  have ht := quotientRankAtLeast_transpose step109_orbit214_lb16_wc
  have hle : step109wc374s5SrcT ≤ transposeW o214W_wc := by
    unfold step109wc374s5SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4
    · subst h0
      show codeMat 306 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 408, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 408 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 132 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 96, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 96 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 96 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 132, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 132 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 10 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 10, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 10 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 1 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc374s5_QtInv :
    (codeMat 307 : Mat3).transpose⁻¹ = (codeMat 311 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 307 : Mat3).transpose * (codeMat 311 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc374s5_contain :
    (o374SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 177) (codeMat 307) step109wc374s5SrcT := by
  change spanCodes [260, 160, 74, 30, 1] ≤ actionW (codeMat 177) (codeMat 307) step109wc374s5SrcT
  apply step109wc374_spanCodes_le_of_gens [260, 160, 74, 30, 1]
    (actionW (codeMat 177) (codeMat 307) step109wc374s5SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 438 ∈ step109wc374s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 438 (by decide)
    have hact : actionA (codeMat 177) (codeMat 307) (codeMat 438) = codeMat 260 := by
      unfold actionA
      rw [step109wc374s5_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 438 * (codeMat 311 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 344 ∈ step109wc374s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 344 (by decide)
    have hact : actionA (codeMat 177) (codeMat 307) (codeMat 344) = codeMat 160 := by
      unfold actionA
      rw [step109wc374s5_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 344 * (codeMat 311 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 11 ∈ step109wc374s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 177) (codeMat 307) (codeMat 11) = codeMat 74 := by
      unfold actionA
      rw [step109wc374s5_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 11 * (codeMat 311 : Mat3).transpose = codeMat 74
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 133 ∈ step109wc374s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 133 (by decide)
    have hact : actionA (codeMat 177) (codeMat 307) (codeMat 133) = codeMat 30 := by
      unfold actionA
      rw [step109wc374s5_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 133 * (codeMat 311 : Mat3).transpose = codeMat 30
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ step109wc374s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 307) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc374s5_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * (codeMat 311 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact

theorem step109wc374s5Dispatch :
    QuotientRankAtLeast (o374SourceU_wc ⟨5, by omega⟩) 16 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 307 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 307) step109wc374s5SrcT) 16 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 307) hP hQ step109wc374s5SrcT 16
      step109wc374s5SrcT_lb
  exact quotientRankAtLeast_mono step109wc374s5_contain hAct


private theorem step109wc374s6_QtInv :
    (codeMat 207 : Mat3).transpose⁻¹ = (codeMat 370 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 207 : Mat3).transpose * (codeMat 370 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc374s6_contain :
    (o374SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 355) (codeMat 207) o214W_wc := by
  change spanCodes [282, 132, 84, 36, 1] ≤ actionW (codeMat 355) (codeMat 207) o214W_wc
  apply step109wc374_spanCodes_le_of_gens [282, 132, 84, 36, 1]
    (actionW (codeMat 355) (codeMat 207) o214W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 498 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 498 (by decide)
    have hact : actionA (codeMat 355) (codeMat 207) (codeMat 498) = codeMat 282 := by
      unfold actionA
      rw [step109wc374s6_QtInv]
      show (codeMat 355 : Mat3).transpose * codeMat 498 * (codeMat 370 : Mat3).transpose = codeMat 282
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 96 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 96 (by decide)
    have hact : actionA (codeMat 355) (codeMat 207) (codeMat 96) = codeMat 132 := by
      unfold actionA
      rw [step109wc374s6_QtInv]
      show (codeMat 355 : Mat3).transpose * codeMat 96 * (codeMat 370 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 285 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 285 (by decide)
    have hact : actionA (codeMat 355) (codeMat 207) (codeMat 285) = codeMat 84 := by
      unfold actionA
      rw [step109wc374s6_QtInv]
      show (codeMat 355 : Mat3).transpose * codeMat 285 * (codeMat 370 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 355) (codeMat 207) (codeMat 1) = codeMat 36 := by
      unfold actionA
      rw [step109wc374s6_QtInv]
      show (codeMat 355 : Mat3).transpose * codeMat 1 * (codeMat 370 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 504 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 504 (by decide)
    have hact : actionA (codeMat 355) (codeMat 207) (codeMat 504) = codeMat 1 := by
      unfold actionA
      rw [step109wc374s6_QtInv]
      show (codeMat 355 : Mat3).transpose * codeMat 504 * (codeMat 370 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact

theorem step109wc374s6Dispatch :
    QuotientRankAtLeast (o374SourceU_wc ⟨6, by omega⟩) 16 := by
  have hP : Invertible (codeMat 355 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 207 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 355) (codeMat 207) o214W_wc) 16 :=
    @quotientRankAtLeast_action (codeMat 355) (codeMat 207) hP hQ o214W_wc 16
      step109_orbit214_lb16_wc
  exact quotientRankAtLeast_mono step109wc374s6_contain hAct

private def step109wc374s7SrcT : Submodule F2 Mat3 := spanCodes [306, 132, 96, 10, 1]

private theorem step109wc374s7SrcT_lb : QuotientRankAtLeast step109wc374s7SrcT 16 := by
  have ht := quotientRankAtLeast_transpose step109_orbit214_lb16_wc
  have hle : step109wc374s7SrcT ≤ transposeW o214W_wc := by
    unfold step109wc374s7SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4
    · subst h0
      show codeMat 306 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 408, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 408 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 132 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 96, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 96 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 96 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 132, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 132 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 10 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 10, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 10 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 1 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc374s7_QtInv :
    (codeMat 494 : Mat3).transpose⁻¹ = (codeMat 501 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 494 : Mat3).transpose * (codeMat 501 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc374s7_contain :
    (o374SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 174) (codeMat 494) step109wc374s7SrcT := by
  change spanCodes [282, 134, 84, 38, 1] ≤ actionW (codeMat 174) (codeMat 494) step109wc374s7SrcT
  apply step109wc374_spanCodes_le_of_gens [282, 134, 84, 38, 1]
    (actionW (codeMat 174) (codeMat 494) step109wc374s7SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 106 ∈ step109wc374s7SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 106 (by decide)
    have hact : actionA (codeMat 174) (codeMat 494) (codeMat 106) = codeMat 282 := by
      unfold actionA
      rw [step109wc374s7_QtInv]
      show (codeMat 174 : Mat3).transpose * codeMat 106 * (codeMat 501 : Mat3).transpose = codeMat 282
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 471 ∈ step109wc374s7SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 471 (by decide)
    have hact : actionA (codeMat 174) (codeMat 494) (codeMat 471) = codeMat 134 := by
      unfold actionA
      rw [step109wc374s7_QtInv]
      show (codeMat 174 : Mat3).transpose * codeMat 471 * (codeMat 501 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 313 ∈ step109wc374s7SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 313 (by decide)
    have hact : actionA (codeMat 174) (codeMat 494) (codeMat 313) = codeMat 84 := by
      unfold actionA
      rw [step109wc374s7_QtInv]
      show (codeMat 174 : Mat3).transpose * codeMat 313 * (codeMat 501 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 338 ∈ step109wc374s7SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 338 (by decide)
    have hact : actionA (codeMat 174) (codeMat 494) (codeMat 338) = codeMat 38 := by
      unfold actionA
      rw [step109wc374s7_QtInv]
      show (codeMat 174 : Mat3).transpose * codeMat 338 * (codeMat 501 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 438 ∈ step109wc374s7SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 438 (by decide)
    have hact : actionA (codeMat 174) (codeMat 494) (codeMat 438) = codeMat 1 := by
      unfold actionA
      rw [step109wc374s7_QtInv]
      show (codeMat 174 : Mat3).transpose * codeMat 438 * (codeMat 501 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact

theorem step109wc374s7Dispatch :
    QuotientRankAtLeast (o374SourceU_wc ⟨7, by omega⟩) 16 := by
  have hP : Invertible (codeMat 174 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 494 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 174) (codeMat 494) step109wc374s7SrcT) 16 :=
    @quotientRankAtLeast_action (codeMat 174) (codeMat 494) hP hQ step109wc374s7SrcT 16
      step109wc374s7SrcT_lb
  exact quotientRankAtLeast_mono step109wc374s7_contain hAct


private theorem step109wc374s8_QtInv :
    (codeMat 421 : Mat3).transpose⁻¹ = (codeMat 179 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 421 : Mat3).transpose * (codeMat 179 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc374s8_contain :
    (o374SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 233) (codeMat 421) o237W := by
  change spanCodes [282, 138, 84, 42, 1] ≤ actionW (codeMat 233) (codeMat 421) o237W
  apply step109wc374_spanCodes_le_of_gens [282, 138, 84, 42, 1]
    (actionW (codeMat 233) (codeMat 421) o237W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 382 ∈ o237W :=
      spanContainsCodeCore_implies_mem_spanCodes [266, 136, 96, 20, 1] 382 (by decide)
    have hact : actionA (codeMat 233) (codeMat 421) (codeMat 382) = codeMat 282 := by
      unfold actionA
      rw [step109wc374s8_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 382 * (codeMat 179 : Mat3).transpose = codeMat 282
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 97 ∈ o237W :=
      spanContainsCodeCore_implies_mem_spanCodes [266, 136, 96, 20, 1] 97 (by decide)
    have hact : actionA (codeMat 233) (codeMat 421) (codeMat 97) = codeMat 138 := by
      unfold actionA
      rw [step109wc374s8_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 97 * (codeMat 179 : Mat3).transpose = codeMat 138
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 266 ∈ o237W :=
      spanContainsCodeCore_implies_mem_spanCodes [266, 136, 96, 20, 1] 266 (by decide)
    have hact : actionA (codeMat 233) (codeMat 421) (codeMat 266) = codeMat 84 := by
      unfold actionA
      rw [step109wc374s8_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 266 * (codeMat 179 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 386 ∈ o237W :=
      spanContainsCodeCore_implies_mem_spanCodes [266, 136, 96, 20, 1] 386 (by decide)
    have hact : actionA (codeMat 233) (codeMat 421) (codeMat 386) = codeMat 42 := by
      unfold actionA
      rw [step109wc374s8_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 386 * (codeMat 179 : Mat3).transpose = codeMat 42
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o237W :=
      spanContainsCodeCore_implies_mem_spanCodes [266, 136, 96, 20, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 421) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc374s8_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * (codeMat 179 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact

theorem step109wc374s8Dispatch :
    QuotientRankAtLeast (o374SourceU_wc ⟨8, by omega⟩) 16 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 421 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 421) o237W) 16 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 421) hP hQ o237W 16
      step99_orbit237_lb16_unconditional
  exact quotientRankAtLeast_mono step109wc374s8_contain hAct


private theorem step109wc374s9_QtInv :
    (codeMat 331 : Mat3).transpose⁻¹ = (codeMat 410 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 331 : Mat3).transpose * (codeMat 410 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc374s9_contain :
    (o374SourceU_wc ⟨9, by omega⟩) ≤ actionW (codeMat 215) (codeMat 331) o214W_wc := by
  change spanCodes [282, 146, 84, 50, 1] ≤ actionW (codeMat 215) (codeMat 331) o214W_wc
  apply step109wc374_spanCodes_le_of_gens [282, 146, 84, 50, 1]
    (actionW (codeMat 215) (codeMat 331) o214W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 380 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 380 (by decide)
    have hact : actionA (codeMat 215) (codeMat 331) (codeMat 380) = codeMat 282 := by
      unfold actionA
      rw [step109wc374s9_QtInv]
      show (codeMat 215 : Mat3).transpose * codeMat 380 * (codeMat 410 : Mat3).transpose = codeMat 282
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 215) (codeMat 331) (codeMat 1) = codeMat 146 := by
      unfold actionA
      rw [step109wc374s9_QtInv]
      show (codeMat 215 : Mat3).transpose * codeMat 1 * (codeMat 410 : Mat3).transpose = codeMat 146
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 239 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 239 (by decide)
    have hact : actionA (codeMat 215) (codeMat 331) (codeMat 239) = codeMat 84 := by
      unfold actionA
      rw [step109wc374s9_QtInv]
      show (codeMat 215 : Mat3).transpose * codeMat 239 * (codeMat 410 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 96 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 96 (by decide)
    have hact : actionA (codeMat 215) (codeMat 331) (codeMat 96) = codeMat 50 := by
      unfold actionA
      rw [step109wc374s9_QtInv]
      show (codeMat 215 : Mat3).transpose * codeMat 96 * (codeMat 410 : Mat3).transpose = codeMat 50
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 504 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 504 (by decide)
    have hact : actionA (codeMat 215) (codeMat 331) (codeMat 504) = codeMat 1 := by
      unfold actionA
      rw [step109wc374s9_QtInv]
      show (codeMat 215 : Mat3).transpose * codeMat 504 * (codeMat 410 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact

theorem step109wc374s9Dispatch :
    QuotientRankAtLeast (o374SourceU_wc ⟨9, by omega⟩) 16 := by
  have hP : Invertible (codeMat 215 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 331 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 215) (codeMat 331) o214W_wc) 16 :=
    @quotientRankAtLeast_action (codeMat 215) (codeMat 331) hP hQ o214W_wc 16
      step109_orbit214_lb16_wc
  exact quotientRankAtLeast_mono step109wc374s9_contain hAct

private def step109wc374s10SrcT : Submodule F2 Mat3 := spanCodes [306, 132, 96, 10, 1]

private theorem step109wc374s10SrcT_lb : QuotientRankAtLeast step109wc374s10SrcT 16 := by
  have ht := quotientRankAtLeast_transpose step109_orbit214_lb16_wc
  have hle : step109wc374s10SrcT ≤ transposeW o214W_wc := by
    unfold step109wc374s10SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4
    · subst h0
      show codeMat 306 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 408, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 408 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 132 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 96, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 96 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 96 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 132, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 132 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 10 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 10, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 10 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 1 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc374s10_QtInv :
    (codeMat 250 : Mat3).transpose⁻¹ = (codeMat 397 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 250 : Mat3).transpose * (codeMat 397 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc374s10_contain :
    (o374SourceU_wc ⟨10, by omega⟩) ≤ actionW (codeMat 412) (codeMat 250) step109wc374s10SrcT := by
  change spanCodes [282, 148, 84, 52, 1] ≤ actionW (codeMat 412) (codeMat 250) step109wc374s10SrcT
  apply step109wc374_spanCodes_le_of_gens [282, 148, 84, 52, 1]
    (actionW (codeMat 412) (codeMat 250) step109wc374s10SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 444 ∈ step109wc374s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 444 (by decide)
    have hact : actionA (codeMat 412) (codeMat 250) (codeMat 444) = codeMat 282 := by
      unfold actionA
      rw [step109wc374s10_QtInv]
      show (codeMat 412 : Mat3).transpose * codeMat 444 * (codeMat 397 : Mat3).transpose = codeMat 282
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 338 ∈ step109wc374s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 338 (by decide)
    have hact : actionA (codeMat 412) (codeMat 250) (codeMat 338) = codeMat 148 := by
      unfold actionA
      rw [step109wc374s10_QtInv]
      show (codeMat 412 : Mat3).transpose * codeMat 338 * (codeMat 397 : Mat3).transpose = codeMat 148
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 339 ∈ step109wc374s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 339 (by decide)
    have hact : actionA (codeMat 412) (codeMat 250) (codeMat 339) = codeMat 84 := by
      unfold actionA
      rw [step109wc374s10_QtInv]
      show (codeMat 412 : Mat3).transpose * codeMat 339 * (codeMat 397 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 471 ∈ step109wc374s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 471 (by decide)
    have hact : actionA (codeMat 412) (codeMat 250) (codeMat 471) = codeMat 52 := by
      unfold actionA
      rw [step109wc374s10_QtInv]
      show (codeMat 412 : Mat3).transpose * codeMat 471 * (codeMat 397 : Mat3).transpose = codeMat 52
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 438 ∈ step109wc374s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 438 (by decide)
    have hact : actionA (codeMat 412) (codeMat 250) (codeMat 438) = codeMat 1 := by
      unfold actionA
      rw [step109wc374s10_QtInv]
      show (codeMat 412 : Mat3).transpose * codeMat 438 * (codeMat 397 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact

theorem step109wc374s10Dispatch :
    QuotientRankAtLeast (o374SourceU_wc ⟨10, by omega⟩) 16 := by
  have hP : Invertible (codeMat 412 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 250 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 412) (codeMat 250) step109wc374s10SrcT) 16 :=
    @quotientRankAtLeast_action (codeMat 412) (codeMat 250) hP hQ step109wc374s10SrcT 16
      step109wc374s10SrcT_lb
  exact quotientRankAtLeast_mono step109wc374s10_contain hAct

private def step109wc374s11SrcT : Submodule F2 Mat3 := spanCodes [306, 132, 96, 10, 1]

private theorem step109wc374s11SrcT_lb : QuotientRankAtLeast step109wc374s11SrcT 16 := by
  have ht := quotientRankAtLeast_transpose step109_orbit214_lb16_wc
  have hle : step109wc374s11SrcT ≤ transposeW o214W_wc := by
    unfold step109wc374s11SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4
    · subst h0
      show codeMat 306 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 408, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 408 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 132 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 96, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 96 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 96 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 132, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 132 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 10 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 10, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 10 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 1 ∈ Submodule.map transposeLinearMap o214W_wc
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc374s11_QtInv :
    (codeMat 348 : Mat3).transpose⁻¹ = (codeMat 125 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 348 : Mat3).transpose * (codeMat 125 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc374s11_contain :
    (o374SourceU_wc ⟨11, by omega⟩) ≤ actionW (codeMat 314) (codeMat 348) step109wc374s11SrcT := by
  change spanCodes [282, 152, 84, 56, 1] ≤ actionW (codeMat 314) (codeMat 348) step109wc374s11SrcT
  apply step109wc374_spanCodes_le_of_gens [282, 152, 84, 56, 1]
    (actionW (codeMat 314) (codeMat 348) step109wc374s11SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 470 ∈ step109wc374s11SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 470 (by decide)
    have hact : actionA (codeMat 314) (codeMat 348) (codeMat 470) = codeMat 282 := by
      unfold actionA
      rw [step109wc374s11_QtInv]
      show (codeMat 314 : Mat3).transpose * codeMat 470 * (codeMat 125 : Mat3).transpose = codeMat 282
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 132 ∈ step109wc374s11SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 132 (by decide)
    have hact : actionA (codeMat 314) (codeMat 348) (codeMat 132) = codeMat 152 := by
      unfold actionA
      rw [step109wc374s11_QtInv]
      show (codeMat 314 : Mat3).transpose * codeMat 132 * (codeMat 125 : Mat3).transpose = codeMat 152
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 239 ∈ step109wc374s11SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 239 (by decide)
    have hact : actionA (codeMat 314) (codeMat 348) (codeMat 239) = codeMat 84 := by
      unfold actionA
      rw [step109wc374s11_QtInv]
      show (codeMat 314 : Mat3).transpose * codeMat 239 * (codeMat 125 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ step109wc374s11SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 314) (codeMat 348) (codeMat 1) = codeMat 56 := by
      unfold actionA
      rw [step109wc374s11_QtInv]
      show (codeMat 314 : Mat3).transpose * codeMat 1 * (codeMat 125 : Mat3).transpose = codeMat 56
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 438 ∈ step109wc374s11SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 438 (by decide)
    have hact : actionA (codeMat 314) (codeMat 348) (codeMat 438) = codeMat 1 := by
      unfold actionA
      rw [step109wc374s11_QtInv]
      show (codeMat 314 : Mat3).transpose * codeMat 438 * (codeMat 125 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact

theorem step109wc374s11Dispatch :
    QuotientRankAtLeast (o374SourceU_wc ⟨11, by omega⟩) 16 := by
  have hP : Invertible (codeMat 314 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 348 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 314) (codeMat 348) step109wc374s11SrcT) 16 :=
    @quotientRankAtLeast_action (codeMat 314) (codeMat 348) hP hQ step109wc374s11SrcT 16
      step109wc374s11SrcT_lb
  exact quotientRankAtLeast_mono step109wc374s11_contain hAct


private theorem step109wc374s12_QtInv :
    (codeMat 461 : Mat3).transpose⁻¹ = (codeMat 234 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 461 : Mat3).transpose * (codeMat 234 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc374s12_contain :
    (o374SourceU_wc ⟨12, by omega⟩) ≤ actionW (codeMat 501) (codeMat 461) o214W_wc := by
  change spanCodes [282, 156, 84, 60, 1] ≤ actionW (codeMat 501) (codeMat 461) o214W_wc
  apply step109wc374_spanCodes_le_of_gens [282, 156, 84, 60, 1]
    (actionW (codeMat 501) (codeMat 461) o214W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 142 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 142 (by decide)
    have hact : actionA (codeMat 501) (codeMat 461) (codeMat 142) = codeMat 282 := by
      unfold actionA
      rw [step109wc374s12_QtInv]
      show (codeMat 501 : Mat3).transpose * codeMat 142 * (codeMat 234 : Mat3).transpose = codeMat 282
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 143 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 143 (by decide)
    have hact : actionA (codeMat 501) (codeMat 461) (codeMat 143) = codeMat 156 := by
      unfold actionA
      rw [step109wc374s12_QtInv]
      show (codeMat 501 : Mat3).transpose * codeMat 143 * (codeMat 234 : Mat3).transpose = codeMat 156
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 403 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 403 (by decide)
    have hact : actionA (codeMat 501) (codeMat 461) (codeMat 403) = codeMat 84 := by
      unfold actionA
      rw [step109wc374s12_QtInv]
      show (codeMat 501 : Mat3).transpose * codeMat 403 * (codeMat 234 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 238 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 238 (by decide)
    have hact : actionA (codeMat 501) (codeMat 461) (codeMat 238) = codeMat 60 := by
      unfold actionA
      rw [step109wc374s12_QtInv]
      show (codeMat 501 : Mat3).transpose * codeMat 238 * (codeMat 234 : Mat3).transpose = codeMat 60
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 504 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 504 (by decide)
    have hact : actionA (codeMat 501) (codeMat 461) (codeMat 504) = codeMat 1 := by
      unfold actionA
      rw [step109wc374s12_QtInv]
      show (codeMat 501 : Mat3).transpose * codeMat 504 * (codeMat 234 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact

theorem step109wc374s12Dispatch :
    QuotientRankAtLeast (o374SourceU_wc ⟨12, by omega⟩) 16 := by
  have hP : Invertible (codeMat 501 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 461 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 501) (codeMat 461) o214W_wc) 16 :=
    @quotientRankAtLeast_action (codeMat 501) (codeMat 461) hP hQ o214W_wc 16
      step109_orbit214_lb16_wc
  exact quotientRankAtLeast_mono step109wc374s12_contain hAct


private theorem step109wc374s13_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc374s13_contain :
    (o374SourceU_wc ⟨13, by omega⟩) ≤ actionW (codeMat 84) (codeMat 84) o63W_wc := by
  change spanCodes [256, 160, 68, 16, 10, 1] ≤ actionW (codeMat 84) (codeMat 84) o63W_wc
  apply step109wc374_spanCodes_le_of_gens [256, 160, 68, 16, 10, 1]
    (actionW (codeMat 84) (codeMat 84) o63W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 1 ∈ o63W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc374s13_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 10 ∈ o63W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 10) = codeMat 160 := by
      unfold actionA
      rw [step109wc374s13_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 10 * (codeMat 84 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ o63W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 16, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step109wc374s13_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 68 * (codeMat 84 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ o63W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 16) = codeMat 16 := by
      unfold actionA
      rw [step109wc374s13_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 16 * (codeMat 84 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ o63W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 16, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc374s13_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 160 * (codeMat 84 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ o63W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 16, 10, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc374s13_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact

theorem step109wc374s13Dispatch :
    QuotientRankAtLeast (o374SourceU_wc ⟨13, by omega⟩) 14 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 84) o63W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 84) hP hQ o63W_wc 14
      step109_orbit63_lb14_wc
  exact quotientRankAtLeast_mono step109wc374s13_contain hAct


private theorem step109wc374s14_QtInv :
    (codeMat 165 : Mat3).transpose⁻¹ = (codeMat 163 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 165 : Mat3).transpose * (codeMat 163 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc374s14_contain :
    (o374SourceU_wc ⟨14, by omega⟩) ≤ actionW (codeMat 266) (codeMat 165) orbit10W := by
  change spanCodes [274, 128, 80, 32, 8, 4, 1] ≤ actionW (codeMat 266) (codeMat 165) orbit10W
  apply step109wc374_spanCodes_le_of_gens [274, 128, 80, 32, 8, 4, 1]
    (actionW (codeMat 266) (codeMat 165) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 228 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 228 (by decide)
    have hact : actionA (codeMat 266) (codeMat 165) (codeMat 228) = codeMat 274 := by
      unfold actionA
      rw [step109wc374s14_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 228 * (codeMat 163 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 266) (codeMat 165) (codeMat 256) = codeMat 128 := by
      unfold actionA
      rw [step109wc374s14_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 256 * (codeMat 163 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 266) (codeMat 165) (codeMat 68) = codeMat 80 := by
      unfold actionA
      rw [step109wc374s14_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 68 * (codeMat 163 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 3 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 266) (codeMat 165) (codeMat 3) = codeMat 32 := by
      unfold actionA
      rw [step109wc374s14_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 3 * (codeMat 163 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 165) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step109wc374s14_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 163 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 266) (codeMat 165) (codeMat 24) = codeMat 4 := by
      unfold actionA
      rw [step109wc374s14_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 24 * (codeMat 163 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 165) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc374s14_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 163 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact

theorem step109wc374s14Dispatch :
    QuotientRankAtLeast (o374SourceU_wc ⟨14, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 165 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 165) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 165) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc374s14_contain hAct


private theorem step109wc374s15_QtInv :
    (codeMat 311 : Mat3).transpose⁻¹ = (codeMat 307 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 311 : Mat3).transpose * (codeMat 307 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc374s15_contain :
    (o374SourceU_wc ⟨15, by omega⟩) ≤ actionW (codeMat 142) (codeMat 311) orbit10W := by
  change spanCodes [260, 140, 72, 44, 28, 2, 1] ≤ actionW (codeMat 142) (codeMat 311) orbit10W
  apply step109wc374_spanCodes_le_of_gens [260, 140, 72, 44, 28, 2, 1]
    (actionW (codeMat 142) (codeMat 311) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 511 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 511 (by decide)
    have hact : actionA (codeMat 142) (codeMat 311) (codeMat 511) = codeMat 260 := by
      unfold actionA
      rw [step109wc374s15_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 511 * (codeMat 307 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 187 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 187 (by decide)
    have hact : actionA (codeMat 142) (codeMat 311) (codeMat 187) = codeMat 140 := by
      unfold actionA
      rw [step109wc374s15_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 187 * (codeMat 307 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 142) (codeMat 311) (codeMat 1) = codeMat 72 := by
      unfold actionA
      rw [step109wc374s15_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 1 * (codeMat 307 : Mat3).transpose = codeMat 72
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 440 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 440 (by decide)
    have hact : actionA (codeMat 142) (codeMat 311) (codeMat 440) = codeMat 44 := by
      unfold actionA
      rw [step109wc374s15_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 440 * (codeMat 307 : Mat3).transpose = codeMat 44
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 184 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 184 (by decide)
    have hact : actionA (codeMat 142) (codeMat 311) (codeMat 184) = codeMat 28 := by
      unfold actionA
      rw [step109wc374s15_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 184 * (codeMat 307 : Mat3).transpose = codeMat 28
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 142) (codeMat 311) (codeMat 24) = codeMat 2 := by
      unfold actionA
      rw [step109wc374s15_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 24 * (codeMat 307 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 142) (codeMat 311) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc374s15_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 8 * (codeMat 307 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact

theorem step109wc374s15Dispatch :
    QuotientRankAtLeast (o374SourceU_wc ⟨15, by omega⟩) 12 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 311 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 311) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 311) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc374s15_contain hAct


private theorem step109wc374s16_QtInv :
    (codeMat 281 : Mat3).transpose⁻¹ = (codeMat 281 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 281 : Mat3).transpose * (codeMat 281 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc374s16_contain :
    (o374SourceU_wc ⟨16, by omega⟩) ≤ actionW (codeMat 140) (codeMat 281) orbit10W := by
  change spanCodes [268, 128, 64, 32, 20, 2, 1] ≤ actionW (codeMat 140) (codeMat 281) orbit10W
  apply step109wc374_spanCodes_le_of_gens [268, 128, 64, 32, 20, 2, 1]
    (actionW (codeMat 140) (codeMat 281) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 228 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 228 (by decide)
    have hact : actionA (codeMat 140) (codeMat 281) (codeMat 228) = codeMat 268 := by
      unfold actionA
      rw [step109wc374s16_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 228 * (codeMat 281 : Mat3).transpose = codeMat 268
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 281) (codeMat 2) = codeMat 128 := by
      unfold actionA
      rw [step109wc374s16_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 281 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 3 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 140) (codeMat 281) (codeMat 3) = codeMat 64 := by
      unfold actionA
      rw [step109wc374s16_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 3 * (codeMat 281 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 140) (codeMat 281) (codeMat 256) = codeMat 32 := by
      unfold actionA
      rw [step109wc374s16_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 256 * (codeMat 281 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 140) (codeMat 281) (codeMat 160) = codeMat 20 := by
      unfold actionA
      rw [step109wc374s16_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 160 * (codeMat 281 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 140) (codeMat 281) (codeMat 16) = codeMat 2 := by
      unfold actionA
      rw [step109wc374s16_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 16 * (codeMat 281 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 140) (codeMat 281) (codeMat 24) = codeMat 1 := by
      unfold actionA
      rw [step109wc374s16_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 24 * (codeMat 281 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact

theorem step109wc374s16Dispatch :
    QuotientRankAtLeast (o374SourceU_wc ⟨16, by omega⟩) 12 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 281) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 281) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc374s16_contain hAct


private theorem step109wc374s17_QtInv :
    (codeMat 405 : Mat3).transpose⁻¹ = (codeMat 407 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 405 : Mat3).transpose * (codeMat 407 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc374s17_contain :
    (o374SourceU_wc ⟨17, by omega⟩) ≤ actionW (codeMat 140) (codeMat 405) orbit10W := by
  change spanCodes [264, 136, 64, 40, 18, 6, 1] ≤ actionW (codeMat 140) (codeMat 405) orbit10W
  apply step109wc374_spanCodes_le_of_gens [264, 136, 64, 40, 18, 6, 1]
    (actionW (codeMat 140) (codeMat 405) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 69 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 69 (by decide)
    have hact : actionA (codeMat 140) (codeMat 405) (codeMat 69) = codeMat 264 := by
      unfold actionA
      rw [step109wc374s17_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 69 * (codeMat 407 : Mat3).transpose = codeMat 264
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 70 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 70 (by decide)
    have hact : actionA (codeMat 140) (codeMat 405) (codeMat 70) = codeMat 136 := by
      unfold actionA
      rw [step109wc374s17_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 70 * (codeMat 407 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 405) (codeMat 1) = codeMat 64 := by
      unfold actionA
      rw [step109wc374s17_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * (codeMat 407 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 140) (codeMat 405) (codeMat 256) = codeMat 40 := by
      unfold actionA
      rw [step109wc374s17_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 256 * (codeMat 407 : Mat3).transpose = codeMat 40
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 432 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide)
    have hact : actionA (codeMat 140) (codeMat 405) (codeMat 432) = codeMat 18 := by
      unfold actionA
      rw [step109wc374s17_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 432 * (codeMat 407 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 140) (codeMat 405) (codeMat 24) = codeMat 6 := by
      unfold actionA
      rw [step109wc374s17_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 24 * (codeMat 407 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 140) (codeMat 405) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc374s17_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 8 * (codeMat 407 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact

theorem step109wc374s17Dispatch :
    QuotientRankAtLeast (o374SourceU_wc ⟨17, by omega⟩) 12 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 405 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 405) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 405) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc374s17_contain hAct


private theorem step109wc374s18_QtInv :
    (codeMat 431 : Mat3).transpose⁻¹ = (codeMat 477 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 431 : Mat3).transpose * (codeMat 477 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc374s18_contain :
    (o374SourceU_wc ⟨18, by omega⟩) ≤ actionW (codeMat 266) (codeMat 431) orbit10W := by
  change spanCodes [274, 144, 82, 48, 8, 6, 1] ≤ actionW (codeMat 266) (codeMat 431) orbit10W
  apply step109wc374_spanCodes_le_of_gens [274, 144, 82, 48, 8, 6, 1]
    (actionW (codeMat 266) (codeMat 431) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 493 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 493 (by decide)
    have hact : actionA (codeMat 266) (codeMat 431) (codeMat 493) = codeMat 274 := by
      unfold actionA
      rw [step109wc374s18_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 493 * (codeMat 477 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 325 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 325 (by decide)
    have hact : actionA (codeMat 266) (codeMat 431) (codeMat 325) = codeMat 144 := by
      unfold actionA
      rw [step109wc374s18_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 325 * (codeMat 477 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 237 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 237 (by decide)
    have hact : actionA (codeMat 266) (codeMat 431) (codeMat 237) = codeMat 82 := by
      unfold actionA
      rw [step109wc374s18_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 237 * (codeMat 477 : Mat3).transpose = codeMat 82
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 431) (codeMat 2) = codeMat 48 := by
      unfold actionA
      rw [step109wc374s18_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 477 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 266) (codeMat 431) (codeMat 3) = codeMat 8 := by
      unfold actionA
      rw [step109wc374s18_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 3 * (codeMat 477 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 431) (codeMat 16) = codeMat 6 := by
      unfold actionA
      rw [step109wc374s18_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 477 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 266) (codeMat 431) (codeMat 24) = codeMat 1 := by
      unfold actionA
      rw [step109wc374s18_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 24 * (codeMat 477 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact

theorem step109wc374s18Dispatch :
    QuotientRankAtLeast (o374SourceU_wc ⟨18, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 431 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 431) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 431) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc374s18_contain hAct


private theorem step109wc374s19_QtInv :
    (codeMat 187 : Mat3).transpose⁻¹ = (codeMat 229 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 187 : Mat3).transpose * (codeMat 229 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc374s19_contain :
    (o374SourceU_wc ⟨19, by omega⟩) ≤ actionW (codeMat 142) (codeMat 187) orbit10W := by
  change spanCodes [258, 130, 72, 34, 24, 4, 1] ≤ actionW (codeMat 142) (codeMat 187) orbit10W
  apply step109wc374_spanCodes_le_of_gens [258, 130, 72, 34, 24, 4, 1]
    (actionW (codeMat 142) (codeMat 187) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 186 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 186 (by decide)
    have hact : actionA (codeMat 142) (codeMat 187) (codeMat 186) = codeMat 258 := by
      unfold actionA
      rw [step109wc374s19_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 186 * (codeMat 229 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 511 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 511 (by decide)
    have hact : actionA (codeMat 142) (codeMat 187) (codeMat 511) = codeMat 130 := by
      unfold actionA
      rw [step109wc374s19_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 511 * (codeMat 229 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 3 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 142) (codeMat 187) (codeMat 3) = codeMat 72 := by
      unfold actionA
      rw [step109wc374s19_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 3 * (codeMat 229 : Mat3).transpose = codeMat 72
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 184 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 184 (by decide)
    have hact : actionA (codeMat 142) (codeMat 187) (codeMat 184) = codeMat 34 := by
      unfold actionA
      rw [step109wc374s19_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 184 * (codeMat 229 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 142) (codeMat 187) (codeMat 256) = codeMat 24 := by
      unfold actionA
      rw [step109wc374s19_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 256 * (codeMat 229 : Mat3).transpose = codeMat 24
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 142) (codeMat 187) (codeMat 16) = codeMat 4 := by
      unfold actionA
      rw [step109wc374s19_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 16 * (codeMat 229 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 142) (codeMat 187) (codeMat 24) = codeMat 1 := by
      unfold actionA
      rw [step109wc374s19_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 24 * (codeMat 229 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc374_codeMat_mem_actionW_of_witness hw hact

theorem step109wc374s19Dispatch :
    QuotientRankAtLeast (o374SourceU_wc ⟨19, by omega⟩) 12 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 187 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 187) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 187) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc374s19_contain hAct

theorem step109wc374_all_dispatch (i : Fin 20) :
    QuotientRankAtLeast (o374SourceU_wc i) (o374SourceLb_wc i) := by
  fin_cases i
  · exact step109wc374s0Dispatch
  · exact step109wc374s1Dispatch
  · exact step109wc374s2Dispatch
  · exact step109wc374s3Dispatch
  · exact step109wc374s4Dispatch
  · exact step109wc374s5Dispatch
  · exact step109wc374s6Dispatch
  · exact step109wc374s7Dispatch
  · exact step109wc374s8Dispatch
  · exact step109wc374s9Dispatch
  · exact step109wc374s10Dispatch
  · exact step109wc374s11Dispatch
  · exact step109wc374s12Dispatch
  · exact step109wc374s13Dispatch
  · exact step109wc374s14Dispatch
  · exact step109wc374s15Dispatch
  · exact step109wc374s16Dispatch
  · exact step109wc374s17Dispatch
  · exact step109wc374s18Dispatch
  · exact step109wc374s19Dispatch

theorem step109_orbit374_lb17_wc : QuotientRankAtLeast o374W_wc 17 :=
  o374Lb17_wc step109wc374_all_dispatch

end QiushiMatmul
