import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit322Consumer
import QiushiStep126Mono175From75
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit214Dispatch
import QiushiStep128Mono189From80T
import QiushiStep99Orbit65Dispatch
import QiushiOrbit10FP
import QiushiOrbit14FP

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc322_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc322_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc322s0_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc322s0_contain :
    (o322SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 473) (codeMat 273) o175W_mono := by
  change spanCodes [290, 160, 22, 10, 1] ≤ actionW (codeMat 473) (codeMat 273) o175W_mono
  apply step109wc322_spanCodes_le_of_gens [290, 160, 22, 10, 1]
    (actionW (codeMat 473) (codeMat 273) o175W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 262 ∈ o175W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 160, 20, 10, 1] 262 (by decide)
    have hact : actionA (codeMat 473) (codeMat 273) (codeMat 262) = codeMat 290 := by
      unfold actionA
      rw [step109wc322s0_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 262 * (codeMat 273 : Mat3).transpose = codeMat 290
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 180 ∈ o175W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 160, 20, 10, 1] 180 (by decide)
    have hact : actionA (codeMat 473) (codeMat 273) (codeMat 180) = codeMat 160 := by
      unfold actionA
      rw [step109wc322s0_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 180 * (codeMat 273 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 20 ∈ o175W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 160, 20, 10, 1] 20 (by decide)
    have hact : actionA (codeMat 473) (codeMat 273) (codeMat 20) = codeMat 22 := by
      unfold actionA
      rw [step109wc322s0_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 20 * (codeMat 273 : Mat3).transpose = codeMat 22
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 11 ∈ o175W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 160, 20, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 473) (codeMat 273) (codeMat 11) = codeMat 10 := by
      unfold actionA
      rw [step109wc322s0_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 11 * (codeMat 273 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o175W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 160, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 473) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc322s0_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact

theorem step109wc322s0Dispatch :
    QuotientRankAtLeast (o322SourceU_wc ⟨0, by omega⟩) 16 := by
  have hP : Invertible (codeMat 473 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 473) (codeMat 273) o175W_mono) 16 :=
    @quotientRankAtLeast_action (codeMat 473) (codeMat 273) hP hQ o175W_mono 16
      orbit175_lb16_mono
  exact quotientRankAtLeast_mono step109wc322s0_contain hAct


private theorem step109wc322s1_QtInv :
    (codeMat 277 : Mat3).transpose⁻¹ = (codeMat 277 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 277 : Mat3).transpose * (codeMat 277 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc322s1_contain :
    (o322SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 345) (codeMat 277) o201W_wc := by
  change spanCodes [274, 134, 38, 10, 1] ≤ actionW (codeMat 345) (codeMat 277) o201W_wc
  apply step109wc322_spanCodes_le_of_gens [274, 134, 38, 10, 1]
    (actionW (codeMat 345) (codeMat 277) o201W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 341 ∈ o201W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [340, 132, 32, 10, 1] 341 (by decide)
    have hact : actionA (codeMat 345) (codeMat 277) (codeMat 341) = codeMat 274 := by
      unfold actionA
      rw [step109wc322s1_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 341 * (codeMat 277 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 133 ∈ o201W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [340, 132, 32, 10, 1] 133 (by decide)
    have hact : actionA (codeMat 345) (codeMat 277) (codeMat 133) = codeMat 134 := by
      unfold actionA
      rw [step109wc322s1_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 133 * (codeMat 277 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 42 ∈ o201W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [340, 132, 32, 10, 1] 42 (by decide)
    have hact : actionA (codeMat 345) (codeMat 277) (codeMat 42) = codeMat 38 := by
      unfold actionA
      rw [step109wc322s1_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 42 * (codeMat 277 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 11 ∈ o201W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [340, 132, 32, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 345) (codeMat 277) (codeMat 11) = codeMat 10 := by
      unfold actionA
      rw [step109wc322s1_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 11 * (codeMat 277 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o201W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [340, 132, 32, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 345) (codeMat 277) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc322s1_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 1 * (codeMat 277 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact

theorem step109wc322s1Dispatch :
    QuotientRankAtLeast (o322SourceU_wc ⟨1, by omega⟩) 16 := by
  have hP : Invertible (codeMat 345 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 277 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 345) (codeMat 277) o201W_wc) 16 :=
    @quotientRankAtLeast_action (codeMat 345) (codeMat 277) hP hQ o201W_wc 16
      step109_orbit201_lb16_wc
  exact quotientRankAtLeast_mono step109wc322s1_contain hAct

private def step109wc322s2SrcT : Submodule F2 Mat3 := spanCodes [256, 132, 80, 10, 1]

private theorem step109wc322s2SrcT_lb : QuotientRankAtLeast step109wc322s2SrcT 16 := by
  have ht := quotientRankAtLeast_transpose step109_orbit164_lb16_wc
  have hle : step109wc322s2SrcT ≤ transposeW o164W_wc := by
    unfold step109wc322s2SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4
    · subst h0
      show codeMat 256 ∈ Submodule.map transposeLinearMap o164W_wc
      exact ⟨codeMat 256, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 10, 1] 256 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 132 ∈ Submodule.map transposeLinearMap o164W_wc
      exact ⟨codeMat 96, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 10, 1] 96 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 80 ∈ Submodule.map transposeLinearMap o164W_wc
      exact ⟨codeMat 20, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 10, 1] 20 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 10 ∈ Submodule.map transposeLinearMap o164W_wc
      exact ⟨codeMat 10, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 10, 1] 10 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 1 ∈ Submodule.map transposeLinearMap o164W_wc
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 10, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc322s2_QtInv :
    (codeMat 116 : Mat3).transpose⁻¹ = (codeMat 92 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 116 : Mat3).transpose * (codeMat 92 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc322s2_contain :
    (o322SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 115) (codeMat 116) step109wc322s2SrcT := by
  change spanCodes [258, 150, 54, 10, 1] ≤ actionW (codeMat 115) (codeMat 116) step109wc322s2SrcT
  apply step109wc322_spanCodes_le_of_gens [258, 150, 54, 10, 1]
    (actionW (codeMat 115) (codeMat 116) step109wc322s2SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 91 ∈ step109wc322s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 80, 10, 1] 91 (by decide)
    have hact : actionA (codeMat 115) (codeMat 116) (codeMat 91) = codeMat 258 := by
      unfold actionA
      rw [step109wc322s2_QtInv]
      show (codeMat 115 : Mat3).transpose * codeMat 91 * (codeMat 92 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 80 ∈ step109wc322s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 80, 10, 1] 80 (by decide)
    have hact : actionA (codeMat 115) (codeMat 116) (codeMat 80) = codeMat 150 := by
      unfold actionA
      rw [step109wc322s2_QtInv]
      show (codeMat 115 : Mat3).transpose * codeMat 80 * (codeMat 92 : Mat3).transpose = codeMat 150
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ step109wc322s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 80, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 115) (codeMat 116) (codeMat 1) = codeMat 54 := by
      unfold actionA
      rw [step109wc322s2_QtInv]
      show (codeMat 115 : Mat3).transpose * codeMat 1 * (codeMat 92 : Mat3).transpose = codeMat 54
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 388 ∈ step109wc322s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 80, 10, 1] 388 (by decide)
    have hact : actionA (codeMat 115) (codeMat 116) (codeMat 388) = codeMat 10 := by
      unfold actionA
      rw [step109wc322s2_QtInv]
      show (codeMat 115 : Mat3).transpose * codeMat 388 * (codeMat 92 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ step109wc322s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 80, 10, 1] 256 (by decide)
    have hact : actionA (codeMat 115) (codeMat 116) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc322s2_QtInv]
      show (codeMat 115 : Mat3).transpose * codeMat 256 * (codeMat 92 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact

theorem step109wc322s2Dispatch :
    QuotientRankAtLeast (o322SourceU_wc ⟨2, by omega⟩) 16 := by
  have hP : Invertible (codeMat 115 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 116 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 115) (codeMat 116) step109wc322s2SrcT) 16 :=
    @quotientRankAtLeast_action (codeMat 115) (codeMat 116) hP hQ step109wc322s2SrcT 16
      step109wc322s2SrcT_lb
  exact quotientRankAtLeast_mono step109wc322s2_contain hAct

private def step109wc322s3SrcT : Submodule F2 Mat3 := spanCodes [274, 160, 80, 10, 1]

private theorem step109wc322s3SrcT_lb : QuotientRankAtLeast step109wc322s3SrcT 16 := by
  have ht := quotientRankAtLeast_transpose orbit175_lb16_mono
  have hle : step109wc322s3SrcT ≤ transposeW o175W_mono := by
    unfold step109wc322s3SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4
    · subst h0
      show codeMat 274 ∈ Submodule.map transposeLinearMap o175W_mono
      exact ⟨codeMat 280, spanContainsCodeCore_implies_mem_spanCodes [262, 160, 20, 10, 1] 280 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 160 ∈ Submodule.map transposeLinearMap o175W_mono
      exact ⟨codeMat 160, spanContainsCodeCore_implies_mem_spanCodes [262, 160, 20, 10, 1] 160 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 80 ∈ Submodule.map transposeLinearMap o175W_mono
      exact ⟨codeMat 20, spanContainsCodeCore_implies_mem_spanCodes [262, 160, 20, 10, 1] 20 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 10 ∈ Submodule.map transposeLinearMap o175W_mono
      exact ⟨codeMat 10, spanContainsCodeCore_implies_mem_spanCodes [262, 160, 20, 10, 1] 10 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 1 ∈ Submodule.map transposeLinearMap o175W_mono
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [262, 160, 20, 10, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc322s3_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = (codeMat 275 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * (codeMat 275 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc322s3_contain :
    (o322SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 465) (codeMat 275) step109wc322s3SrcT := by
  change spanCodes [308, 160, 80, 10, 1] ≤ actionW (codeMat 465) (codeMat 275) step109wc322s3SrcT
  apply step109wc322_spanCodes_le_of_gens [308, 160, 80, 10, 1]
    (actionW (codeMat 465) (codeMat 275) step109wc322s3SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 280 ∈ step109wc322s3SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 160, 80, 10, 1] 280 (by decide)
    have hact : actionA (codeMat 465) (codeMat 275) (codeMat 280) = codeMat 308 := by
      unfold actionA
      rw [step109wc322s3_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 280 * (codeMat 275 : Mat3).transpose = codeMat 308
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 251 ∈ step109wc322s3SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 160, 80, 10, 1] 251 (by decide)
    have hact : actionA (codeMat 465) (codeMat 275) (codeMat 251) = codeMat 160 := by
      unfold actionA
      rw [step109wc322s3_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 251 * (codeMat 275 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 81 ∈ step109wc322s3SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 160, 80, 10, 1] 81 (by decide)
    have hact : actionA (codeMat 465) (codeMat 275) (codeMat 81) = codeMat 80 := by
      unfold actionA
      rw [step109wc322s3_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 81 * (codeMat 275 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 11 ∈ step109wc322s3SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 160, 80, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 465) (codeMat 275) (codeMat 11) = codeMat 10 := by
      unfold actionA
      rw [step109wc322s3_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 11 * (codeMat 275 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ step109wc322s3SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 160, 80, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 465) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc322s3_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 1 * (codeMat 275 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact

theorem step109wc322s3Dispatch :
    QuotientRankAtLeast (o322SourceU_wc ⟨3, by omega⟩) 16 := by
  have hP : Invertible (codeMat 465 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 465) (codeMat 275) step109wc322s3SrcT) 16 :=
    @quotientRankAtLeast_action (codeMat 465) (codeMat 275) hP hQ step109wc322s3SrcT 16
      step109wc322s3SrcT_lb
  exact quotientRankAtLeast_mono step109wc322s3_contain hAct


private theorem step109wc322s4_QtInv :
    (codeMat 482 : Mat3).transpose⁻¹ = (codeMat 143 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 482 : Mat3).transpose * (codeMat 143 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc322s4_contain :
    (o322SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 85) (codeMat 482) o164W_wc := by
  change spanCodes [308, 160, 98, 10, 1] ≤ actionW (codeMat 85) (codeMat 482) o164W_wc
  apply step109wc322_spanCodes_le_of_gens [308, 160, 98, 10, 1]
    (actionW (codeMat 85) (codeMat 482) o164W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 30 ∈ o164W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 10, 1] 30 (by decide)
    have hact : actionA (codeMat 85) (codeMat 482) (codeMat 30) = codeMat 308 := by
      unfold actionA
      rw [step109wc322s4_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 30 * (codeMat 143 : Mat3).transpose = codeMat 308
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 373 ∈ o164W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 10, 1] 373 (by decide)
    have hact : actionA (codeMat 85) (codeMat 482) (codeMat 373) = codeMat 160 := by
      unfold actionA
      rw [step109wc322s4_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 373 * (codeMat 143 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 116 ∈ o164W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 10, 1] 116 (by decide)
    have hact : actionA (codeMat 85) (codeMat 482) (codeMat 116) = codeMat 98 := by
      unfold actionA
      rw [step109wc322s4_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 116 * (codeMat 143 : Mat3).transpose = codeMat 98
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 352 ∈ o164W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 10, 1] 352 (by decide)
    have hact : actionA (codeMat 85) (codeMat 482) (codeMat 352) = codeMat 10 := by
      unfold actionA
      rw [step109wc322s4_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 352 * (codeMat 143 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ o164W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 10, 1] 256 (by decide)
    have hact : actionA (codeMat 85) (codeMat 482) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc322s4_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 256 * (codeMat 143 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact

theorem step109wc322s4Dispatch :
    QuotientRankAtLeast (o322SourceU_wc ⟨4, by omega⟩) 16 := by
  have hP : Invertible (codeMat 85 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 482 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 85) (codeMat 482) o164W_wc) 16 :=
    @quotientRankAtLeast_action (codeMat 85) (codeMat 482) hP hQ o164W_wc 16
      step109_orbit164_lb16_wc
  exact quotientRankAtLeast_mono step109wc322s4_contain hAct


private theorem step109wc322s5_QtInv :
    (codeMat 279 : Mat3).transpose⁻¹ = (codeMat 279 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 279 : Mat3).transpose * (codeMat 279 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc322s5_contain :
    (o322SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 345) (codeMat 279) o214W_wc := by
  change spanCodes [308, 160, 102, 10, 1] ≤ actionW (codeMat 345) (codeMat 279) o214W_wc
  apply step109wc322_spanCodes_le_of_gens [308, 160, 102, 10, 1]
    (actionW (codeMat 345) (codeMat 279) o214W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 374 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 374 (by decide)
    have hact : actionA (codeMat 345) (codeMat 279) (codeMat 374) = codeMat 308 := by
      unfold actionA
      rw [step109wc322s5_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 374 * (codeMat 279 : Mat3).transpose = codeMat 308
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 238 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 238 (by decide)
    have hact : actionA (codeMat 345) (codeMat 279) (codeMat 238) = codeMat 160 := by
      unfold actionA
      rw [step109wc322s5_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 238 * (codeMat 279 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 106 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 106 (by decide)
    have hact : actionA (codeMat 345) (codeMat 279) (codeMat 106) = codeMat 102 := by
      unfold actionA
      rw [step109wc322s5_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 106 * (codeMat 279 : Mat3).transpose = codeMat 102
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 10 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 345) (codeMat 279) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step109wc322s5_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 10 * (codeMat 279 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o214W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 96, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 345) (codeMat 279) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc322s5_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 1 * (codeMat 279 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact

theorem step109wc322s5Dispatch :
    QuotientRankAtLeast (o322SourceU_wc ⟨5, by omega⟩) 16 := by
  have hP : Invertible (codeMat 345 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 279 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 345) (codeMat 279) o214W_wc) 16 :=
    @quotientRankAtLeast_action (codeMat 345) (codeMat 279) hP hQ o214W_wc 16
      step109_orbit214_lb16_wc
  exact quotientRankAtLeast_mono step109wc322s5_contain hAct

private def step109wc322s6SrcT : Submodule F2 Mat3 := spanCodes [308, 128, 96, 10, 1]

private theorem step109wc322s6SrcT_lb : QuotientRankAtLeast step109wc322s6SrcT 16 := by
  have ht := quotientRankAtLeast_transpose step109_orbit201_lb16_wc
  have hle : step109wc322s6SrcT ≤ transposeW o201W_wc := by
    unfold step109wc322s6SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4
    · subst h0
      show codeMat 308 ∈ Submodule.map transposeLinearMap o201W_wc
      exact ⟨codeMat 464, spanContainsCodeCore_implies_mem_spanCodes [340, 132, 32, 10, 1] 464 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 128 ∈ Submodule.map transposeLinearMap o201W_wc
      exact ⟨codeMat 32, spanContainsCodeCore_implies_mem_spanCodes [340, 132, 32, 10, 1] 32 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 96 ∈ Submodule.map transposeLinearMap o201W_wc
      exact ⟨codeMat 132, spanContainsCodeCore_implies_mem_spanCodes [340, 132, 32, 10, 1] 132 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 10 ∈ Submodule.map transposeLinearMap o201W_wc
      exact ⟨codeMat 10, spanContainsCodeCore_implies_mem_spanCodes [340, 132, 32, 10, 1] 10 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 1 ∈ Submodule.map transposeLinearMap o201W_wc
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [340, 132, 32, 10, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc322s6_QtInv :
    (codeMat 311 : Mat3).transpose⁻¹ = (codeMat 307 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 311 : Mat3).transpose * (codeMat 307 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc322s6_contain :
    (o322SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 401) (codeMat 311) step109wc322s6SrcT := by
  change spanCodes [308, 160, 114, 10, 1] ≤ actionW (codeMat 401) (codeMat 311) step109wc322s6SrcT
  apply step109wc322_spanCodes_le_of_gens [308, 160, 114, 10, 1]
    (actionW (codeMat 401) (codeMat 311) step109wc322s6SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 479 ∈ step109wc322s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [308, 128, 96, 10, 1] 479 (by decide)
    have hact : actionA (codeMat 401) (codeMat 311) (codeMat 479) = codeMat 308 := by
      unfold actionA
      rw [step109wc322s6_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 479 * (codeMat 307 : Mat3).transpose = codeMat 308
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 224 ∈ step109wc322s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [308, 128, 96, 10, 1] 224 (by decide)
    have hact : actionA (codeMat 401) (codeMat 311) (codeMat 224) = codeMat 160 := by
      unfold actionA
      rw [step109wc322s6_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 224 * (codeMat 307 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 107 ∈ step109wc322s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [308, 128, 96, 10, 1] 107 (by decide)
    have hact : actionA (codeMat 401) (codeMat 311) (codeMat 107) = codeMat 114 := by
      unfold actionA
      rw [step109wc322s6_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 107 * (codeMat 307 : Mat3).transpose = codeMat 114
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 11 ∈ step109wc322s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [308, 128, 96, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 401) (codeMat 311) (codeMat 11) = codeMat 10 := by
      unfold actionA
      rw [step109wc322s6_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 11 * (codeMat 307 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ step109wc322s6SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [308, 128, 96, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 401) (codeMat 311) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc322s6_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 1 * (codeMat 307 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact

theorem step109wc322s6Dispatch :
    QuotientRankAtLeast (o322SourceU_wc ⟨6, by omega⟩) 16 := by
  have hP : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 311 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 401) (codeMat 311) step109wc322s6SrcT) 16 :=
    @quotientRankAtLeast_action (codeMat 401) (codeMat 311) hP hQ step109wc322s6SrcT 16
      step109wc322s6SrcT_lb
  exact quotientRankAtLeast_mono step109wc322s6_contain hAct

private def step109wc322s7SrcT : Submodule F2 Mat3 := spanCodes [306, 132, 96, 10, 1]

private theorem step109wc322s7SrcT_lb : QuotientRankAtLeast step109wc322s7SrcT 16 := by
  have ht := quotientRankAtLeast_transpose step109_orbit214_lb16_wc
  have hle : step109wc322s7SrcT ≤ transposeW o214W_wc := by
    unfold step109wc322s7SrcT transposeW
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

private theorem step109wc322s7_QtInv :
    (codeMat 311 : Mat3).transpose⁻¹ = (codeMat 307 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 311 : Mat3).transpose * (codeMat 307 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc322s7_contain :
    (o322SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 409) (codeMat 311) step109wc322s7SrcT := by
  change spanCodes [308, 160, 116, 10, 1] ≤ actionW (codeMat 409) (codeMat 311) step109wc322s7SrcT
  apply step109wc322_spanCodes_le_of_gens [308, 160, 116, 10, 1]
    (actionW (codeMat 409) (codeMat 311) step109wc322s7SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 476 ∈ step109wc322s7SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 476 (by decide)
    have hact : actionA (codeMat 409) (codeMat 311) (codeMat 476) = codeMat 308 := by
      unfold actionA
      rw [step109wc322s7_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 476 * (codeMat 307 : Mat3).transpose = codeMat 308
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 228 ∈ step109wc322s7SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 228 (by decide)
    have hact : actionA (codeMat 409) (codeMat 311) (codeMat 228) = codeMat 160 := by
      unfold actionA
      rw [step109wc322s7_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 228 * (codeMat 307 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 106 ∈ step109wc322s7SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 106 (by decide)
    have hact : actionA (codeMat 409) (codeMat 311) (codeMat 106) = codeMat 116 := by
      unfold actionA
      rw [step109wc322s7_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 106 * (codeMat 307 : Mat3).transpose = codeMat 116
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 10 ∈ step109wc322s7SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 409) (codeMat 311) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step109wc322s7_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 10 * (codeMat 307 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ step109wc322s7SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [306, 132, 96, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 409) (codeMat 311) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc322s7_QtInv]
      show (codeMat 409 : Mat3).transpose * codeMat 1 * (codeMat 307 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact

theorem step109wc322s7Dispatch :
    QuotientRankAtLeast (o322SourceU_wc ⟨7, by omega⟩) 16 := by
  have hP : Invertible (codeMat 409 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 311 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 409) (codeMat 311) step109wc322s7SrcT) 16 :=
    @quotientRankAtLeast_action (codeMat 409) (codeMat 311) hP hQ step109wc322s7SrcT 16
      step109wc322s7SrcT_lb
  exact quotientRankAtLeast_mono step109wc322s7_contain hAct

private def step109wc322s8SrcT : Submodule F2 Mat3 := spanCodes [338, 128, 32, 10, 1]

private theorem step109wc322s8SrcT_lb : QuotientRankAtLeast step109wc322s8SrcT 15 := by
  have ht := quotientRankAtLeast_transpose orbit189_lb15_mono
  have hle : step109wc322s8SrcT ≤ transposeW o189W_mono := by
    unfold step109wc322s8SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4
    · subst h0
      show codeMat 338 ∈ Submodule.map transposeLinearMap o189W_mono
      exact ⟨codeMat 284, spanContainsCodeCore_implies_mem_spanCodes [278, 128, 32, 10, 1] 284 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 128 ∈ Submodule.map transposeLinearMap o189W_mono
      exact ⟨codeMat 32, spanContainsCodeCore_implies_mem_spanCodes [278, 128, 32, 10, 1] 32 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 32 ∈ Submodule.map transposeLinearMap o189W_mono
      exact ⟨codeMat 128, spanContainsCodeCore_implies_mem_spanCodes [278, 128, 32, 10, 1] 128 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 10 ∈ Submodule.map transposeLinearMap o189W_mono
      exact ⟨codeMat 10, spanContainsCodeCore_implies_mem_spanCodes [278, 128, 32, 10, 1] 10 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 1 ∈ Submodule.map transposeLinearMap o189W_mono
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [278, 128, 32, 10, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc322s8_QtInv :
    (codeMat 277 : Mat3).transpose⁻¹ = (codeMat 277 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 277 : Mat3).transpose * (codeMat 277 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc322s8_contain :
    (o322SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 337) (codeMat 277) step109wc322s8SrcT := by
  change spanCodes [278, 130, 34, 10, 1] ≤ actionW (codeMat 337) (codeMat 277) step109wc322s8SrcT
  apply step109wc322_spanCodes_le_of_gens [278, 130, 34, 10, 1]
    (actionW (codeMat 337) (codeMat 277) step109wc322s8SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 338 ∈ step109wc322s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [338, 128, 32, 10, 1] 338 (by decide)
    have hact : actionA (codeMat 337) (codeMat 277) (codeMat 338) = codeMat 278 := by
      unfold actionA
      rw [step109wc322s8_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 338 * (codeMat 277 : Mat3).transpose = codeMat 278
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 128 ∈ step109wc322s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [338, 128, 32, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 337) (codeMat 277) (codeMat 128) = codeMat 130 := by
      unfold actionA
      rw [step109wc322s8_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 128 * (codeMat 277 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 42 ∈ step109wc322s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [338, 128, 32, 10, 1] 42 (by decide)
    have hact : actionA (codeMat 337) (codeMat 277) (codeMat 42) = codeMat 34 := by
      unfold actionA
      rw [step109wc322s8_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 42 * (codeMat 277 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 10 ∈ step109wc322s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [338, 128, 32, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 337) (codeMat 277) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step109wc322s8_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 10 * (codeMat 277 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ step109wc322s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [338, 128, 32, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 337) (codeMat 277) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc322s8_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 1 * (codeMat 277 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact

theorem step109wc322s8Dispatch :
    QuotientRankAtLeast (o322SourceU_wc ⟨8, by omega⟩) 15 := by
  have hP : Invertible (codeMat 337 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 277 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 337) (codeMat 277) step109wc322s8SrcT) 15 :=
    @quotientRankAtLeast_action (codeMat 337) (codeMat 277) hP hQ step109wc322s8SrcT 15
      step109wc322s8SrcT_lb
  exact quotientRankAtLeast_mono step109wc322s8_contain hAct


private theorem step109wc322s9_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = (codeMat 305 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * (codeMat 305 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc322s9_contain :
    (o322SourceU_wc ⟨9, by omega⟩) ≤ actionW (codeMat 401) (codeMat 305) o189W_mono := by
  change spanCodes [260, 144, 48, 10, 1] ≤ actionW (codeMat 401) (codeMat 305) o189W_mono
  apply step109wc322_spanCodes_le_of_gens [260, 144, 48, 10, 1]
    (actionW (codeMat 401) (codeMat 305) o189W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 438 ∈ o189W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 128, 32, 10, 1] 438 (by decide)
    have hact : actionA (codeMat 401) (codeMat 305) (codeMat 438) = codeMat 260 := by
      unfold actionA
      rw [step109wc322s9_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 438 * (codeMat 305 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 128 ∈ o189W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 128, 32, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 401) (codeMat 305) (codeMat 128) = codeMat 144 := by
      unfold actionA
      rw [step109wc322s9_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 128 * (codeMat 305 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ o189W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 128, 32, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 401) (codeMat 305) (codeMat 32) = codeMat 48 := by
      unfold actionA
      rw [step109wc322s9_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 32 * (codeMat 305 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 10 ∈ o189W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 128, 32, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 401) (codeMat 305) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [step109wc322s9_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 10 * (codeMat 305 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o189W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 128, 32, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 401) (codeMat 305) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc322s9_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 1 * (codeMat 305 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact

theorem step109wc322s9Dispatch :
    QuotientRankAtLeast (o322SourceU_wc ⟨9, by omega⟩) 15 := by
  have hP : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 401) (codeMat 305) o189W_mono) 15 :=
    @quotientRankAtLeast_action (codeMat 401) (codeMat 305) hP hQ o189W_mono 15
      orbit189_lb15_mono
  exact quotientRankAtLeast_mono step109wc322s9_contain hAct


private theorem step109wc322s10_QtInv :
    (codeMat 179 : Mat3).transpose⁻¹ = (codeMat 421 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 179 : Mat3).transpose * (codeMat 421 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc322s10_contain :
    (o322SourceU_wc ⟨10, by omega⟩) ≤ actionW (codeMat 305) (codeMat 179) o65W := by
  change spanCodes [288, 160, 70, 20, 10, 1] ≤ actionW (codeMat 305) (codeMat 179) o65W
  apply step109wc322_spanCodes_le_of_gens [288, 160, 70, 20, 10, 1]
    (actionW (codeMat 305) (codeMat 179) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 16 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 305) (codeMat 179) (codeMat 16) = codeMat 288 := by
      unfold actionA
      rw [step109wc322s10_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 16 * (codeMat 421 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 336 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 336 (by decide)
    have hact : actionA (codeMat 305) (codeMat 179) (codeMat 336) = codeMat 160 := by
      unfold actionA
      rw [step109wc322s10_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 336 * (codeMat 421 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 69 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 305) (codeMat 179) (codeMat 69) = codeMat 70 := by
      unfold actionA
      rw [step109wc322s10_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 69 * (codeMat 421 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 506 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 506 (by decide)
    have hact : actionA (codeMat 305) (codeMat 179) (codeMat 506) = codeMat 20 := by
      unfold actionA
      rw [step109wc322s10_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 506 * (codeMat 421 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 79 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 79 (by decide)
    have hact : actionA (codeMat 305) (codeMat 179) (codeMat 79) = codeMat 10 := by
      unfold actionA
      rw [step109wc322s10_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 79 * (codeMat 421 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 305) (codeMat 179) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc322s10_QtInv]
      show (codeMat 305 : Mat3).transpose * codeMat 1 * (codeMat 421 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact

theorem step109wc322s10Dispatch :
    QuotientRankAtLeast (o322SourceU_wc ⟨10, by omega⟩) 15 := by
  have hP : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 179 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 305) (codeMat 179) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 305) (codeMat 179) hP hQ o65W 15
      step99_orbit65_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc322s10_contain hAct


private theorem step109wc322s11_QtInv :
    (codeMat 302 : Mat3).transpose⁻¹ = (codeMat 302 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 302 : Mat3).transpose * (codeMat 302 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc322s11_contain :
    (o322SourceU_wc ⟨11, by omega⟩) ≤ actionW (codeMat 266) (codeMat 302) orbit10W := by
  change spanCodes [292, 160, 68, 16, 8, 2, 1] ≤ actionW (codeMat 266) (codeMat 302) orbit10W
  apply step109wc322_spanCodes_le_of_gens [292, 160, 68, 16, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 302) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 511 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 511 (by decide)
    have hact : actionA (codeMat 266) (codeMat 302) (codeMat 511) = codeMat 292 := by
      unfold actionA
      rw [step109wc322s11_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 511 * (codeMat 302 : Mat3).transpose = codeMat 292
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 71 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 71 (by decide)
    have hact : actionA (codeMat 266) (codeMat 302) (codeMat 71) = codeMat 160 := by
      unfold actionA
      rw [step109wc322s11_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 71 * (codeMat 302 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 184 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 184 (by decide)
    have hact : actionA (codeMat 266) (codeMat 302) (codeMat 184) = codeMat 68 := by
      unfold actionA
      rw [step109wc322s11_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 184 * (codeMat 302 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 302) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc322s11_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 302 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 302) (codeMat 2) = codeMat 8 := by
      unfold actionA
      rw [step109wc322s11_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 302 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 302) (codeMat 8) = codeMat 2 := by
      unfold actionA
      rw [step109wc322s11_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 302 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 302) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc322s11_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 302 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact

theorem step109wc322s11Dispatch :
    QuotientRankAtLeast (o322SourceU_wc ⟨11, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 302 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 302) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 302) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc322s11_contain hAct


private theorem step109wc322s12_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc322s12_contain :
    (o322SourceU_wc ⟨12, by omega⟩) ≤ actionW (codeMat 273) (codeMat 140) orbit14W := by
  change spanCodes [272, 128, 64, 32, 10, 4, 1] ≤ actionW (codeMat 273) (codeMat 140) orbit14W
  apply step109wc322_spanCodes_le_of_gens [272, 128, 64, 32, 10, 4, 1]
    (actionW (codeMat 273) (codeMat 140) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 96) = codeMat 272 := by
      unfold actionA
      rw [step109wc322s12_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 96 * (codeMat 98 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 256) = codeMat 128 := by
      unfold actionA
      rw [step109wc322s12_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 98 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 128) = codeMat 64 := by
      unfold actionA
      rw [step109wc322s12_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 128 * (codeMat 98 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc322s12_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 20 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 20) = codeMat 10 := by
      unfold actionA
      rw [step109wc322s12_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * (codeMat 98 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step109wc322s12_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc322s12_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact

theorem step109wc322s12Dispatch :
    QuotientRankAtLeast (o322SourceU_wc ⟨12, by omega⟩) 12 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 140) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 140) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc322s12_contain hAct


private theorem step109wc322s13_QtInv :
    (codeMat 428 : Mat3).transpose⁻¹ = (codeMat 107 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 428 : Mat3).transpose * (codeMat 107 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc322s13_contain :
    (o322SourceU_wc ⟨13, by omega⟩) ≤ actionW (codeMat 465) (codeMat 428) orbit14W := by
  change spanCodes [256, 146, 66, 50, 10, 6, 1] ≤ actionW (codeMat 465) (codeMat 428) orbit14W
  apply step109wc322_spanCodes_le_of_gens [256, 146, 66, 50, 10, 6, 1]
    (actionW (codeMat 465) (codeMat 428) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 511 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 511 (by decide)
    have hact : actionA (codeMat 465) (codeMat 428) (codeMat 511) = codeMat 256 := by
      unfold actionA
      rw [step109wc322s13_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 511 * (codeMat 107 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 465) (codeMat 428) (codeMat 256) = codeMat 146 := by
      unfold actionA
      rw [step109wc322s13_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 256 * (codeMat 107 : Mat3).transpose = codeMat 146
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 150 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 150 (by decide)
    have hact : actionA (codeMat 465) (codeMat 428) (codeMat 150) = codeMat 66 := by
      unfold actionA
      rw [step109wc322s13_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 150 * (codeMat 107 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 28 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 28 (by decide)
    have hact : actionA (codeMat 465) (codeMat 428) (codeMat 28) = codeMat 50 := by
      unfold actionA
      rw [step109wc322s13_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 28 * (codeMat 107 : Mat3).transpose = codeMat 50
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 20 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 20 (by decide)
    have hact : actionA (codeMat 465) (codeMat 428) (codeMat 20) = codeMat 10 := by
      unfold actionA
      rw [step109wc322s13_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 20 * (codeMat 107 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 465) (codeMat 428) (codeMat 3) = codeMat 6 := by
      unfold actionA
      rw [step109wc322s13_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 3 * (codeMat 107 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 465) (codeMat 428) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc322s13_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 2 * (codeMat 107 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc322_codeMat_mem_actionW_of_witness hw hact

theorem step109wc322s13Dispatch :
    QuotientRankAtLeast (o322SourceU_wc ⟨13, by omega⟩) 12 := by
  have hP : Invertible (codeMat 465 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 428 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 465) (codeMat 428) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 465) (codeMat 428) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc322s13_contain hAct

theorem step109wc322_all_dispatch (i : Fin 14) :
    QuotientRankAtLeast (o322SourceU_wc i) (o322SourceLb_wc i) := by
  fin_cases i
  · exact step109wc322s0Dispatch
  · exact step109wc322s1Dispatch
  · exact step109wc322s2Dispatch
  · exact step109wc322s3Dispatch
  · exact step109wc322s4Dispatch
  · exact step109wc322s5Dispatch
  · exact step109wc322s6Dispatch
  · exact step109wc322s7Dispatch
  · exact step109wc322s8Dispatch
  · exact step109wc322s9Dispatch
  · exact step109wc322s10Dispatch
  · exact step109wc322s11Dispatch
  · exact step109wc322s12Dispatch
  · exact step109wc322s13Dispatch

theorem step109_orbit322_lb17_wc : QuotientRankAtLeast o322W_wc 17 :=
  o322Lb17_wc step109wc322_all_dispatch

end QiushiMatmul
