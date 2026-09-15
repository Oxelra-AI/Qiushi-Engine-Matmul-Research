import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit281Consumer
import QiushiMonoOrbit149From65
import QiushiWcOrbit111Dispatch
import QiushiOrbit11FP
import QiushiOrbit10FP

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc281_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc281_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc281s0_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc281s0_contain :
    (o281SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 161) (codeMat 161) o149W_mono := by
  change spanCodes [256, 68, 16, 10, 1] ≤ actionW (codeMat 161) (codeMat 161) o149W_mono
  apply step109wc281_spanCodes_le_of_gens [256, 68, 16, 10, 1]
    (actionW (codeMat 161) (codeMat 161) o149W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 16 ∈ o149W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 16) = codeMat 256 := by
      unfold actionA
      rw [step109wc281s0_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 16 * (codeMat 161 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 10 ∈ o149W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 10) = codeMat 68 := by
      unfold actionA
      rw [step109wc281s0_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 10 * (codeMat 161 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 256 ∈ o149W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 16, 10, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step109wc281s0_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 161 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 68 ∈ o149W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 16, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 68) = codeMat 10 := by
      unfold actionA
      rw [step109wc281s0_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 68 * (codeMat 161 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o149W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc281s0_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact

theorem step109wc281s0Dispatch :
    QuotientRankAtLeast (o281SourceU_wc ⟨0, by omega⟩) 15 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 161) o149W_mono) 15 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 161) hP hQ o149W_mono 15
      orbit149_lb15_mono
  exact quotientRankAtLeast_mono step109wc281s0_contain hAct


private theorem step109wc281s1_QtInv :
    (codeMat 98 : Mat3).transpose⁻¹ = (codeMat 140 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 98 : Mat3).transpose * (codeMat 140 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc281s1_contain :
    (o281SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 98) (codeMat 98) o149W_mono := by
  change spanCodes [256, 160, 16, 10, 1] ≤ actionW (codeMat 98) (codeMat 98) o149W_mono
  apply step109wc281_spanCodes_le_of_gens [256, 160, 16, 10, 1]
    (actionW (codeMat 98) (codeMat 98) o149W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 16 ∈ o149W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 98) (codeMat 98) (codeMat 16) = codeMat 256 := by
      unfold actionA
      rw [step109wc281s1_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 16 * (codeMat 140 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 10 ∈ o149W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 98) (codeMat 98) (codeMat 10) = codeMat 160 := by
      unfold actionA
      rw [step109wc281s1_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 10 * (codeMat 140 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ o149W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 98) (codeMat 98) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc281s1_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 1 * (codeMat 140 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 68 ∈ o149W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 16, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 98) (codeMat 98) (codeMat 68) = codeMat 10 := by
      unfold actionA
      rw [step109wc281s1_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 68 * (codeMat 140 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ o149W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 16, 10, 1] 256 (by decide)
    have hact : actionA (codeMat 98) (codeMat 98) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc281s1_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 256 * (codeMat 140 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact

theorem step109wc281s1Dispatch :
    QuotientRankAtLeast (o281SourceU_wc ⟨1, by omega⟩) 15 := by
  have hP : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 98) (codeMat 98) o149W_mono) 15 :=
    @quotientRankAtLeast_action (codeMat 98) (codeMat 98) hP hQ o149W_mono 15
      orbit149_lb15_mono
  exact quotientRankAtLeast_mono step109wc281s1_contain hAct


private theorem step109wc281s2_QtInv :
    (codeMat 226 : Mat3).transpose⁻¹ = (codeMat 141 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 226 : Mat3).transpose * (codeMat 141 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc281s2_contain :
    (o281SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 99) (codeMat 226) o149W_mono := by
  change spanCodes [256, 228, 16, 10, 1] ≤ actionW (codeMat 99) (codeMat 226) o149W_mono
  apply step109wc281_spanCodes_le_of_gens [256, 228, 16, 10, 1]
    (actionW (codeMat 99) (codeMat 226) o149W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 16 ∈ o149W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 99) (codeMat 226) (codeMat 16) = codeMat 256 := by
      unfold actionA
      rw [step109wc281s2_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 16 * (codeMat 141 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 10 ∈ o149W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 99) (codeMat 226) (codeMat 10) = codeMat 228 := by
      unfold actionA
      rw [step109wc281s2_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 10 * (codeMat 141 : Mat3).transpose = codeMat 228
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 325 ∈ o149W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 16, 10, 1] 325 (by decide)
    have hact : actionA (codeMat 99) (codeMat 226) (codeMat 325) = codeMat 16 := by
      unfold actionA
      rw [step109wc281s2_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 325 * (codeMat 141 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 68 ∈ o149W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 16, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 99) (codeMat 226) (codeMat 68) = codeMat 10 := by
      unfold actionA
      rw [step109wc281s2_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 68 * (codeMat 141 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ o149W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 16, 10, 1] 256 (by decide)
    have hact : actionA (codeMat 99) (codeMat 226) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc281s2_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 256 * (codeMat 141 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact

theorem step109wc281s2Dispatch :
    QuotientRankAtLeast (o281SourceU_wc ⟨2, by omega⟩) 15 := by
  have hP : Invertible (codeMat 99 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 226 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 99) (codeMat 226) o149W_mono) 15 :=
    @quotientRankAtLeast_action (codeMat 99) (codeMat 226) hP hQ o149W_mono 15
      orbit149_lb15_mono
  exact quotientRankAtLeast_mono step109wc281s2_contain hAct

private def step109wc281s3SrcT : Submodule F2 Mat3 := spanCodes [256, 132, 8, 2, 1]

private theorem step109wc281s3SrcT_lb : QuotientRankAtLeast step109wc281s3SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step109_orbit111_lb14_wc
  have hle : step109wc281s3SrcT ≤ transposeW o111W_wc := by
    unfold step109wc281s3SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4
    · subst h0
      show codeMat 256 ∈ Submodule.map transposeLinearMap o111W_wc
      exact ⟨codeMat 256, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 8, 2, 1] 256 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 132 ∈ Submodule.map transposeLinearMap o111W_wc
      exact ⟨codeMat 96, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 8, 2, 1] 96 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 8 ∈ Submodule.map transposeLinearMap o111W_wc
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 8, 2, 1] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 2 ∈ Submodule.map transposeLinearMap o111W_wc
      exact ⟨codeMat 8, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 8, 2, 1] 8 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 1 ∈ Submodule.map transposeLinearMap o111W_wc
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 8, 2, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc281s3_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc281s3_contain :
    (o281SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 98) (codeMat 84) step109wc281s3SrcT := by
  change spanCodes [256, 32, 16, 10, 1] ≤ actionW (codeMat 98) (codeMat 84) step109wc281s3SrcT
  apply step109wc281_spanCodes_le_of_gens [256, 32, 16, 10, 1]
    (actionW (codeMat 98) (codeMat 84) step109wc281s3SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 8 ∈ step109wc281s3SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 98) (codeMat 84) (codeMat 8) = codeMat 256 := by
      unfold actionA
      rw [step109wc281s3_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 8 * (codeMat 84 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ step109wc281s3SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 98) (codeMat 84) (codeMat 1) = codeMat 32 := by
      unfold actionA
      rw [step109wc281s3_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ step109wc281s3SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 98) (codeMat 84) (codeMat 2) = codeMat 16 := by
      unfold actionA
      rw [step109wc281s3_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 132 ∈ step109wc281s3SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 8, 2, 1] 132 (by decide)
    have hact : actionA (codeMat 98) (codeMat 84) (codeMat 132) = codeMat 10 := by
      unfold actionA
      rw [step109wc281s3_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 132 * (codeMat 84 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ step109wc281s3SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 98) (codeMat 84) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc281s3_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 256 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact

theorem step109wc281s3Dispatch :
    QuotientRankAtLeast (o281SourceU_wc ⟨3, by omega⟩) 14 := by
  have hP : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 98) (codeMat 84) step109wc281s3SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 98) (codeMat 84) hP hQ step109wc281s3SrcT 14
      step109wc281s3SrcT_lb
  exact quotientRankAtLeast_mono step109wc281s3_contain hAct


private theorem step109wc281s4_QtInv :
    (codeMat 98 : Mat3).transpose⁻¹ = (codeMat 140 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 98 : Mat3).transpose * (codeMat 140 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc281s4_contain :
    (o281SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 84) (codeMat 98) o111W_wc := by
  change spanCodes [256, 128, 16, 10, 1] ≤ actionW (codeMat 84) (codeMat 98) o111W_wc
  apply step109wc281_spanCodes_le_of_gens [256, 128, 16, 10, 1]
    (actionW (codeMat 84) (codeMat 98) o111W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 2 ∈ o111W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 98) (codeMat 2) = codeMat 256 := by
      unfold actionA
      rw [step109wc281s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 140 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ o111W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 98) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step109wc281s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 140 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ o111W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 98) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step109wc281s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 140 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 96 ∈ o111W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 8, 2, 1] 96 (by decide)
    have hact : actionA (codeMat 84) (codeMat 98) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step109wc281s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 96 * (codeMat 140 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ o111W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 98) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc281s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 140 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact

theorem step109wc281s4Dispatch :
    QuotientRankAtLeast (o281SourceU_wc ⟨4, by omega⟩) 14 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 98) o111W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 98) hP hQ o111W_wc 14
      step109_orbit111_lb14_wc
  exact quotientRankAtLeast_mono step109wc281s4_contain hAct


private theorem step109wc281s5_QtInv :
    (codeMat 169 : Mat3).transpose⁻¹ = (codeMat 225 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 169 : Mat3).transpose * (codeMat 225 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc281s5_contain :
    (o281SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 273) (codeMat 169) orbit11W := by
  change spanCodes [256, 66, 34, 16, 10, 4, 1] ≤ actionW (codeMat 273) (codeMat 169) orbit11W
  apply step109wc281_spanCodes_le_of_gens [256, 66, 34, 16, 10, 4, 1]
    (actionW (codeMat 273) (codeMat 169) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 273) (codeMat 169) (codeMat 128) = codeMat 256 := by
      unfold actionA
      rw [step109wc281s5_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 128 * (codeMat 225 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 196 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 196 (by decide)
    have hact : actionA (codeMat 273) (codeMat 169) (codeMat 196) = codeMat 66 := by
      unfold actionA
      rw [step109wc281s5_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 196 * (codeMat 225 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 20 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 169) (codeMat 20) = codeMat 34 := by
      unfold actionA
      rw [step109wc281s5_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * (codeMat 225 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 273) (codeMat 169) (codeMat 32) = codeMat 16 := by
      unfold actionA
      rw [step109wc281s5_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 32 * (codeMat 225 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 28 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 28 (by decide)
    have hact : actionA (codeMat 273) (codeMat 169) (codeMat 28) = codeMat 10 := by
      unfold actionA
      rw [step109wc281s5_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 28 * (codeMat 225 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 169) (codeMat 2) = codeMat 4 := by
      unfold actionA
      rw [step109wc281s5_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 225 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 3 (by decide)
    have hact : actionA (codeMat 273) (codeMat 169) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step109wc281s5_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 3 * (codeMat 225 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact

theorem step109wc281s5Dispatch :
    QuotientRankAtLeast (o281SourceU_wc ⟨5, by omega⟩) 12 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 169) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 169) hP hQ orbit11W 12
      orbit11_lb12
  exact quotientRankAtLeast_mono step109wc281s5_contain hAct


private theorem step109wc281s6_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = (codeMat 305 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * (codeMat 305 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc281s6_contain :
    (o281SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 141) (codeMat 305) orbit11W := by
  change spanCodes [256, 130, 64, 16, 10, 6, 1] ≤ actionW (codeMat 141) (codeMat 305) orbit11W
  apply step109wc281_spanCodes_le_of_gens [256, 130, 64, 16, 10, 6, 1]
    (actionW (codeMat 141) (codeMat 305) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 54 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 54 (by decide)
    have hact : actionA (codeMat 141) (codeMat 305) (codeMat 54) = codeMat 256 := by
      unfold actionA
      rw [step109wc281s6_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 54 * (codeMat 305 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 2 (by decide)
    have hact : actionA (codeMat 141) (codeMat 305) (codeMat 2) = codeMat 130 := by
      unfold actionA
      rw [step109wc281s6_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 2 * (codeMat 305 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 9 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 9 (by decide)
    have hact : actionA (codeMat 141) (codeMat 305) (codeMat 9) = codeMat 64 := by
      unfold actionA
      rw [step109wc281s6_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 9 * (codeMat 305 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 141) (codeMat 305) (codeMat 128) = codeMat 16 := by
      unfold actionA
      rw [step109wc281s6_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 128 * (codeMat 305 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 80 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 80 (by decide)
    have hact : actionA (codeMat 141) (codeMat 305) (codeMat 80) = codeMat 10 := by
      unfold actionA
      rw [step109wc281s6_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 80 * (codeMat 305 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 141) (codeMat 305) (codeMat 32) = codeMat 6 := by
      unfold actionA
      rw [step109wc281s6_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 32 * (codeMat 305 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 8 (by decide)
    have hact : actionA (codeMat 141) (codeMat 305) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc281s6_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 8 * (codeMat 305 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact

theorem step109wc281s6Dispatch :
    QuotientRankAtLeast (o281SourceU_wc ⟨6, by omega⟩) 12 := by
  have hP : Invertible (codeMat 141 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 141) (codeMat 305) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 141) (codeMat 305) hP hQ orbit11W 12
      orbit11_lb12
  exact quotientRankAtLeast_mono step109wc281s6_contain hAct


private theorem step109wc281s7_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = (codeMat 275 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * (codeMat 275 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc281s7_contain :
    (o281SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 266) (codeMat 275) orbit10W := by
  change spanCodes [256, 164, 96, 16, 8, 2, 1] ≤ actionW (codeMat 266) (codeMat 275) orbit10W
  apply step109wc281_spanCodes_le_of_gens [256, 164, 96, 16, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 275) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 266) (codeMat 275) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step109wc281s7_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 256 * (codeMat 275 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 228 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 228 (by decide)
    have hact : actionA (codeMat 266) (codeMat 275) (codeMat 228) = codeMat 164 := by
      unfold actionA
      rw [step109wc281s7_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 228 * (codeMat 275 : Mat3).transpose = codeMat 164
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 266) (codeMat 275) (codeMat 68) = codeMat 96 := by
      unfold actionA
      rw [step109wc281s7_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 68 * (codeMat 275 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 3 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 266) (codeMat 275) (codeMat 3) = codeMat 16 := by
      unfold actionA
      rw [step109wc281s7_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 3 * (codeMat 275 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 275) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step109wc281s7_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 275 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 266) (codeMat 275) (codeMat 24) = codeMat 2 := by
      unfold actionA
      rw [step109wc281s7_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 24 * (codeMat 275 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 275) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc281s7_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 275 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact

theorem step109wc281s7Dispatch :
    QuotientRankAtLeast (o281SourceU_wc ⟨7, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 275) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 275) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc281s7_contain hAct


private theorem step109wc281s8_QtInv :
    (codeMat 281 : Mat3).transpose⁻¹ = (codeMat 281 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 281 : Mat3).transpose * (codeMat 281 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc281s8_contain :
    (o281SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 266) (codeMat 281) orbit10W := by
  change spanCodes [256, 132, 100, 16, 8, 2, 1] ≤ actionW (codeMat 266) (codeMat 281) orbit10W
  apply step109wc281_spanCodes_le_of_gens [256, 132, 100, 16, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 281) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 266) (codeMat 281) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step109wc281s8_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 256 * (codeMat 281 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 266) (codeMat 281) (codeMat 160) = codeMat 132 := by
      unfold actionA
      rw [step109wc281s8_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 160 * (codeMat 281 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 228 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 228 (by decide)
    have hact : actionA (codeMat 266) (codeMat 281) (codeMat 228) = codeMat 100 := by
      unfold actionA
      rw [step109wc281s8_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 228 * (codeMat 281 : Mat3).transpose = codeMat 100
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 281) (codeMat 2) = codeMat 16 := by
      unfold actionA
      rw [step109wc281s8_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 281 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 266) (codeMat 281) (codeMat 3) = codeMat 8 := by
      unfold actionA
      rw [step109wc281s8_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 3 * (codeMat 281 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 281) (codeMat 16) = codeMat 2 := by
      unfold actionA
      rw [step109wc281s8_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 281 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 266) (codeMat 281) (codeMat 24) = codeMat 1 := by
      unfold actionA
      rw [step109wc281s8_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 24 * (codeMat 281 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact

theorem step109wc281s8Dispatch :
    QuotientRankAtLeast (o281SourceU_wc ⟨8, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 281) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 281) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc281s8_contain hAct


private theorem step109wc281s9_QtInv :
    (codeMat 244 : Mat3).transpose⁻¹ = (codeMat 95 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 244 : Mat3).transpose * (codeMat 95 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc281s9_contain :
    (o281SourceU_wc ⟨9, by omega⟩) ≤ actionW (codeMat 92) (codeMat 244) orbit10W := by
  change spanCodes [256, 134, 70, 36, 16, 10, 1] ≤ actionW (codeMat 92) (codeMat 244) orbit10W
  apply step109wc281_spanCodes_le_of_gens [256, 134, 70, 36, 16, 10, 1]
    (actionW (codeMat 92) (codeMat 244) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 3 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 92) (codeMat 244) (codeMat 3) = codeMat 256 := by
      unfold actionA
      rw [step109wc281s9_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 3 * (codeMat 95 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 326 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 326 (by decide)
    have hact : actionA (codeMat 92) (codeMat 244) (codeMat 326) = codeMat 134 := by
      unfold actionA
      rw [step109wc281s9_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 326 * (codeMat 95 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 324 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 324 (by decide)
    have hact : actionA (codeMat 92) (codeMat 244) (codeMat 324) = codeMat 70 := by
      unfold actionA
      rw [step109wc281s9_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 324 * (codeMat 95 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 92) (codeMat 244) (codeMat 24) = codeMat 36 := by
      unfold actionA
      rw [step109wc281s9_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 24 * (codeMat 95 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 432 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide)
    have hact : actionA (codeMat 92) (codeMat 244) (codeMat 432) = codeMat 16 := by
      unfold actionA
      rw [step109wc281s9_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 432 * (codeMat 95 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 92) (codeMat 244) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc281s9_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 160 * (codeMat 95 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 92) (codeMat 244) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc281s9_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 256 * (codeMat 95 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact

theorem step109wc281s9Dispatch :
    QuotientRankAtLeast (o281SourceU_wc ⟨9, by omega⟩) 12 := by
  have hP : Invertible (codeMat 92 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 244 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 92) (codeMat 244) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 92) (codeMat 244) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc281s9_contain hAct


private theorem step109wc281s10_QtInv :
    (codeMat 314 : Mat3).transpose⁻¹ = (codeMat 271 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 314 : Mat3).transpose * (codeMat 271 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc281s10_contain :
    (o281SourceU_wc ⟨10, by omega⟩) ≤ actionW (codeMat 95) (codeMat 314) orbit11W := by
  change spanCodes [256, 130, 66, 38, 16, 10, 1] ≤ actionW (codeMat 95) (codeMat 314) orbit11W
  apply step109wc281_spanCodes_le_of_gens [256, 130, 66, 38, 16, 10, 1]
    (actionW (codeMat 95) (codeMat 314) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 54 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 54 (by decide)
    have hact : actionA (codeMat 95) (codeMat 314) (codeMat 54) = codeMat 256 := by
      unfold actionA
      rw [step109wc281s10_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 54 * (codeMat 271 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 219 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 219 (by decide)
    have hact : actionA (codeMat 95) (codeMat 314) (codeMat 219) = codeMat 130 := by
      unfold actionA
      rw [step109wc281s10_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 219 * (codeMat 271 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 210 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 210 (by decide)
    have hact : actionA (codeMat 95) (codeMat 314) (codeMat 210) = codeMat 66 := by
      unfold actionA
      rw [step109wc281s10_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 210 * (codeMat 271 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 240 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 240 (by decide)
    have hact : actionA (codeMat 95) (codeMat 314) (codeMat 240) = codeMat 38 := by
      unfold actionA
      rw [step109wc281s10_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 240 * (codeMat 271 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 216 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 216 (by decide)
    have hact : actionA (codeMat 95) (codeMat 314) (codeMat 216) = codeMat 16 := by
      unfold actionA
      rw [step109wc281s10_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 216 * (codeMat 271 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 80 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 80 (by decide)
    have hact : actionA (codeMat 95) (codeMat 314) (codeMat 80) = codeMat 10 := by
      unfold actionA
      rw [step109wc281s10_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 80 * (codeMat 271 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 95) (codeMat 314) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc281s10_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 128 * (codeMat 271 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact

theorem step109wc281s10Dispatch :
    QuotientRankAtLeast (o281SourceU_wc ⟨10, by omega⟩) 12 := by
  have hP : Invertible (codeMat 95 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 314 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 95) (codeMat 314) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 95) (codeMat 314) hP hQ orbit11W 12
      orbit11_lb12
  exact quotientRankAtLeast_mono step109wc281s10_contain hAct


private theorem step109wc281s11_QtInv :
    (codeMat 116 : Mat3).transpose⁻¹ = (codeMat 92 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 116 : Mat3).transpose * (codeMat 92 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc281s11_contain :
    (o281SourceU_wc ⟨11, by omega⟩) ≤ actionW (codeMat 84) (codeMat 116) orbit10W := by
  change spanCodes [256, 128, 70, 32, 16, 10, 1] ≤ actionW (codeMat 84) (codeMat 116) orbit10W
  apply step109wc281_spanCodes_le_of_gens [256, 128, 70, 32, 16, 10, 1]
    (actionW (codeMat 84) (codeMat 116) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 3 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 84) (codeMat 116) (codeMat 3) = codeMat 256 := by
      unfold actionA
      rw [step109wc281s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 3 * (codeMat 92 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 116) (codeMat 2) = codeMat 128 := by
      unfold actionA
      rw [step109wc281s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 92 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 84) (codeMat 116) (codeMat 68) = codeMat 70 := by
      unfold actionA
      rw [step109wc281s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 68 * (codeMat 92 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 84) (codeMat 116) (codeMat 24) = codeMat 32 := by
      unfold actionA
      rw [step109wc281s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 24 * (codeMat 92 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 84) (codeMat 116) (codeMat 16) = codeMat 16 := by
      unfold actionA
      rw [step109wc281s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 16 * (codeMat 92 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 84) (codeMat 116) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc281s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 160 * (codeMat 92 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 116) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc281s11_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 92 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact

theorem step109wc281s11Dispatch :
    QuotientRankAtLeast (o281SourceU_wc ⟨11, by omega⟩) 12 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 116 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 116) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 116) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc281s11_contain hAct


private theorem step109wc281s12_QtInv :
    (codeMat 241 : Mat3).transpose⁻¹ = (codeMat 489 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 241 : Mat3).transpose * (codeMat 489 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc281s12_contain :
    (o281SourceU_wc ⟨12, by omega⟩) ≤ actionW (codeMat 267) (codeMat 241) orbit11W := by
  change spanCodes [256, 194, 34, 16, 10, 6, 1] ≤ actionW (codeMat 267) (codeMat 241) orbit11W
  apply step109wc281_spanCodes_le_of_gens [256, 194, 34, 16, 10, 6, 1]
    (actionW (codeMat 267) (codeMat 241) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 267) (codeMat 241) (codeMat 128) = codeMat 256 := by
      unfold actionA
      rw [step109wc281s12_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 128 * (codeMat 489 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 240 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 240 (by decide)
    have hact : actionA (codeMat 267) (codeMat 241) (codeMat 240) = codeMat 194 := by
      unfold actionA
      rw [step109wc281s12_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 240 * (codeMat 489 : Mat3).transpose = codeMat 194
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 34 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 34 (by decide)
    have hact : actionA (codeMat 267) (codeMat 241) (codeMat 34) = codeMat 34 := by
      unfold actionA
      rw [step109wc281s12_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 34 * (codeMat 489 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 54 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 54 (by decide)
    have hact : actionA (codeMat 267) (codeMat 241) (codeMat 54) = codeMat 16 := by
      unfold actionA
      rw [step109wc281s12_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 54 * (codeMat 489 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 29 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 29 (by decide)
    have hact : actionA (codeMat 267) (codeMat 241) (codeMat 29) = codeMat 10 := by
      unfold actionA
      rw [step109wc281s12_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 29 * (codeMat 489 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 267) (codeMat 241) (codeMat 32) = codeMat 6 := by
      unfold actionA
      rw [step109wc281s12_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 32 * (codeMat 489 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 40 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 40 (by decide)
    have hact : actionA (codeMat 267) (codeMat 241) (codeMat 40) = codeMat 1 := by
      unfold actionA
      rw [step109wc281s12_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 40 * (codeMat 489 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact

theorem step109wc281s12Dispatch :
    QuotientRankAtLeast (o281SourceU_wc ⟨12, by omega⟩) 12 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 241 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 241) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 241) hP hQ orbit11W 12
      orbit11_lb12
  exact quotientRankAtLeast_mono step109wc281s12_contain hAct


private theorem step109wc281s13_QtInv :
    (codeMat 172 : Mat3).transpose⁻¹ = (codeMat 99 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 172 : Mat3).transpose * (codeMat 99 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc281s13_contain :
    (o281SourceU_wc ⟨13, by omega⟩) ≤ actionW (codeMat 140) (codeMat 172) orbit10W := by
  change spanCodes [256, 162, 64, 16, 10, 4, 1] ≤ actionW (codeMat 140) (codeMat 172) orbit10W
  apply step109wc281_spanCodes_le_of_gens [256, 162, 64, 16, 10, 4, 1]
    (actionW (codeMat 140) (codeMat 172) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 3 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 140) (codeMat 172) (codeMat 3) = codeMat 256 := by
      unfold actionA
      rw [step109wc281s13_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 3 * (codeMat 99 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 228 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 228 (by decide)
    have hact : actionA (codeMat 140) (codeMat 172) (codeMat 228) = codeMat 162 := by
      unfold actionA
      rw [step109wc281s13_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 228 * (codeMat 99 : Mat3).transpose = codeMat 162
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 172) (codeMat 2) = codeMat 64 := by
      unfold actionA
      rw [step109wc281s13_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 99 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 140) (codeMat 172) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step109wc281s13_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 256 * (codeMat 99 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 140) (codeMat 172) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc281s13_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 160 * (codeMat 99 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 140) (codeMat 172) (codeMat 24) = codeMat 4 := by
      unfold actionA
      rw [step109wc281s13_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 24 * (codeMat 99 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 140) (codeMat 172) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc281s13_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 16 * (codeMat 99 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc281_codeMat_mem_actionW_of_witness hw hact

theorem step109wc281s13Dispatch :
    QuotientRankAtLeast (o281SourceU_wc ⟨13, by omega⟩) 12 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 172 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 172) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 172) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc281s13_contain hAct

theorem step109wc281_all_dispatch (i : Fin 14) :
    QuotientRankAtLeast (o281SourceU_wc i) (o281SourceLb_wc i) := by
  fin_cases i
  · exact step109wc281s0Dispatch
  · exact step109wc281s1Dispatch
  · exact step109wc281s2Dispatch
  · exact step109wc281s3Dispatch
  · exact step109wc281s4Dispatch
  · exact step109wc281s5Dispatch
  · exact step109wc281s6Dispatch
  · exact step109wc281s7Dispatch
  · exact step109wc281s8Dispatch
  · exact step109wc281s9Dispatch
  · exact step109wc281s10Dispatch
  · exact step109wc281s11Dispatch
  · exact step109wc281s12Dispatch
  · exact step109wc281s13Dispatch

theorem step109_orbit281_lb16_wc : QuotientRankAtLeast o281W_wc 16 :=
  o281Lb16_wc step109wc281_all_dispatch

end QiushiMatmul
