import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit178Consumer
import QiushiOrbit35FP
import QiushiWcOrbit72Dispatch
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit76Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit80Dispatch
import QiushiStep99Orbit55Dispatch
import QiushiStep99Orbit68Dispatch
import QiushiWcOrbit83Dispatch
import QiushiWcOrbit45Dispatch
import QiushiMonoOrbit49From10

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc178_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc178_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

private def step109wc178s0SrcT : Submodule F2 Mat3 := spanCodes [132, 80, 32, 8, 2, 1]

private theorem step109wc178s0SrcT_lb : QuotientRankAtLeast step109wc178s0SrcT 15 := by
  have ht := quotientRankAtLeast_transpose orbit35_lb15
  have hle : step109wc178s0SrcT ≤ transposeW orbit35W := by
    unfold step109wc178s0SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4 | h5
    · subst h0
      show codeMat 132 ∈ Submodule.map transposeLinearMap orbit35W
      exact ⟨codeMat 96, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 96 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 80 ∈ Submodule.map transposeLinearMap orbit35W
      exact ⟨codeMat 20, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 20 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 32 ∈ Submodule.map transposeLinearMap orbit35W
      exact ⟨codeMat 128, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 128 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 8 ∈ Submodule.map transposeLinearMap orbit35W
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 2 ∈ Submodule.map transposeLinearMap orbit35W
      exact ⟨codeMat 8, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h5
      show codeMat 1 ∈ Submodule.map transposeLinearMap orbit35W
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc178s0_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc178s0_contain :
    (o178SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 266) (codeMat 161) step109wc178s0SrcT := by
  change spanCodes [272, 68, 32, 8, 2, 1] ≤ actionW (codeMat 266) (codeMat 161) step109wc178s0SrcT
  apply step109wc178_spanCodes_le_of_gens [272, 68, 32, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 161) step109wc178s0SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 132 ∈ step109wc178s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 80, 32, 8, 2, 1] 132 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 132) = codeMat 272 := by
      unfold actionA
      rw [step109wc178s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 132 * (codeMat 161 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 80 ∈ step109wc178s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 80, 32, 8, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 80) = codeMat 68 := by
      unfold actionA
      rw [step109wc178s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 80 * (codeMat 161 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ step109wc178s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 80, 32, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [step109wc178s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ step109wc178s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 80, 32, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step109wc178s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ step109wc178s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 80, 32, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 32) = codeMat 2 := by
      unfold actionA
      rw [step109wc178s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 161 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ step109wc178s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 80, 32, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc178s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact

theorem step109wc178s0Dispatch :
    QuotientRankAtLeast (o178SourceU_wc ⟨0, by omega⟩) 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 161) step109wc178s0SrcT) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 161) hP hQ step109wc178s0SrcT 15
      step109wc178s0SrcT_lb
  exact quotientRankAtLeast_mono step109wc178s0_contain hAct


private theorem step109wc178s1_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc178s1_contain :
    (o178SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 273) (codeMat 140) orbit35W := by
  change spanCodes [272, 64, 32, 10, 4, 1] ≤ actionW (codeMat 273) (codeMat 140) orbit35W
  apply step109wc178_spanCodes_le_of_gens [272, 64, 32, 10, 4, 1]
    (actionW (codeMat 273) (codeMat 140) orbit35W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 96 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 96 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 96) = codeMat 272 := by
      unfold actionA
      rw [step109wc178s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 96 * (codeMat 98 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 128 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 128 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 128) = codeMat 64 := by
      unfold actionA
      rw [step109wc178s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 128 * (codeMat 98 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc178s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 20 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 20) = codeMat 10 := by
      unfold actionA
      rw [step109wc178s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * (codeMat 98 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step109wc178s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc178s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact

theorem step109wc178s1Dispatch :
    QuotientRankAtLeast (o178SourceU_wc ⟨1, by omega⟩) 15 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 140) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 140) hP hQ orbit35W 15
      orbit35_lb15
  exact quotientRankAtLeast_mono step109wc178s1_contain hAct


private theorem step109wc178s2_QtInv :
    (codeMat 212 : Mat3).transpose⁻¹ = (codeMat 86 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 212 : Mat3).transpose * (codeMat 86 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc178s2_contain :
    (o178SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 330) (codeMat 212) o72W_wc := by
  change spanCodes [262, 68, 32, 22, 10, 1] ≤ actionW (codeMat 330) (codeMat 212) o72W_wc
  apply step109wc178_spanCodes_le_of_gens [262, 68, 32, 22, 10, 1]
    (actionW (codeMat 330) (codeMat 212) o72W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 112 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 112 (by decide)
    have hact : actionA (codeMat 330) (codeMat 212) (codeMat 112) = codeMat 262 := by
      unfold actionA
      rw [step109wc178s2_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 112 * (codeMat 86 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 296 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 296 (by decide)
    have hact : actionA (codeMat 330) (codeMat 212) (codeMat 296) = codeMat 68 := by
      unfold actionA
      rw [step109wc178s2_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 296 * (codeMat 86 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 330) (codeMat 212) (codeMat 1) = codeMat 32 := by
      unfold actionA
      rw [step109wc178s2_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 1 * (codeMat 86 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 62 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 62 (by decide)
    have hact : actionA (codeMat 330) (codeMat 212) (codeMat 62) = codeMat 22 := by
      unfold actionA
      rw [step109wc178s2_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 62 * (codeMat 86 : Mat3).transpose = codeMat 22
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 52 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 52 (by decide)
    have hact : actionA (codeMat 330) (codeMat 212) (codeMat 52) = codeMat 10 := by
      unfold actionA
      rw [step109wc178s2_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 52 * (codeMat 86 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o72W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 20, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 330) (codeMat 212) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc178s2_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 32 * (codeMat 86 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact

theorem step109wc178s2Dispatch :
    QuotientRankAtLeast (o178SourceU_wc ⟨2, by omega⟩) 15 := by
  have hP : Invertible (codeMat 330 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 212 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 330) (codeMat 212) o72W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 330) (codeMat 212) hP hQ o72W_wc 15
      step109_orbit72_lb15_wc
  exact quotientRankAtLeast_mono step109wc178s2_contain hAct


private theorem step109wc178s3_QtInv :
    (codeMat 396 : Mat3).transpose⁻¹ = (codeMat 106 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 396 : Mat3).transpose * (codeMat 106 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc178s3_contain :
    (o178SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 142) (codeMat 396) o65W := by
  change spanCodes [272, 128, 68, 32, 10, 1] ≤ actionW (codeMat 142) (codeMat 396) o65W
  apply step109wc178_spanCodes_le_of_gens [272, 128, 68, 32, 10, 1]
    (actionW (codeMat 142) (codeMat 396) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 69 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 69) = codeMat 272 := by
      unfold actionA
      rw [step109wc178s3_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 69 * (codeMat 106 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 260 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 260) = codeMat 128 := by
      unfold actionA
      rw [step109wc178s3_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 260 * (codeMat 106 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 170 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 170 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 170) = codeMat 68 := by
      unfold actionA
      rw [step109wc178s3_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 170 * (codeMat 106 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 320 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 320 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 320) = codeMat 32 := by
      unfold actionA
      rw [step109wc178s3_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 320 * (codeMat 106 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc178s3_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 160 * (codeMat 106 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 142) (codeMat 396) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc178s3_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 16 * (codeMat 106 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact

theorem step109wc178s3Dispatch :
    QuotientRankAtLeast (o178SourceU_wc ⟨3, by omega⟩) 15 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 396 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 396) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 396) hP hQ o65W 15
      step99_orbit65_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc178s3_contain hAct


private theorem step109wc178s4_QtInv :
    (codeMat 401 : Mat3).transpose⁻¹ = (codeMat 401 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 401 : Mat3).transpose * (codeMat 401 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc178s4_contain :
    (o178SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 377) (codeMat 401) o76W := by
  change spanCodes [272, 130, 68, 32, 10, 1] ≤ actionW (codeMat 377) (codeMat 401) o76W
  apply step109wc178_spanCodes_le_of_gens [272, 130, 68, 32, 10, 1]
    (actionW (codeMat 377) (codeMat 401) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 180 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 180 (by decide)
    have hact : actionA (codeMat 377) (codeMat 401) (codeMat 180) = codeMat 272 := by
      unfold actionA
      rw [step109wc178s4_QtInv]
      show (codeMat 377 : Mat3).transpose * codeMat 180 * (codeMat 401 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 384 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 384 (by decide)
    have hact : actionA (codeMat 377) (codeMat 401) (codeMat 384) = codeMat 130 := by
      unfold actionA
      rw [step109wc178s4_QtInv]
      show (codeMat 377 : Mat3).transpose * codeMat 384 * (codeMat 401 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 69 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 377) (codeMat 401) (codeMat 69) = codeMat 68 := by
      unfold actionA
      rw [step109wc178s4_QtInv]
      show (codeMat 377 : Mat3).transpose * codeMat 69 * (codeMat 401 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 288 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 377) (codeMat 401) (codeMat 288) = codeMat 32 := by
      unfold actionA
      rw [step109wc178s4_QtInv]
      show (codeMat 377 : Mat3).transpose * codeMat 288 * (codeMat 401 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 78 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 377) (codeMat 401) (codeMat 78) = codeMat 10 := by
      unfold actionA
      rw [step109wc178s4_QtInv]
      show (codeMat 377 : Mat3).transpose * codeMat 78 * (codeMat 401 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 377) (codeMat 401) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc178s4_QtInv]
      show (codeMat 377 : Mat3).transpose * codeMat 1 * (codeMat 401 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact

theorem step109wc178s4Dispatch :
    QuotientRankAtLeast (o178SourceU_wc ⟨4, by omega⟩) 15 := by
  have hP : Invertible (codeMat 377 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 377) (codeMat 401) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 377) (codeMat 401) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc178s4_contain hAct


private theorem step109wc178s5_QtInv :
    (codeMat 419 : Mat3).transpose⁻¹ = (codeMat 183 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 419 : Mat3).transpose * (codeMat 183 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc178s5_contain :
    (o178SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 177) (codeMat 419) o76W := by
  change spanCodes [272, 132, 68, 32, 10, 1] ≤ actionW (codeMat 177) (codeMat 419) o76W
  apply step109wc178_spanCodes_le_of_gens [272, 132, 68, 32, 10, 1]
    (actionW (codeMat 177) (codeMat 419) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 240 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 240 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 240) = codeMat 272 := by
      unfold actionA
      rw [step109wc178s5_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 240 * (codeMat 183 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 366 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 366 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 366) = codeMat 132 := by
      unfold actionA
      rw [step109wc178s5_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 366 * (codeMat 183 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 78 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 78) = codeMat 68 := by
      unfold actionA
      rw [step109wc178s5_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 78 * (codeMat 183 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 384 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 384 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 384) = codeMat 32 := by
      unfold actionA
      rw [step109wc178s5_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 384 * (codeMat 183 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 69 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 69) = codeMat 10 := by
      unfold actionA
      rw [step109wc178s5_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 69 * (codeMat 183 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc178s5_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * (codeMat 183 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact

theorem step109wc178s5Dispatch :
    QuotientRankAtLeast (o178SourceU_wc ⟨5, by omega⟩) 15 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 419 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 419) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 419) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc178s5_contain hAct


private theorem step109wc178s6_QtInv :
    (codeMat 98 : Mat3).transpose⁻¹ = (codeMat 140 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 98 : Mat3).transpose * (codeMat 140 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc178s6_contain :
    (o178SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 86) (codeMat 98) o69W := by
  change spanCodes [272, 144, 68, 32, 10, 1] ≤ actionW (codeMat 86) (codeMat 98) o69W
  apply step109wc178_spanCodes_le_of_gens [272, 144, 68, 32, 10, 1]
    (actionW (codeMat 86) (codeMat 98) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 26 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 26 (by decide)
    have hact : actionA (codeMat 86) (codeMat 98) (codeMat 26) = codeMat 272 := by
      unfold actionA
      rw [step109wc178s6_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 26 * (codeMat 140 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 86) (codeMat 98) (codeMat 1) = codeMat 144 := by
      unfold actionA
      rw [step109wc178s6_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 1 * (codeMat 140 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 164 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 164 (by decide)
    have hact : actionA (codeMat 86) (codeMat 98) (codeMat 164) = codeMat 68 := by
      unfold actionA
      rw [step109wc178s6_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 164 * (codeMat 140 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 86) (codeMat 98) (codeMat 16) = codeMat 32 := by
      unfold actionA
      rw [step109wc178s6_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 16 * (codeMat 140 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 96 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 96 (by decide)
    have hact : actionA (codeMat 86) (codeMat 98) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step109wc178s6_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 96 * (codeMat 140 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 256 (by decide)
    have hact : actionA (codeMat 86) (codeMat 98) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc178s6_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 256 * (codeMat 140 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact

theorem step109wc178s6Dispatch :
    QuotientRankAtLeast (o178SourceU_wc ⟨6, by omega⟩) 15 := by
  have hP : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 86) (codeMat 98) o69W) 15 :=
    @quotientRankAtLeast_action (codeMat 86) (codeMat 98) hP hQ o69W 15
      step99_orbit69_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc178s6_contain hAct


private theorem step109wc178s7_QtInv :
    (codeMat 236 : Mat3).transpose⁻¹ = (codeMat 123 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 236 : Mat3).transpose * (codeMat 123 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc178s7_contain :
    (o178SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 157) (codeMat 236) o80W_wc := by
  change spanCodes [272, 146, 68, 32, 10, 1] ≤ actionW (codeMat 157) (codeMat 236) o80W_wc
  apply step109wc178_spanCodes_le_of_gens [272, 146, 68, 32, 10, 1]
    (actionW (codeMat 157) (codeMat 236) o80W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 475 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 475 (by decide)
    have hact : actionA (codeMat 157) (codeMat 236) (codeMat 475) = codeMat 272 := by
      unfold actionA
      rw [step109wc178s7_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 475 * (codeMat 123 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 260 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 157) (codeMat 236) (codeMat 260) = codeMat 146 := by
      unfold actionA
      rw [step109wc178s7_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 260 * (codeMat 123 : Mat3).transpose = codeMat 146
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 366 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 366 (by decide)
    have hact : actionA (codeMat 157) (codeMat 236) (codeMat 366) = codeMat 68 := by
      unfold actionA
      rw [step109wc178s7_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 366 * (codeMat 123 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 192 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 192 (by decide)
    have hact : actionA (codeMat 157) (codeMat 236) (codeMat 192) = codeMat 32 := by
      unfold actionA
      rw [step109wc178s7_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 192 * (codeMat 123 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 157) (codeMat 236) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc178s7_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 160 * (codeMat 123 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 432 ∈ o80W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 96, 20, 10, 1] 432 (by decide)
    have hact : actionA (codeMat 157) (codeMat 236) (codeMat 432) = codeMat 1 := by
      unfold actionA
      rw [step109wc178s7_QtInv]
      show (codeMat 157 : Mat3).transpose * codeMat 432 * (codeMat 123 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact

theorem step109wc178s7Dispatch :
    QuotientRankAtLeast (o178SourceU_wc ⟨7, by omega⟩) 15 := by
  have hP : Invertible (codeMat 157 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 236 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 157) (codeMat 236) o80W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 157) (codeMat 236) hP hQ o80W_wc 15
      step109_orbit80_lb15_wc
  exact quotientRankAtLeast_mono step109wc178s7_contain hAct

private def step109wc178s8SrcT : Submodule F2 Mat3 := spanCodes [272, 132, 80, 36, 10, 1]

private theorem step109wc178s8SrcT_lb : QuotientRankAtLeast step109wc178s8SrcT 15 := by
  have ht := quotientRankAtLeast_transpose step109_orbit80_lb15_wc
  have hle : step109wc178s8SrcT ≤ transposeW o80W_wc := by
    unfold step109wc178s8SrcT transposeW
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

private theorem step109wc178s8_QtInv :
    (codeMat 348 : Mat3).transpose⁻¹ = (codeMat 125 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 348 : Mat3).transpose * (codeMat 125 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc178s8_contain :
    (o178SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 156) (codeMat 348) step109wc178s8SrcT := by
  change spanCodes [272, 148, 68, 32, 10, 1] ≤ actionW (codeMat 156) (codeMat 348) step109wc178s8SrcT
  apply step109wc178_spanCodes_le_of_gens [272, 148, 68, 32, 10, 1]
    (actionW (codeMat 156) (codeMat 348) step109wc178s8SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 133 ∈ step109wc178s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 36, 10, 1] 133 (by decide)
    have hact : actionA (codeMat 156) (codeMat 348) (codeMat 133) = codeMat 272 := by
      unfold actionA
      rw [step109wc178s8_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 133 * (codeMat 125 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 490 ∈ step109wc178s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 36, 10, 1] 490 (by decide)
    have hact : actionA (codeMat 156) (codeMat 348) (codeMat 490) = codeMat 148 := by
      unfold actionA
      rw [step109wc178s8_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 490 * (codeMat 125 : Mat3).transpose = codeMat 148
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 366 ∈ step109wc178s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 36, 10, 1] 366 (by decide)
    have hact : actionA (codeMat 156) (codeMat 348) (codeMat 366) = codeMat 68 := by
      unfold actionA
      rw [step109wc178s8_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 366 * (codeMat 125 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 320 ∈ step109wc178s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 36, 10, 1] 320 (by decide)
    have hact : actionA (codeMat 156) (codeMat 348) (codeMat 320) = codeMat 32 := by
      unfold actionA
      rw [step109wc178s8_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 320 * (codeMat 125 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 272 ∈ step109wc178s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 36, 10, 1] 272 (by decide)
    have hact : actionA (codeMat 156) (codeMat 348) (codeMat 272) = codeMat 10 := by
      unfold actionA
      rw [step109wc178s8_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 272 * (codeMat 125 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 432 ∈ step109wc178s8SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 36, 10, 1] 432 (by decide)
    have hact : actionA (codeMat 156) (codeMat 348) (codeMat 432) = codeMat 1 := by
      unfold actionA
      rw [step109wc178s8_QtInv]
      show (codeMat 156 : Mat3).transpose * codeMat 432 * (codeMat 125 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact

theorem step109wc178s8Dispatch :
    QuotientRankAtLeast (o178SourceU_wc ⟨8, by omega⟩) 15 := by
  have hP : Invertible (codeMat 156 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 348 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 156) (codeMat 348) step109wc178s8SrcT) 15 :=
    @quotientRankAtLeast_action (codeMat 156) (codeMat 348) hP hQ step109wc178s8SrcT 15
      step109wc178s8SrcT_lb
  exact quotientRankAtLeast_mono step109wc178s8_contain hAct


private theorem step109wc178s9_QtInv :
    (codeMat 226 : Mat3).transpose⁻¹ = (codeMat 141 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 226 : Mat3).transpose * (codeMat 141 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc178s9_contain :
    (o178SourceU_wc ⟨9, by omega⟩) ≤ actionW (codeMat 266) (codeMat 226) o55W := by
  change spanCodes [258, 68, 32, 18, 10, 1] ≤ actionW (codeMat 266) (codeMat 226) o55W
  apply step109wc178_spanCodes_le_of_gens [258, 68, 32, 18, 10, 1]
    (actionW (codeMat 266) (codeMat 226) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 168 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 168 (by decide)
    have hact : actionA (codeMat 266) (codeMat 226) (codeMat 168) = codeMat 258 := by
      unfold actionA
      rw [step109wc178s9_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 168 * (codeMat 141 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 272 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 272 (by decide)
    have hact : actionA (codeMat 266) (codeMat 226) (codeMat 272) = codeMat 68 := by
      unfold actionA
      rw [step109wc178s9_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 272 * (codeMat 141 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 226) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [step109wc178s9_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 141 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 45 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 45 (by decide)
    have hact : actionA (codeMat 266) (codeMat 226) (codeMat 45) = codeMat 18 := by
      unfold actionA
      rw [step109wc178s9_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 45 * (codeMat 141 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 44 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 44 (by decide)
    have hact : actionA (codeMat 266) (codeMat 226) (codeMat 44) = codeMat 10 := by
      unfold actionA
      rw [step109wc178s9_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 44 * (codeMat 141 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 226) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc178s9_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 141 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact

theorem step109wc178s9Dispatch :
    QuotientRankAtLeast (o178SourceU_wc ⟨9, by omega⟩) 14 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 226 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 226) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 226) hP hQ o55W 14
      step99_orbit55_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc178s9_contain hAct

private def step109wc178s10SrcT : Submodule F2 Mat3 := spanCodes [272, 128, 66, 34, 8, 1]

private theorem step109wc178s10SrcT_lb : QuotientRankAtLeast step109wc178s10SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step99_orbit55_lb14_unconditional
  have hle : step109wc178s10SrcT ≤ transposeW o55W := by
    unfold step109wc178s10SrcT transposeW
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

private theorem step109wc178s10_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc178s10_contain :
    (o178SourceU_wc ⟨10, by omega⟩) ≤ actionW (codeMat 85) (codeMat 140) step109wc178s10SrcT := by
  change spanCodes [260, 68, 32, 20, 10, 1] ≤ actionW (codeMat 85) (codeMat 140) step109wc178s10SrcT
  apply step109wc178_spanCodes_le_of_gens [260, 68, 32, 20, 10, 1]
    (actionW (codeMat 85) (codeMat 140) step109wc178s10SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 1 ∈ step109wc178s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 1 (by decide)
    have hact : actionA (codeMat 85) (codeMat 140) (codeMat 1) = codeMat 260 := by
      unfold actionA
      rw [step109wc178s10_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 194 ∈ step109wc178s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 194 (by decide)
    have hact : actionA (codeMat 85) (codeMat 140) (codeMat 194) = codeMat 68 := by
      unfold actionA
      rw [step109wc178s10_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 194 * (codeMat 98 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ step109wc178s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 8 (by decide)
    have hact : actionA (codeMat 85) (codeMat 140) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc178s10_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 96 ∈ step109wc178s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 96 (by decide)
    have hact : actionA (codeMat 85) (codeMat 140) (codeMat 96) = codeMat 20 := by
      unfold actionA
      rw [step109wc178s10_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 96 * (codeMat 98 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 272 ∈ step109wc178s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 272 (by decide)
    have hact : actionA (codeMat 85) (codeMat 140) (codeMat 272) = codeMat 10 := by
      unfold actionA
      rw [step109wc178s10_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 272 * (codeMat 98 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ step109wc178s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 128 (by decide)
    have hact : actionA (codeMat 85) (codeMat 140) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc178s10_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 128 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact

theorem step109wc178s10Dispatch :
    QuotientRankAtLeast (o178SourceU_wc ⟨10, by omega⟩) 14 := by
  have hP : Invertible (codeMat 85 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 85) (codeMat 140) step109wc178s10SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 85) (codeMat 140) hP hQ step109wc178s10SrcT 14
      step109wc178s10SrcT_lb
  exact quotientRankAtLeast_mono step109wc178s10_contain hAct


private theorem step109wc178s11_QtInv :
    (codeMat 423 : Mat3).transpose⁻¹ = (codeMat 181 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 423 : Mat3).transpose * (codeMat 181 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc178s11_contain :
    (o178SourceU_wc ⟨11, by omega⟩) ≤ actionW (codeMat 185) (codeMat 423) o68W := by
  change spanCodes [272, 134, 68, 32, 10, 1] ≤ actionW (codeMat 185) (codeMat 423) o68W
  apply step109wc178_spanCodes_le_of_gens [272, 134, 68, 32, 10, 1]
    (actionW (codeMat 185) (codeMat 423) o68W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 191 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 191 (by decide)
    have hact : actionA (codeMat 185) (codeMat 423) (codeMat 191) = codeMat 272 := by
      unfold actionA
      rw [step109wc178s11_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 191 * (codeMat 181 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 367 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 367 (by decide)
    have hact : actionA (codeMat 185) (codeMat 423) (codeMat 367) = codeMat 134 := by
      unfold actionA
      rw [step109wc178s11_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 367 * (codeMat 181 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 78 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 185) (codeMat 423) (codeMat 78) = codeMat 68 := by
      unfold actionA
      rw [step109wc178s11_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 78 * (codeMat 181 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 448 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 448 (by decide)
    have hact : actionA (codeMat 185) (codeMat 423) (codeMat 448) = codeMat 32 := by
      unfold actionA
      rw [step109wc178s11_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 448 * (codeMat 181 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 69 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 185) (codeMat 423) (codeMat 69) = codeMat 10 := by
      unfold actionA
      rw [step109wc178s11_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 69 * (codeMat 181 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 185) (codeMat 423) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc178s11_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 1 * (codeMat 181 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact

theorem step109wc178s11Dispatch :
    QuotientRankAtLeast (o178SourceU_wc ⟨11, by omega⟩) 14 := by
  have hP : Invertible (codeMat 185 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 423 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 185) (codeMat 423) o68W) 14 :=
    @quotientRankAtLeast_action (codeMat 185) (codeMat 423) hP hQ o68W 14
      step99_orbit68_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc178s11_contain hAct


private theorem step109wc178s12_QtInv :
    (codeMat 423 : Mat3).transpose⁻¹ = (codeMat 181 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 423 : Mat3).transpose * (codeMat 181 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc178s12_contain :
    (o178SourceU_wc ⟨12, by omega⟩) ≤ actionW (codeMat 241) (codeMat 423) o83W_wc := by
  change spanCodes [272, 150, 68, 32, 10, 1] ≤ actionW (codeMat 241) (codeMat 423) o83W_wc
  apply step109wc178_spanCodes_le_of_gens [272, 150, 68, 32, 10, 1]
    (actionW (codeMat 241) (codeMat 423) o83W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 186 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 186 (by decide)
    have hact : actionA (codeMat 241) (codeMat 423) (codeMat 186) = codeMat 272 := by
      unfold actionA
      rw [step109wc178s12_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 186 * (codeMat 181 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 42 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 42 (by decide)
    have hact : actionA (codeMat 241) (codeMat 423) (codeMat 42) = codeMat 150 := by
      unfold actionA
      rw [step109wc178s12_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 42 * (codeMat 181 : Mat3).transpose = codeMat 150
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 78 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 241) (codeMat 423) (codeMat 78) = codeMat 68 := by
      unfold actionA
      rw [step109wc178s12_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 78 * (codeMat 181 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 455 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 455 (by decide)
    have hact : actionA (codeMat 241) (codeMat 423) (codeMat 455) = codeMat 32 := by
      unfold actionA
      rw [step109wc178s12_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 455 * (codeMat 181 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 68 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 241) (codeMat 423) (codeMat 68) = codeMat 10 := by
      unfold actionA
      rw [step109wc178s12_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 68 * (codeMat 181 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o83W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 241) (codeMat 423) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc178s12_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 1 * (codeMat 181 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact

theorem step109wc178s12Dispatch :
    QuotientRankAtLeast (o178SourceU_wc ⟨12, by omega⟩) 14 := by
  have hP : Invertible (codeMat 241 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 423 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 241) (codeMat 423) o83W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 241) (codeMat 423) hP hQ o83W_wc 14
      step109_orbit83_lb14_wc
  exact quotientRankAtLeast_mono step109wc178s12_contain hAct


private theorem step109wc178s13_QtInv :
    (codeMat 401 : Mat3).transpose⁻¹ = (codeMat 401 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 401 : Mat3).transpose * (codeMat 401 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc178s13_contain :
    (o178SourceU_wc ⟨13, by omega⟩) ≤ actionW (codeMat 177) (codeMat 401) o45W_wc := by
  change spanCodes [272, 66, 32, 10, 6, 1] ≤ actionW (codeMat 177) (codeMat 401) o45W_wc
  apply step109wc178_spanCodes_le_of_gens [272, 66, 32, 10, 6, 1]
    (actionW (codeMat 177) (codeMat 401) o45W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 160 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 177) (codeMat 401) (codeMat 160) = codeMat 272 := by
      unfold actionA
      rw [step109wc178s13_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 160 * (codeMat 401 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 78 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 78 (by decide)
    have hact : actionA (codeMat 177) (codeMat 401) (codeMat 78) = codeMat 66 := by
      unfold actionA
      rw [step109wc178s13_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 78 * (codeMat 401 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 256 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 177) (codeMat 401) (codeMat 256) = codeMat 32 := by
      unfold actionA
      rw [step109wc178s13_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 256 * (codeMat 401 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 70 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 70 (by decide)
    have hact : actionA (codeMat 177) (codeMat 401) (codeMat 70) = codeMat 10 := by
      unfold actionA
      rw [step109wc178s13_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 70 * (codeMat 401 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 177) (codeMat 401) (codeMat 2) = codeMat 6 := by
      unfold actionA
      rw [step109wc178s13_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 2 * (codeMat 401 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o45W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 401) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc178s13_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * (codeMat 401 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact

theorem step109wc178s13Dispatch :
    QuotientRankAtLeast (o178SourceU_wc ⟨13, by omega⟩) 13 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 401) o45W_wc) 13 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 401) hP hQ o45W_wc 13
      step109_orbit45_lb13_wc
  exact quotientRankAtLeast_mono step109wc178s13_contain hAct


private theorem step109wc178s14_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc178s14_contain :
    (o178SourceU_wc ⟨14, by omega⟩) ≤ actionW (codeMat 98) (codeMat 84) o49W_mono := by
  change spanCodes [256, 68, 32, 16, 10, 1] ≤ actionW (codeMat 98) (codeMat 84) o49W_mono
  apply step109wc178_spanCodes_le_of_gens [256, 68, 32, 16, 10, 1]
    (actionW (codeMat 98) (codeMat 84) o49W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 8 ∈ o49W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 96, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 98) (codeMat 84) (codeMat 8) = codeMat 256 := by
      unfold actionA
      rw [step109wc178s14_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 8 * (codeMat 84 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 96 ∈ o49W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 96, 8, 2, 1] 96 (by decide)
    have hact : actionA (codeMat 98) (codeMat 84) (codeMat 96) = codeMat 68 := by
      unfold actionA
      rw [step109wc178s14_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 96 * (codeMat 84 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ o49W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 96, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 98) (codeMat 84) (codeMat 1) = codeMat 32 := by
      unfold actionA
      rw [step109wc178s14_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o49W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 96, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 98) (codeMat 84) (codeMat 2) = codeMat 16 := by
      unfold actionA
      rw [step109wc178s14_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 132 ∈ o49W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 96, 8, 2, 1] 132 (by decide)
    have hact : actionA (codeMat 98) (codeMat 84) (codeMat 132) = codeMat 10 := by
      unfold actionA
      rw [step109wc178s14_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 132 * (codeMat 84 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ o49W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 96, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 98) (codeMat 84) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc178s14_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 256 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc178_codeMat_mem_actionW_of_witness hw hact

theorem step109wc178s14Dispatch :
    QuotientRankAtLeast (o178SourceU_wc ⟨14, by omega⟩) 12 := by
  have hP : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 98) (codeMat 84) o49W_mono) 12 :=
    @quotientRankAtLeast_action (codeMat 98) (codeMat 84) hP hQ o49W_mono 12
      orbit49_lb12_mono
  exact quotientRankAtLeast_mono step109wc178s14_contain hAct

theorem step109wc178_all_dispatch (i : Fin 15) :
    QuotientRankAtLeast (o178SourceU_wc i) (o178SourceLb_wc i) := by
  fin_cases i
  · exact step109wc178s0Dispatch
  · exact step109wc178s1Dispatch
  · exact step109wc178s2Dispatch
  · exact step109wc178s3Dispatch
  · exact step109wc178s4Dispatch
  · exact step109wc178s5Dispatch
  · exact step109wc178s6Dispatch
  · exact step109wc178s7Dispatch
  · exact step109wc178s8Dispatch
  · exact step109wc178s9Dispatch
  · exact step109wc178s10Dispatch
  · exact step109wc178s11Dispatch
  · exact step109wc178s12Dispatch
  · exact step109wc178s13Dispatch
  · exact step109wc178s14Dispatch

theorem step109_orbit178_lb16_wc : QuotientRankAtLeast o178W_wc 16 :=
  o178Lb16_wc step109wc178_all_dispatch

end QiushiMatmul
