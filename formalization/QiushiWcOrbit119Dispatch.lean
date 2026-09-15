import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit119Consumer
import QiushiStep99Mono3032
import QiushiMonoOrbit43From14
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiMonoOrbit19From5

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc119_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc119_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

private def step109wc119s0SrcT : Submodule F2 Mat3 := spanCodes [128, 80, 32, 8, 2, 1]

private theorem step109wc119s0SrcT_lb : QuotientRankAtLeast step109wc119s0SrcT 12 := by
  have ht := quotientRankAtLeast_transpose step99_mono_32_lb12
  have hle : step109wc119s0SrcT ≤ transposeW monoW_32 := by
    unfold step109wc119s0SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4 | h5
    · subst h0
      show codeMat 128 ∈ Submodule.map transposeLinearMap monoW_32
      exact ⟨codeMat 32, spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 32 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 80 ∈ Submodule.map transposeLinearMap monoW_32
      exact ⟨codeMat 20, spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 20 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 32 ∈ Submodule.map transposeLinearMap monoW_32
      exact ⟨codeMat 128, spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 128 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 8 ∈ Submodule.map transposeLinearMap monoW_32
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 2 ∈ Submodule.map transposeLinearMap monoW_32
      exact ⟨codeMat 8, spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 8 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h5
      show codeMat 1 ∈ Submodule.map transposeLinearMap monoW_32
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc119s0_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc119s0_contain :
    (o119SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 140) (codeMat 161) step109wc119s0SrcT := by
  change spanCodes [256, 64, 32, 12, 2, 1] ≤ actionW (codeMat 140) (codeMat 161) step109wc119s0SrcT
  apply step109wc119_spanCodes_le_of_gens [256, 64, 32, 12, 2, 1]
    (actionW (codeMat 140) (codeMat 161) step109wc119s0SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 2 ∈ step109wc119s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 80, 32, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 2) = codeMat 256 := by
      unfold actionA
      rw [step109wc119s0_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ step109wc119s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 80, 32, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 1) = codeMat 64 := by
      unfold actionA
      rw [step109wc119s0_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 128 ∈ step109wc119s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 80, 32, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 128) = codeMat 32 := by
      unfold actionA
      rw [step109wc119s0_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 128 * (codeMat 161 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 80 ∈ step109wc119s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 80, 32, 8, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 80) = codeMat 12 := by
      unfold actionA
      rw [step109wc119s0_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 80 * (codeMat 161 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ step109wc119s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 80, 32, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 32) = codeMat 2 := by
      unfold actionA
      rw [step109wc119s0_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 32 * (codeMat 161 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ step109wc119s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 80, 32, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc119s0_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact

theorem step109wc119s0Dispatch :
    QuotientRankAtLeast (o119SourceU_wc ⟨0, by omega⟩) 12 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 161) step109wc119s0SrcT) 12 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 161) hP hQ step109wc119s0SrcT 12
      step109wc119s0SrcT_lb
  exact quotientRankAtLeast_mono step109wc119s0_contain hAct

private def step109wc119s1SrcT : Submodule F2 Mat3 := spanCodes [128, 80, 32, 8, 2, 1]

private theorem step109wc119s1SrcT_lb : QuotientRankAtLeast step109wc119s1SrcT 12 := by
  have ht := quotientRankAtLeast_transpose step99_mono_32_lb12
  have hle : step109wc119s1SrcT ≤ transposeW monoW_32 := by
    unfold step109wc119s1SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4 | h5
    · subst h0
      show codeMat 128 ∈ Submodule.map transposeLinearMap monoW_32
      exact ⟨codeMat 32, spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 32 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 80 ∈ Submodule.map transposeLinearMap monoW_32
      exact ⟨codeMat 20, spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 20 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 32 ∈ Submodule.map transposeLinearMap monoW_32
      exact ⟨codeMat 128, spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 128 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 8 ∈ Submodule.map transposeLinearMap monoW_32
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 2 ∈ Submodule.map transposeLinearMap monoW_32
      exact ⟨codeMat 8, spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 8 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h5
      show codeMat 1 ∈ Submodule.map transposeLinearMap monoW_32
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc119s1_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc119s1_contain :
    (o119SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 142) (codeMat 161) step109wc119s1SrcT := by
  change spanCodes [256, 68, 32, 12, 2, 1] ≤ actionW (codeMat 142) (codeMat 161) step109wc119s1SrcT
  apply step109wc119_spanCodes_le_of_gens [256, 68, 32, 12, 2, 1]
    (actionW (codeMat 142) (codeMat 161) step109wc119s1SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 130 ∈ step109wc119s1SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 80, 32, 8, 2, 1] 130 (by decide)
    have hact : actionA (codeMat 142) (codeMat 161) (codeMat 130) = codeMat 256 := by
      unfold actionA
      rw [step109wc119s1_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 130 * (codeMat 161 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 81 ∈ step109wc119s1SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 80, 32, 8, 2, 1] 81 (by decide)
    have hact : actionA (codeMat 142) (codeMat 161) (codeMat 81) = codeMat 68 := by
      unfold actionA
      rw [step109wc119s1_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 81 * (codeMat 161 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 128 ∈ step109wc119s1SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 80, 32, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 142) (codeMat 161) (codeMat 128) = codeMat 32 := by
      unfold actionA
      rw [step109wc119s1_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 128 * (codeMat 161 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 80 ∈ step109wc119s1SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 80, 32, 8, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 142) (codeMat 161) (codeMat 80) = codeMat 12 := by
      unfold actionA
      rw [step109wc119s1_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 80 * (codeMat 161 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ step109wc119s1SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 80, 32, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 142) (codeMat 161) (codeMat 32) = codeMat 2 := by
      unfold actionA
      rw [step109wc119s1_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 32 * (codeMat 161 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ step109wc119s1SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 80, 32, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 142) (codeMat 161) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc119s1_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact

theorem step109wc119s1Dispatch :
    QuotientRankAtLeast (o119SourceU_wc ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 161) step109wc119s1SrcT) 12 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 161) hP hQ step109wc119s1SrcT 12
      step109wc119s1SrcT_lb
  exact quotientRankAtLeast_mono step109wc119s1_contain hAct


private theorem step109wc119s2_QtInv :
    (codeMat 98 : Mat3).transpose⁻¹ = (codeMat 140 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 98 : Mat3).transpose * (codeMat 140 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc119s2_contain :
    (o119SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 140) (codeMat 98) o43W_mono := by
  change spanCodes [256, 128, 32, 12, 2, 1] ≤ actionW (codeMat 140) (codeMat 98) o43W_mono
  apply step109wc119_spanCodes_le_of_gens [256, 128, 32, 12, 2, 1]
    (actionW (codeMat 140) (codeMat 98) o43W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 2 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 98) (codeMat 2) = codeMat 256 := by
      unfold actionA
      rw [step109wc119s2_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 140 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 98) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step109wc119s2_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * (codeMat 140 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 128 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 140) (codeMat 98) (codeMat 128) = codeMat 32 := by
      unfold actionA
      rw [step109wc119s2_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 128 * (codeMat 140 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 272 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 272 (by decide)
    have hact : actionA (codeMat 140) (codeMat 98) (codeMat 272) = codeMat 12 := by
      unfold actionA
      rw [step109wc119s2_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 272 * (codeMat 140 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 140) (codeMat 98) (codeMat 8) = codeMat 2 := by
      unfold actionA
      rw [step109wc119s2_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 8 * (codeMat 140 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 140) (codeMat 98) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc119s2_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 32 * (codeMat 140 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact

theorem step109wc119s2Dispatch :
    QuotientRankAtLeast (o119SourceU_wc ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 98) o43W_mono) 12 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 98) hP hQ o43W_mono 12
      orbit43_lb12_mono
  exact quotientRankAtLeast_mono step109wc119s2_contain hAct


private theorem step109wc119s3_QtInv :
    (codeMat 98 : Mat3).transpose⁻¹ = (codeMat 140 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 98 : Mat3).transpose * (codeMat 140 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc119s3_contain :
    (o119SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 266) (codeMat 98) orbit11W := by
  change spanCodes [256, 132, 32, 16, 12, 2, 1] ≤ actionW (codeMat 266) (codeMat 98) orbit11W
  apply step109wc119_spanCodes_le_of_gens [256, 132, 32, 16, 12, 2, 1]
    (actionW (codeMat 266) (codeMat 98) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 128) = codeMat 256 := by
      unfold actionA
      rw [step109wc119s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 128 * (codeMat 140 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 80 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 80 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 80) = codeMat 132 := by
      unfold actionA
      rw [step109wc119s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 80 * (codeMat 140 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [step109wc119s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 140 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc119s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 140 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 20 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 20 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 20) = codeMat 12 := by
      unfold actionA
      rw [step109wc119s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 20 * (codeMat 140 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 8) = codeMat 2 := by
      unfold actionA
      rw [step109wc119s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 140 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc119s3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 140 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact

theorem step109wc119s3Dispatch :
    QuotientRankAtLeast (o119SourceU_wc ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 98) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 98) hP hQ orbit11W 12
      orbit11_lb12
  exact quotientRankAtLeast_mono step109wc119s3_contain hAct


private theorem step109wc119s4_QtInv :
    (codeMat 226 : Mat3).transpose⁻¹ = (codeMat 141 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 226 : Mat3).transpose * (codeMat 141 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc119s4_contain :
    (o119SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 140) (codeMat 226) o43W_mono := by
  change spanCodes [256, 192, 32, 12, 2, 1] ≤ actionW (codeMat 140) (codeMat 226) o43W_mono
  apply step109wc119_spanCodes_le_of_gens [256, 192, 32, 12, 2, 1]
    (actionW (codeMat 140) (codeMat 226) o43W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 2 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 226) (codeMat 2) = codeMat 256 := by
      unfold actionA
      rw [step109wc119s4_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 141 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 226) (codeMat 1) = codeMat 192 := by
      unfold actionA
      rw [step109wc119s4_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * (codeMat 141 : Mat3).transpose = codeMat 192
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 128 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 140) (codeMat 226) (codeMat 128) = codeMat 32 := by
      unfold actionA
      rw [step109wc119s4_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 128 * (codeMat 141 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 272 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 272 (by decide)
    have hact : actionA (codeMat 140) (codeMat 226) (codeMat 272) = codeMat 12 := by
      unfold actionA
      rw [step109wc119s4_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 272 * (codeMat 141 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 40 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 140) (codeMat 226) (codeMat 40) = codeMat 2 := by
      unfold actionA
      rw [step109wc119s4_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 40 * (codeMat 141 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 140) (codeMat 226) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc119s4_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 32 * (codeMat 141 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact

theorem step109wc119s4Dispatch :
    QuotientRankAtLeast (o119SourceU_wc ⟨4, by omega⟩) 12 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 226 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 226) o43W_mono) 12 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 226) hP hQ o43W_mono 12
      orbit43_lb12_mono
  exact quotientRankAtLeast_mono step109wc119s4_contain hAct


private theorem step109wc119s5_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc119s5_contain :
    (o119SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 86) (codeMat 84) orbit14W := by
  change spanCodes [256, 144, 84, 32, 12, 2, 1] ≤ actionW (codeMat 86) (codeMat 84) orbit14W
  apply step109wc119_spanCodes_le_of_gens [256, 144, 84, 32, 12, 2, 1]
    (actionW (codeMat 86) (codeMat 84) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 9 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 9 (by decide)
    have hact : actionA (codeMat 86) (codeMat 84) (codeMat 9) = codeMat 256 := by
      unfold actionA
      rw [step109wc119s5_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 9 * (codeMat 84 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 86) (codeMat 84) (codeMat 2) = codeMat 144 := by
      unfold actionA
      rw [step109wc119s5_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 116 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 116 (by decide)
    have hact : actionA (codeMat 86) (codeMat 84) (codeMat 116) = codeMat 84 := by
      unfold actionA
      rw [step109wc119s5_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 116 * (codeMat 84 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 86) (codeMat 84) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc119s5_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 8 * (codeMat 84 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 86) (codeMat 84) (codeMat 96) = codeMat 12 := by
      unfold actionA
      rw [step109wc119s5_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 96 * (codeMat 84 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 86) (codeMat 84) (codeMat 128) = codeMat 2 := by
      unfold actionA
      rw [step109wc119s5_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 128 * (codeMat 84 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 86) (codeMat 84) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc119s5_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 256 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact

theorem step109wc119s5Dispatch :
    QuotientRankAtLeast (o119SourceU_wc ⟨5, by omega⟩) 12 := by
  have hP : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 86) (codeMat 84) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 86) (codeMat 84) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc119s5_contain hAct


private theorem step109wc119s6_QtInv :
    (codeMat 225 : Mat3).transpose⁻¹ = (codeMat 169 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 225 : Mat3).transpose * (codeMat 169 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc119s6_contain :
    (o119SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 266) (codeMat 225) orbit11W := by
  change spanCodes [256, 196, 32, 20, 12, 2, 1] ≤ actionW (codeMat 266) (codeMat 225) orbit11W
  apply step109wc119_spanCodes_le_of_gens [256, 196, 32, 20, 12, 2, 1]
    (actionW (codeMat 266) (codeMat 225) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 266) (codeMat 225) (codeMat 128) = codeMat 256 := by
      unfold actionA
      rw [step109wc119s6_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 128 * (codeMat 169 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 80 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 80 (by decide)
    have hact : actionA (codeMat 266) (codeMat 225) (codeMat 80) = codeMat 196 := by
      unfold actionA
      rw [step109wc119s6_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 80 * (codeMat 169 : Mat3).transpose = codeMat 196
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 225) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [step109wc119s6_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 169 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 20 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 20 (by decide)
    have hact : actionA (codeMat 266) (codeMat 225) (codeMat 20) = codeMat 20 := by
      unfold actionA
      rw [step109wc119s6_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 20 * (codeMat 169 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 21 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 21 (by decide)
    have hact : actionA (codeMat 266) (codeMat 225) (codeMat 21) = codeMat 12 := by
      unfold actionA
      rw [step109wc119s6_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 21 * (codeMat 169 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 225) (codeMat 32) = codeMat 2 := by
      unfold actionA
      rw [step109wc119s6_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 169 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 40 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 40 (by decide)
    have hact : actionA (codeMat 266) (codeMat 225) (codeMat 40) = codeMat 1 := by
      unfold actionA
      rw [step109wc119s6_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 40 * (codeMat 169 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact

theorem step109wc119s6Dispatch :
    QuotientRankAtLeast (o119SourceU_wc ⟨6, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 225) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 225) hP hQ orbit11W 12
      orbit11_lb12
  exact quotientRankAtLeast_mono step109wc119s6_contain hAct


private theorem step109wc119s7_QtInv :
    (codeMat 212 : Mat3).transpose⁻¹ = (codeMat 86 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 212 : Mat3).transpose * (codeMat 86 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc119s7_contain :
    (o119SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 86) (codeMat 212) orbit14W := by
  change spanCodes [256, 132, 80, 32, 12, 2, 1] ≤ actionW (codeMat 86) (codeMat 212) orbit14W
  apply step109wc119_spanCodes_le_of_gens [256, 132, 80, 32, 12, 2, 1]
    (actionW (codeMat 86) (codeMat 212) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 9 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 9 (by decide)
    have hact : actionA (codeMat 86) (codeMat 212) (codeMat 9) = codeMat 256 := by
      unfold actionA
      rw [step109wc119s7_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 9 * (codeMat 86 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 118 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 118 (by decide)
    have hact : actionA (codeMat 86) (codeMat 212) (codeMat 118) = codeMat 132 := by
      unfold actionA
      rw [step109wc119s7_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 118 * (codeMat 86 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 20 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 20 (by decide)
    have hact : actionA (codeMat 86) (codeMat 212) (codeMat 20) = codeMat 80 := by
      unfold actionA
      rw [step109wc119s7_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 20 * (codeMat 86 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 86) (codeMat 212) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc119s7_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 8 * (codeMat 86 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 86) (codeMat 212) (codeMat 96) = codeMat 12 := by
      unfold actionA
      rw [step109wc119s7_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 96 * (codeMat 86 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 86) (codeMat 212) (codeMat 384) = codeMat 2 := by
      unfold actionA
      rw [step109wc119s7_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 384 * (codeMat 86 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 86) (codeMat 212) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc119s7_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 256 * (codeMat 86 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact

theorem step109wc119s7Dispatch :
    QuotientRankAtLeast (o119SourceU_wc ⟨7, by omega⟩) 12 := by
  have hP : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 212 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 86) (codeMat 212) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 86) (codeMat 212) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc119s7_contain hAct


private theorem step109wc119s8_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc119s8_contain :
    (o119SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 273) (codeMat 140) o19W_mono := by
  change spanCodes [256, 32, 8, 4, 2, 1] ≤ actionW (codeMat 273) (codeMat 140) o19W_mono
  apply step109wc119_spanCodes_le_of_gens [256, 32, 8, 4, 2, 1]
    (actionW (codeMat 273) (codeMat 140) o19W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 64 ∈ o19W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [64, 16, 8, 4, 2, 1] 64 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 64) = codeMat 256 := by
      unfold actionA
      rw [step109wc119s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 64 * (codeMat 98 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ o19W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [64, 16, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc119s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 16 ∈ o19W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [64, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 16) = codeMat 8 := by
      unfold actionA
      rw [step109wc119s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 16 * (codeMat 98 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o19W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [64, 16, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step109wc119s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 4 ∈ o19W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [64, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 4) = codeMat 2 := by
      unfold actionA
      rw [step109wc119s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 4 * (codeMat 98 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o19W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [64, 16, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc119s8_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc119_codeMat_mem_actionW_of_witness hw hact

theorem step109wc119s8Dispatch :
    QuotientRankAtLeast (o119SourceU_wc ⟨8, by omega⟩) 9 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 140) o19W_mono) 9 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 140) hP hQ o19W_mono 9
      orbit19_lb9_mono
  exact quotientRankAtLeast_mono step109wc119s8_contain hAct

theorem step109wc119_all_dispatch (i : Fin 9) :
    QuotientRankAtLeast (o119SourceU_wc i) (o119SourceLb_wc i) := by
  fin_cases i
  · exact step109wc119s0Dispatch
  · exact step109wc119s1Dispatch
  · exact step109wc119s2Dispatch
  · exact step109wc119s3Dispatch
  · exact step109wc119s4Dispatch
  · exact step109wc119s5Dispatch
  · exact step109wc119s6Dispatch
  · exact step109wc119s7Dispatch
  · exact step109wc119s8Dispatch

theorem step109_orbit119_lb14_wc : QuotientRankAtLeast o119W_wc 14 :=
  o119Lb14_wc step109wc119_all_dispatch

end QiushiMatmul
