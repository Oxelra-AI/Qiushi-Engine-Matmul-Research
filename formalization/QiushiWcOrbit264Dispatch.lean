import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit264Consumer
import QiushiMonoOrbit98From31T
import QiushiMonoOrbit124From35T
import QiushiWcOrbit128Dispatch
import QiushiMonoOrbit103From35T
import QiushiMonoOrbit118From31
import QiushiMonoOrbit130From35T
import QiushiWcOrbit113Dispatch
import QiushiStep99Orbit55Dispatch
import QiushiOrbit23FP
import QiushiOrbit11FP
import QiushiOrbit10FP
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc264_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc264_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

private def step109wc264s0SrcT : Submodule F2 Mat3 := spanCodes [80, 32, 8, 2, 1]

private theorem step109wc264s0SrcT_lb : QuotientRankAtLeast step109wc264s0SrcT 15 := by
  have ht := quotientRankAtLeast_transpose orbit98_lb15_mono
  have hle : step109wc264s0SrcT ≤ transposeW o98W_mono := by
    unfold step109wc264s0SrcT transposeW
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

private theorem step109wc264s0_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc264s0_contain :
    (o264SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 140) (codeMat 161) step109wc264s0SrcT := by
  change spanCodes [256, 64, 12, 2, 1] ≤ actionW (codeMat 140) (codeMat 161) step109wc264s0SrcT
  apply step109wc264_spanCodes_le_of_gens [256, 64, 12, 2, 1]
    (actionW (codeMat 140) (codeMat 161) step109wc264s0SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 2 ∈ step109wc264s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [80, 32, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 2) = codeMat 256 := by
      unfold actionA
      rw [step109wc264s0_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ step109wc264s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [80, 32, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 1) = codeMat 64 := by
      unfold actionA
      rw [step109wc264s0_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 80 ∈ step109wc264s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [80, 32, 8, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 80) = codeMat 12 := by
      unfold actionA
      rw [step109wc264s0_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 80 * (codeMat 161 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ step109wc264s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [80, 32, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 32) = codeMat 2 := by
      unfold actionA
      rw [step109wc264s0_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 32 * (codeMat 161 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ step109wc264s0SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [80, 32, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc264s0_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact

theorem step109wc264s0Dispatch :
    QuotientRankAtLeast (o264SourceU_wc ⟨0, by omega⟩) 15 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 161) step109wc264s0SrcT) 15 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 161) hP hQ step109wc264s0SrcT 15
      step109wc264s0SrcT_lb
  exact quotientRankAtLeast_mono step109wc264s0_contain hAct


private theorem step109wc264s1_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc264s1_contain :
    (o264SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 273) (codeMat 273) o124W_mono := by
  change spanCodes [256, 80, 12, 2, 1] ≤ actionW (codeMat 273) (codeMat 273) o124W_mono
  apply step109wc264_spanCodes_le_of_gens [256, 80, 12, 2, 1]
    (actionW (codeMat 273) (codeMat 273) o124W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 256 ∈ o124W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step109wc264s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 273 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 80 ∈ o124W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 12, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 80) = codeMat 80 := by
      unfold actionA
      rw [step109wc264s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 80 * (codeMat 273 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 12 ∈ o124W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 12) = codeMat 12 := by
      unfold actionA
      rw [step109wc264s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 12 * (codeMat 273 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o124W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc264s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o124W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc264s1_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact

theorem step109wc264s1Dispatch :
    QuotientRankAtLeast (o264SourceU_wc ⟨1, by omega⟩) 15 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 273) o124W_mono) 15 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 273) hP hQ o124W_mono 15
      orbit124_lb15_mono
  exact quotientRankAtLeast_mono step109wc264s1_contain hAct


private theorem step109wc264s2_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = (codeMat 275 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * (codeMat 275 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc264s2_contain :
    (o264SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 273) (codeMat 275) o124W_mono := by
  change spanCodes [256, 84, 12, 2, 1] ≤ actionW (codeMat 273) (codeMat 275) o124W_mono
  apply step109wc264_spanCodes_le_of_gens [256, 84, 12, 2, 1]
    (actionW (codeMat 273) (codeMat 275) o124W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 256 ∈ o124W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step109wc264s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 275 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 92 ∈ o124W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 12, 2, 1] 92 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 92) = codeMat 84 := by
      unfold actionA
      rw [step109wc264s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 92 * (codeMat 275 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 12 ∈ o124W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 12) = codeMat 12 := by
      unfold actionA
      rw [step109wc264s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 12 * (codeMat 275 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 3 ∈ o124W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc264s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 3 * (codeMat 275 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o124W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 80, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc264s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 275 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact

theorem step109wc264s2Dispatch :
    QuotientRankAtLeast (o264SourceU_wc ⟨2, by omega⟩) 15 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 275) o124W_mono) 15 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 275) hP hQ o124W_mono 15
      orbit124_lb15_mono
  exact quotientRankAtLeast_mono step109wc264s2_contain hAct


private theorem step109wc264s3_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = (codeMat 305 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * (codeMat 305 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc264s3_contain :
    (o264SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 273) (codeMat 305) o128W_wc := by
  change spanCodes [256, 112, 12, 2, 1] ≤ actionW (codeMat 273) (codeMat 305) o128W_wc
  apply step109wc264_spanCodes_le_of_gens [256, 112, 12, 2, 1]
    (actionW (codeMat 273) (codeMat 305) o128W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 384 ∈ o128W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [384, 96, 12, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 273) (codeMat 305) (codeMat 384) = codeMat 256 := by
      unfold actionA
      rw [step109wc264s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 384 * (codeMat 305 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 96 ∈ o128W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [384, 96, 12, 2, 1] 96 (by decide)
    have hact : actionA (codeMat 273) (codeMat 305) (codeMat 96) = codeMat 112 := by
      unfold actionA
      rw [step109wc264s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 96 * (codeMat 305 : Mat3).transpose = codeMat 112
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 14 ∈ o128W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [384, 96, 12, 2, 1] 14 (by decide)
    have hact : actionA (codeMat 273) (codeMat 305) (codeMat 14) = codeMat 12 := by
      unfold actionA
      rw [step109wc264s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 14 * (codeMat 305 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o128W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [384, 96, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 305) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc264s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 305 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o128W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [384, 96, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 305) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc264s3_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 305 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact

theorem step109wc264s3Dispatch :
    QuotientRankAtLeast (o264SourceU_wc ⟨3, by omega⟩) 15 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 305) o128W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 305) hP hQ o128W_wc 15
      step109_orbit128_lb15_wc
  exact quotientRankAtLeast_mono step109wc264s3_contain hAct


private theorem step109wc264s4_QtInv :
    (codeMat 307 : Mat3).transpose⁻¹ = (codeMat 311 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 307 : Mat3).transpose * (codeMat 311 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc264s4_contain :
    (o264SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 273) (codeMat 307) o128W_wc := by
  change spanCodes [256, 116, 12, 2, 1] ≤ actionW (codeMat 273) (codeMat 307) o128W_wc
  apply step109wc264_spanCodes_le_of_gens [256, 116, 12, 2, 1]
    (actionW (codeMat 273) (codeMat 307) o128W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 384 ∈ o128W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [384, 96, 12, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 273) (codeMat 307) (codeMat 384) = codeMat 256 := by
      unfold actionA
      rw [step109wc264s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 384 * (codeMat 311 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 110 ∈ o128W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [384, 96, 12, 2, 1] 110 (by decide)
    have hact : actionA (codeMat 273) (codeMat 307) (codeMat 110) = codeMat 116 := by
      unfold actionA
      rw [step109wc264s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 110 * (codeMat 311 : Mat3).transpose = codeMat 116
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 14 ∈ o128W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [384, 96, 12, 2, 1] 14 (by decide)
    have hact : actionA (codeMat 273) (codeMat 307) (codeMat 14) = codeMat 12 := by
      unfold actionA
      rw [step109wc264s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 14 * (codeMat 311 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 3 ∈ o128W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [384, 96, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 273) (codeMat 307) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc264s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 3 * (codeMat 311 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o128W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [384, 96, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 307) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc264s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 311 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact

theorem step109wc264s4Dispatch :
    QuotientRankAtLeast (o264SourceU_wc ⟨4, by omega⟩) 15 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 307 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 307) o128W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 307) hP hQ o128W_wc 15
      step109_orbit128_lb15_wc
  exact quotientRankAtLeast_mono step109wc264s4_contain hAct


private theorem step109wc264s5_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc264s5_contain :
    (o264SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 161) (codeMat 266) o103W_mono := by
  change spanCodes [256, 128, 12, 2, 1] ≤ actionW (codeMat 161) (codeMat 266) o103W_mono
  apply step109wc264_spanCodes_le_of_gens [256, 128, 12, 2, 1]
    (actionW (codeMat 161) (codeMat 266) o103W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 32 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 32) = codeMat 256 := by
      unfold actionA
      rw [step109wc264s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 32 * (codeMat 266 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 8) = codeMat 128 := by
      unfold actionA
      rw [step109wc264s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 132 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 132 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 132) = codeMat 12 := by
      unfold actionA
      rw [step109wc264s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 132 * (codeMat 266 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step109wc264s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc264s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact

theorem step109wc264s5Dispatch :
    QuotientRankAtLeast (o264SourceU_wc ⟨5, by omega⟩) 15 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 266) o103W_mono) 15 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 266) hP hQ o103W_mono 15
      orbit103_lb15_mono
  exact quotientRankAtLeast_mono step109wc264s5_contain hAct


private theorem step109wc264s6_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc264s6_contain :
    (o264SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 161) (codeMat 266) o118W_mono := by
  change spanCodes [256, 132, 12, 2, 1] ≤ actionW (codeMat 161) (codeMat 266) o118W_mono
  apply step109wc264_spanCodes_le_of_gens [256, 132, 12, 2, 1]
    (actionW (codeMat 161) (codeMat 266) o118W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 32 ∈ o118W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 32) = codeMat 256 := by
      unfold actionA
      rw [step109wc264s6_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 32 * (codeMat 266 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 12 ∈ o118W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 12) = codeMat 132 := by
      unfold actionA
      rw [step109wc264s6_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 12 * (codeMat 266 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 132 ∈ o118W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 12, 2, 1] 132 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 132) = codeMat 12 := by
      unfold actionA
      rw [step109wc264s6_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 132 * (codeMat 266 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o118W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step109wc264s6_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o118W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc264s6_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact

theorem step109wc264s6Dispatch :
    QuotientRankAtLeast (o264SourceU_wc ⟨6, by omega⟩) 15 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 266) o118W_mono) 15 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 266) hP hQ o118W_mono 15
      orbit118_lb15_mono
  exact quotientRankAtLeast_mono step109wc264s6_contain hAct


private theorem step109wc264s7_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc264s7_contain :
    (o264SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 273) (codeMat 273) o130W_mono := by
  change spanCodes [256, 160, 12, 2, 1] ≤ actionW (codeMat 273) (codeMat 273) o130W_mono
  apply step109wc264_spanCodes_le_of_gens [256, 160, 12, 2, 1]
    (actionW (codeMat 273) (codeMat 273) o130W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 256 ∈ o130W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step109wc264s7_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 273 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ o130W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 12, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 160) = codeMat 160 := by
      unfold actionA
      rw [step109wc264s7_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 160 * (codeMat 273 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 12 ∈ o130W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 12) = codeMat 12 := by
      unfold actionA
      rw [step109wc264s7_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 12 * (codeMat 273 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o130W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc264s7_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o130W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc264s7_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact

theorem step109wc264s7Dispatch :
    QuotientRankAtLeast (o264SourceU_wc ⟨7, by omega⟩) 15 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 273) o130W_mono) 15 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 273) hP hQ o130W_mono 15
      orbit130_lb15_mono
  exact quotientRankAtLeast_mono step109wc264s7_contain hAct


private theorem step109wc264s8_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc264s8_contain :
    (o264SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 281) (codeMat 273) o130W_mono := by
  change spanCodes [256, 164, 12, 2, 1] ≤ actionW (codeMat 281) (codeMat 273) o130W_mono
  apply step109wc264_spanCodes_le_of_gens [256, 164, 12, 2, 1]
    (actionW (codeMat 281) (codeMat 273) o130W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 256 ∈ o130W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 281) (codeMat 273) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step109wc264s8_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 256 * (codeMat 273 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ o130W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 12, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 281) (codeMat 273) (codeMat 160) = codeMat 164 := by
      unfold actionA
      rw [step109wc264s8_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 160 * (codeMat 273 : Mat3).transpose = codeMat 164
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 13 ∈ o130W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 12, 2, 1] 13 (by decide)
    have hact : actionA (codeMat 281) (codeMat 273) (codeMat 13) = codeMat 12 := by
      unfold actionA
      rw [step109wc264s8_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 13 * (codeMat 273 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o130W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 281) (codeMat 273) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc264s8_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o130W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 281) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc264s8_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact

theorem step109wc264s8Dispatch :
    QuotientRankAtLeast (o264SourceU_wc ⟨8, by omega⟩) 15 := by
  have hP : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 281) (codeMat 273) o130W_mono) 15 :=
    @quotientRankAtLeast_action (codeMat 281) (codeMat 273) hP hQ o130W_mono 15
      orbit130_lb15_mono
  exact quotientRankAtLeast_mono step109wc264s8_contain hAct


private theorem step109wc264s9_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = (codeMat 267 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * (codeMat 267 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc264s9_contain :
    (o264SourceU_wc ⟨9, by omega⟩) ≤ actionW (codeMat 161) (codeMat 282) o103W_mono := by
  change spanCodes [256, 192, 12, 2, 1] ≤ actionW (codeMat 161) (codeMat 282) o103W_mono
  apply step109wc264_spanCodes_le_of_gens [256, 192, 12, 2, 1]
    (actionW (codeMat 161) (codeMat 282) o103W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 32 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 161) (codeMat 282) (codeMat 32) = codeMat 256 := by
      unfold actionA
      rw [step109wc264s9_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 32 * (codeMat 267 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 282) (codeMat 8) = codeMat 192 := by
      unfold actionA
      rw [step109wc264s9_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 267 : Mat3).transpose = codeMat 192
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 132 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 132 (by decide)
    have hact : actionA (codeMat 161) (codeMat 282) (codeMat 132) = codeMat 12 := by
      unfold actionA
      rw [step109wc264s9_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 132 * (codeMat 267 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 3 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 161) (codeMat 282) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc264s9_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 3 * (codeMat 267 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o103W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 282) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc264s9_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 267 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact

theorem step109wc264s9Dispatch :
    QuotientRankAtLeast (o264SourceU_wc ⟨9, by omega⟩) 15 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 282) o103W_mono) 15 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 282) hP hQ o103W_mono 15
      orbit103_lb15_mono
  exact quotientRankAtLeast_mono step109wc264s9_contain hAct


private theorem step109wc264s10_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = (codeMat 267 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * (codeMat 267 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc264s10_contain :
    (o264SourceU_wc ⟨10, by omega⟩) ≤ actionW (codeMat 161) (codeMat 282) o118W_mono := by
  change spanCodes [256, 196, 12, 2, 1] ≤ actionW (codeMat 161) (codeMat 282) o118W_mono
  apply step109wc264_spanCodes_le_of_gens [256, 196, 12, 2, 1]
    (actionW (codeMat 161) (codeMat 282) o118W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 32 ∈ o118W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 161) (codeMat 282) (codeMat 32) = codeMat 256 := by
      unfold actionA
      rw [step109wc264s10_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 32 * (codeMat 267 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 12 ∈ o118W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 161) (codeMat 282) (codeMat 12) = codeMat 196 := by
      unfold actionA
      rw [step109wc264s10_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 12 * (codeMat 267 : Mat3).transpose = codeMat 196
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 132 ∈ o118W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 12, 2, 1] 132 (by decide)
    have hact : actionA (codeMat 161) (codeMat 282) (codeMat 132) = codeMat 12 := by
      unfold actionA
      rw [step109wc264s10_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 132 * (codeMat 267 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 3 ∈ o118W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 161) (codeMat 282) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc264s10_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 3 * (codeMat 267 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o118W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [132, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 282) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc264s10_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 267 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact

theorem step109wc264s10Dispatch :
    QuotientRankAtLeast (o264SourceU_wc ⟨10, by omega⟩) 15 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 282) o118W_mono) 15 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 282) hP hQ o118W_mono 15
      orbit118_lb15_mono
  exact quotientRankAtLeast_mono step109wc264s10_contain hAct


private theorem step109wc264s11_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = (codeMat 275 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * (codeMat 275 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc264s11_contain :
    (o264SourceU_wc ⟨11, by omega⟩) ≤ actionW (codeMat 273) (codeMat 275) o130W_mono := by
  change spanCodes [256, 224, 12, 2, 1] ≤ actionW (codeMat 273) (codeMat 275) o130W_mono
  apply step109wc264_spanCodes_le_of_gens [256, 224, 12, 2, 1]
    (actionW (codeMat 273) (codeMat 275) o130W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 256 ∈ o130W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step109wc264s11_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 275 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ o130W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 12, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 160) = codeMat 224 := by
      unfold actionA
      rw [step109wc264s11_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 160 * (codeMat 275 : Mat3).transpose = codeMat 224
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 12 ∈ o130W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 12) = codeMat 12 := by
      unfold actionA
      rw [step109wc264s11_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 12 * (codeMat 275 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 3 ∈ o130W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc264s11_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 3 * (codeMat 275 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o130W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc264s11_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 275 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact

theorem step109wc264s11Dispatch :
    QuotientRankAtLeast (o264SourceU_wc ⟨11, by omega⟩) 15 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 275) o130W_mono) 15 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 275) hP hQ o130W_mono 15
      orbit130_lb15_mono
  exact quotientRankAtLeast_mono step109wc264s11_contain hAct

private def step109wc264s12SrcT : Submodule F2 Mat3 := spanCodes [288, 132, 8, 2, 1]

private theorem step109wc264s12SrcT_lb : QuotientRankAtLeast step109wc264s12SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step109_orbit113_lb14_wc
  have hle : step109wc264s12SrcT ≤ transposeW o113W_wc := by
    unfold step109wc264s12SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4
    · subst h0
      show codeMat 288 ∈ Submodule.map transposeLinearMap o113W_wc
      exact ⟨codeMat 384, spanContainsCodeCore_implies_mem_spanCodes [384, 96, 8, 2, 1] 384 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 132 ∈ Submodule.map transposeLinearMap o113W_wc
      exact ⟨codeMat 96, spanContainsCodeCore_implies_mem_spanCodes [384, 96, 8, 2, 1] 96 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 8 ∈ Submodule.map transposeLinearMap o113W_wc
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [384, 96, 8, 2, 1] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 2 ∈ Submodule.map transposeLinearMap o113W_wc
      exact ⟨codeMat 8, spanContainsCodeCore_implies_mem_spanCodes [384, 96, 8, 2, 1] 8 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 1 ∈ Submodule.map transposeLinearMap o113W_wc
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [384, 96, 8, 2, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc264s12_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc264s12_contain :
    (o264SourceU_wc ⟨12, by omega⟩) ≤ actionW (codeMat 177) (codeMat 266) step109wc264s12SrcT := by
  change spanCodes [256, 144, 12, 2, 1] ≤ actionW (codeMat 177) (codeMat 266) step109wc264s12SrcT
  apply step109wc264_spanCodes_le_of_gens [256, 144, 12, 2, 1]
    (actionW (codeMat 177) (codeMat 266) step109wc264s12SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 288 ∈ step109wc264s12SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 132, 8, 2, 1] 288 (by decide)
    have hact : actionA (codeMat 177) (codeMat 266) (codeMat 288) = codeMat 256 := by
      unfold actionA
      rw [step109wc264s12_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 288 * (codeMat 266 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ step109wc264s12SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 132, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 177) (codeMat 266) (codeMat 8) = codeMat 144 := by
      unfold actionA
      rw [step109wc264s12_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 132 ∈ step109wc264s12SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 132, 8, 2, 1] 132 (by decide)
    have hact : actionA (codeMat 177) (codeMat 266) (codeMat 132) = codeMat 12 := by
      unfold actionA
      rw [step109wc264s12_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 132 * (codeMat 266 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ step109wc264s12SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 132, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 266) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step109wc264s12_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ step109wc264s12SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 132, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 177) (codeMat 266) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc264s12_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact

theorem step109wc264s12Dispatch :
    QuotientRankAtLeast (o264SourceU_wc ⟨12, by omega⟩) 14 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 266) step109wc264s12SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 266) hP hQ step109wc264s12SrcT 14
      step109wc264s12SrcT_lb
  exact quotientRankAtLeast_mono step109wc264s12_contain hAct

private def step109wc264s13SrcT : Submodule F2 Mat3 := spanCodes [288, 132, 8, 2, 1]

private theorem step109wc264s13SrcT_lb : QuotientRankAtLeast step109wc264s13SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step109_orbit113_lb14_wc
  have hle : step109wc264s13SrcT ≤ transposeW o113W_wc := by
    unfold step109wc264s13SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4
    · subst h0
      show codeMat 288 ∈ Submodule.map transposeLinearMap o113W_wc
      exact ⟨codeMat 384, spanContainsCodeCore_implies_mem_spanCodes [384, 96, 8, 2, 1] 384 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 132 ∈ Submodule.map transposeLinearMap o113W_wc
      exact ⟨codeMat 96, spanContainsCodeCore_implies_mem_spanCodes [384, 96, 8, 2, 1] 96 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 8 ∈ Submodule.map transposeLinearMap o113W_wc
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [384, 96, 8, 2, 1] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 2 ∈ Submodule.map transposeLinearMap o113W_wc
      exact ⟨codeMat 8, spanContainsCodeCore_implies_mem_spanCodes [384, 96, 8, 2, 1] 8 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 1 ∈ Submodule.map transposeLinearMap o113W_wc
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [384, 96, 8, 2, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc264s13_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = (codeMat 267 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * (codeMat 267 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc264s13_contain :
    (o264SourceU_wc ⟨13, by omega⟩) ≤ actionW (codeMat 177) (codeMat 282) step109wc264s13SrcT := by
  change spanCodes [256, 212, 12, 2, 1] ≤ actionW (codeMat 177) (codeMat 282) step109wc264s13SrcT
  apply step109wc264_spanCodes_le_of_gens [256, 212, 12, 2, 1]
    (actionW (codeMat 177) (codeMat 282) step109wc264s13SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 288 ∈ step109wc264s13SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 132, 8, 2, 1] 288 (by decide)
    have hact : actionA (codeMat 177) (codeMat 282) (codeMat 288) = codeMat 256 := by
      unfold actionA
      rw [step109wc264s13_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 288 * (codeMat 267 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 140 ∈ step109wc264s13SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 132, 8, 2, 1] 140 (by decide)
    have hact : actionA (codeMat 177) (codeMat 282) (codeMat 140) = codeMat 212 := by
      unfold actionA
      rw [step109wc264s13_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 140 * (codeMat 267 : Mat3).transpose = codeMat 212
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 132 ∈ step109wc264s13SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 132, 8, 2, 1] 132 (by decide)
    have hact : actionA (codeMat 177) (codeMat 282) (codeMat 132) = codeMat 12 := by
      unfold actionA
      rw [step109wc264s13_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 132 * (codeMat 267 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 3 ∈ step109wc264s13SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 132, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 177) (codeMat 282) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc264s13_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 3 * (codeMat 267 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ step109wc264s13SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 132, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 177) (codeMat 282) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc264s13_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 2 * (codeMat 267 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact

theorem step109wc264s13Dispatch :
    QuotientRankAtLeast (o264SourceU_wc ⟨13, by omega⟩) 14 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 282) step109wc264s13SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 282) hP hQ step109wc264s13SrcT 14
      step109wc264s13SrcT_lb
  exact quotientRankAtLeast_mono step109wc264s13_contain hAct


private theorem step109wc264s14_QtInv :
    (codeMat 298 : Mat3).transpose⁻¹ = (codeMat 270 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 298 : Mat3).transpose * (codeMat 270 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc264s14_contain :
    (o264SourceU_wc ⟨14, by omega⟩) ≤ actionW (codeMat 185) (codeMat 298) o55W := by
  change spanCodes [256, 148, 96, 12, 2, 1] ≤ actionW (codeMat 185) (codeMat 298) o55W
  apply step109wc264_spanCodes_le_of_gens [256, 148, 96, 12, 2, 1]
    (actionW (codeMat 185) (codeMat 298) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 438 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 438 (by decide)
    have hact : actionA (codeMat 185) (codeMat 298) (codeMat 438) = codeMat 256 := by
      unfold actionA
      rw [step109wc264s14_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 438 * (codeMat 270 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 15 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 15 (by decide)
    have hact : actionA (codeMat 185) (codeMat 298) (codeMat 15) = codeMat 148 := by
      unfold actionA
      rw [step109wc264s14_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 15 * (codeMat 270 : Mat3).transpose = codeMat 148
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 274 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 274 (by decide)
    have hact : actionA (codeMat 185) (codeMat 298) (codeMat 274) = codeMat 96 := by
      unfold actionA
      rw [step109wc264s14_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 274 * (codeMat 270 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 134 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 134 (by decide)
    have hact : actionA (codeMat 185) (codeMat 298) (codeMat 134) = codeMat 12 := by
      unfold actionA
      rw [step109wc264s14_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 134 * (codeMat 270 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 185) (codeMat 298) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step109wc264s14_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 1 * (codeMat 270 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 185) (codeMat 298) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc264s14_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 2 * (codeMat 270 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact

theorem step109wc264s14Dispatch :
    QuotientRankAtLeast (o264SourceU_wc ⟨14, by omega⟩) 14 := by
  have hP : Invertible (codeMat 185 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 298 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 185) (codeMat 298) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 185) (codeMat 298) hP hQ o55W 14
      step99_orbit55_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc264s14_contain hAct


private theorem step109wc264s15_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc264s15_contain :
    (o264SourceU_wc ⟨15, by omega⟩) ≤ actionW (codeMat 161) (codeMat 140) orbit23W := by
  change spanCodes [256, 96, 8, 4, 2, 1] ≤ actionW (codeMat 161) (codeMat 140) orbit23W
  apply step109wc264_spanCodes_le_of_gens [256, 96, 8, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 140) orbit23W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 8 ∈ orbit23W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 80, 128] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 140) (codeMat 8) = codeMat 256 := by
      unfold actionA
      rw [step109wc264s15_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 80 ∈ orbit23W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 80, 128] 80 (by decide)
    have hact : actionA (codeMat 161) (codeMat 140) (codeMat 80) = codeMat 96 := by
      unfold actionA
      rw [step109wc264s15_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 80 * (codeMat 98 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 128 ∈ orbit23W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 80, 128] 128 (by decide)
    have hact : actionA (codeMat 161) (codeMat 140) (codeMat 128) = codeMat 8 := by
      unfold actionA
      rw [step109wc264s15_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 128 * (codeMat 98 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ orbit23W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 80, 128] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 140) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step109wc264s15_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 4 ∈ orbit23W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 80, 128] 4 (by decide)
    have hact : actionA (codeMat 161) (codeMat 140) (codeMat 4) = codeMat 2 := by
      unfold actionA
      rw [step109wc264s15_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 4 * (codeMat 98 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ orbit23W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 80, 128] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 140) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc264s15_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact

theorem step109wc264s15Dispatch :
    QuotientRankAtLeast (o264SourceU_wc ⟨15, by omega⟩) 12 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 140) orbit23W) 12 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 140) hP hQ orbit23W 12
      orbit23_lb12
  exact quotientRankAtLeast_mono step109wc264s15_contain hAct


private theorem step109wc264s16_QtInv :
    (codeMat 98 : Mat3).transpose⁻¹ = (codeMat 140 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 98 : Mat3).transpose * (codeMat 140 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc264s16_contain :
    (o264SourceU_wc ⟨16, by omega⟩) ≤ actionW (codeMat 267) (codeMat 98) orbit11W := by
  change spanCodes [256, 132, 36, 16, 12, 2, 1] ≤ actionW (codeMat 267) (codeMat 98) orbit11W
  apply step109wc264_spanCodes_le_of_gens [256, 132, 36, 16, 12, 2, 1]
    (actionW (codeMat 267) (codeMat 98) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 267) (codeMat 98) (codeMat 128) = codeMat 256 := by
      unfold actionA
      rw [step109wc264s16_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 128 * (codeMat 140 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 80 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 80 (by decide)
    have hact : actionA (codeMat 267) (codeMat 98) (codeMat 80) = codeMat 132 := by
      unfold actionA
      rw [step109wc264s16_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 80 * (codeMat 140 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 2 (by decide)
    have hact : actionA (codeMat 267) (codeMat 98) (codeMat 2) = codeMat 36 := by
      unfold actionA
      rw [step109wc264s16_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 2 * (codeMat 140 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 9 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 9 (by decide)
    have hact : actionA (codeMat 267) (codeMat 98) (codeMat 9) = codeMat 16 := by
      unfold actionA
      rw [step109wc264s16_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 9 * (codeMat 140 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 52 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 52 (by decide)
    have hact : actionA (codeMat 267) (codeMat 98) (codeMat 52) = codeMat 12 := by
      unfold actionA
      rw [step109wc264s16_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 52 * (codeMat 140 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 8 (by decide)
    have hact : actionA (codeMat 267) (codeMat 98) (codeMat 8) = codeMat 2 := by
      unfold actionA
      rw [step109wc264s16_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 8 * (codeMat 140 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 267) (codeMat 98) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc264s16_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 32 * (codeMat 140 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact

theorem step109wc264s16Dispatch :
    QuotientRankAtLeast (o264SourceU_wc ⟨16, by omega⟩) 12 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 98) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 98) hP hQ orbit11W 12
      orbit11_lb12
  exact quotientRankAtLeast_mono step109wc264s16_contain hAct


private theorem step109wc264s17_QtInv :
    (codeMat 98 : Mat3).transpose⁻¹ = (codeMat 140 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 98 : Mat3).transpose * (codeMat 140 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc264s17_contain :
    (o264SourceU_wc ⟨17, by omega⟩) ≤ actionW (codeMat 266) (codeMat 98) orbit11W := by
  change spanCodes [256, 132, 32, 16, 12, 2, 1] ≤ actionW (codeMat 266) (codeMat 98) orbit11W
  apply step109wc264_spanCodes_le_of_gens [256, 132, 32, 16, 12, 2, 1]
    (actionW (codeMat 266) (codeMat 98) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 128) = codeMat 256 := by
      unfold actionA
      rw [step109wc264s17_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 128 * (codeMat 140 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 80 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 80 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 80) = codeMat 132 := by
      unfold actionA
      rw [step109wc264s17_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 80 * (codeMat 140 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [step109wc264s17_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 140 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc264s17_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 140 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 20 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 20 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 20) = codeMat 12 := by
      unfold actionA
      rw [step109wc264s17_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 20 * (codeMat 140 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 8) = codeMat 2 := by
      unfold actionA
      rw [step109wc264s17_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 140 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc264s17_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 140 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact

theorem step109wc264s17Dispatch :
    QuotientRankAtLeast (o264SourceU_wc ⟨17, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 98) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 98) hP hQ orbit11W 12
      orbit11_lb12
  exact quotientRankAtLeast_mono step109wc264s17_contain hAct


private theorem step109wc264s18_QtInv :
    (codeMat 286 : Mat3).transpose⁻¹ = (codeMat 303 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 286 : Mat3).transpose * (codeMat 303 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc264s18_contain :
    (o264SourceU_wc ⟨18, by omega⟩) ≤ actionW (codeMat 142) (codeMat 286) orbit10W := by
  change spanCodes [256, 144, 68, 52, 12, 2, 1] ≤ actionW (codeMat 142) (codeMat 286) orbit10W
  apply step109wc264_spanCodes_le_of_gens [256, 144, 68, 52, 12, 2, 1]
    (actionW (codeMat 142) (codeMat 286) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 325 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 325 (by decide)
    have hact : actionA (codeMat 142) (codeMat 286) (codeMat 325) = codeMat 256 := by
      unfold actionA
      rw [step109wc264s18_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 325 * (codeMat 303 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 3 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 142) (codeMat 286) (codeMat 3) = codeMat 144 := by
      unfold actionA
      rw [step109wc264s18_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 3 * (codeMat 303 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 170 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 170 (by decide)
    have hact : actionA (codeMat 142) (codeMat 286) (codeMat 170) = codeMat 68 := by
      unfold actionA
      rw [step109wc264s18_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 170 * (codeMat 303 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 424 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 424 (by decide)
    have hact : actionA (codeMat 142) (codeMat 286) (codeMat 424) = codeMat 52 := by
      unfold actionA
      rw [step109wc264s18_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 424 * (codeMat 303 : Mat3).transpose = codeMat 52
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 168 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 168 (by decide)
    have hact : actionA (codeMat 142) (codeMat 286) (codeMat 168) = codeMat 12 := by
      unfold actionA
      rw [step109wc264s18_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 168 * (codeMat 303 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 142) (codeMat 286) (codeMat 24) = codeMat 2 := by
      unfold actionA
      rw [step109wc264s18_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 24 * (codeMat 303 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 142) (codeMat 286) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc264s18_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 16 * (codeMat 303 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact

theorem step109wc264s18Dispatch :
    QuotientRankAtLeast (o264SourceU_wc ⟨18, by omega⟩) 12 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 286 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 286) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 286) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc264s18_contain hAct


private theorem step109wc264s19_QtInv :
    (codeMat 270 : Mat3).transpose⁻¹ = (codeMat 298 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 270 : Mat3).transpose * (codeMat 298 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc264s19_contain :
    (o264SourceU_wc ⟨19, by omega⟩) ≤ actionW (codeMat 142) (codeMat 270) orbit10W := by
  change spanCodes [256, 144, 68, 48, 12, 2, 1] ≤ actionW (codeMat 142) (codeMat 270) orbit10W
  apply step109wc264_spanCodes_le_of_gens [256, 144, 68, 48, 12, 2, 1]
    (actionW (codeMat 142) (codeMat 270) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 325 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 325 (by decide)
    have hact : actionA (codeMat 142) (codeMat 270) (codeMat 325) = codeMat 256 := by
      unfold actionA
      rw [step109wc264s19_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 325 * (codeMat 298 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 142) (codeMat 270) (codeMat 1) = codeMat 144 := by
      unfold actionA
      rw [step109wc264s19_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 1 * (codeMat 298 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 170 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 170 (by decide)
    have hact : actionA (codeMat 142) (codeMat 270) (codeMat 170) = codeMat 68 := by
      unfold actionA
      rw [step109wc264s19_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 170 * (codeMat 298 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 142) (codeMat 270) (codeMat 256) = codeMat 48 := by
      unfold actionA
      rw [step109wc264s19_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 256 * (codeMat 298 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 168 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 168 (by decide)
    have hact : actionA (codeMat 142) (codeMat 270) (codeMat 168) = codeMat 12 := by
      unfold actionA
      rw [step109wc264s19_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 168 * (codeMat 298 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 142) (codeMat 270) (codeMat 8) = codeMat 2 := by
      unfold actionA
      rw [step109wc264s19_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 8 * (codeMat 298 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 142) (codeMat 270) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc264s19_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 16 * (codeMat 298 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact

theorem step109wc264s19Dispatch :
    QuotientRankAtLeast (o264SourceU_wc ⟨19, by omega⟩) 12 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 270 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 270) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 270) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc264s19_contain hAct


private theorem step109wc264s20_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc264s20_contain :
    (o264SourceU_wc ⟨20, by omega⟩) ≤ actionW (codeMat 142) (codeMat 161) orbit11W := by
  change spanCodes [256, 148, 68, 32, 12, 2, 1] ≤ actionW (codeMat 142) (codeMat 161) orbit11W
  apply step109wc264_spanCodes_le_of_gens [256, 148, 68, 32, 12, 2, 1]
    (actionW (codeMat 142) (codeMat 161) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 130 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 130 (by decide)
    have hact : actionA (codeMat 142) (codeMat 161) (codeMat 130) = codeMat 256 := by
      unfold actionA
      rw [step109wc264s20_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 130 * (codeMat 161 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 20 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 20 (by decide)
    have hact : actionA (codeMat 142) (codeMat 161) (codeMat 20) = codeMat 148 := by
      unfold actionA
      rw [step109wc264s20_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 20 * (codeMat 161 : Mat3).transpose = codeMat 148
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 81 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 81 (by decide)
    have hact : actionA (codeMat 142) (codeMat 161) (codeMat 81) = codeMat 68 := by
      unfold actionA
      rw [step109wc264s20_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 81 * (codeMat 161 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 142) (codeMat 161) (codeMat 128) = codeMat 32 := by
      unfold actionA
      rw [step109wc264s20_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 128 * (codeMat 161 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 80 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 80 (by decide)
    have hact : actionA (codeMat 142) (codeMat 161) (codeMat 80) = codeMat 12 := by
      unfold actionA
      rw [step109wc264s20_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 80 * (codeMat 161 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 142) (codeMat 161) (codeMat 32) = codeMat 2 := by
      unfold actionA
      rw [step109wc264s20_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 32 * (codeMat 161 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 8 (by decide)
    have hact : actionA (codeMat 142) (codeMat 161) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc264s20_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact

theorem step109wc264s20Dispatch :
    QuotientRankAtLeast (o264SourceU_wc ⟨20, by omega⟩) 12 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 161) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 161) hP hQ orbit11W 12
      orbit11_lb12
  exact quotientRankAtLeast_mono step109wc264s20_contain hAct


private theorem step109wc264s21_QtInv :
    (codeMat 225 : Mat3).transpose⁻¹ = (codeMat 169 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 225 : Mat3).transpose * (codeMat 169 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc264s21_contain :
    (o264SourceU_wc ⟨21, by omega⟩) ≤ actionW (codeMat 266) (codeMat 225) orbit11W := by
  change spanCodes [256, 196, 32, 20, 12, 2, 1] ≤ actionW (codeMat 266) (codeMat 225) orbit11W
  apply step109wc264_spanCodes_le_of_gens [256, 196, 32, 20, 12, 2, 1]
    (actionW (codeMat 266) (codeMat 225) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 266) (codeMat 225) (codeMat 128) = codeMat 256 := by
      unfold actionA
      rw [step109wc264s21_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 128 * (codeMat 169 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 80 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 80 (by decide)
    have hact : actionA (codeMat 266) (codeMat 225) (codeMat 80) = codeMat 196 := by
      unfold actionA
      rw [step109wc264s21_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 80 * (codeMat 169 : Mat3).transpose = codeMat 196
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 225) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [step109wc264s21_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 169 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 20 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 20 (by decide)
    have hact : actionA (codeMat 266) (codeMat 225) (codeMat 20) = codeMat 20 := by
      unfold actionA
      rw [step109wc264s21_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 20 * (codeMat 169 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 21 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 21 (by decide)
    have hact : actionA (codeMat 266) (codeMat 225) (codeMat 21) = codeMat 12 := by
      unfold actionA
      rw [step109wc264s21_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 21 * (codeMat 169 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 225) (codeMat 32) = codeMat 2 := by
      unfold actionA
      rw [step109wc264s21_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 169 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 40 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 40 (by decide)
    have hact : actionA (codeMat 266) (codeMat 225) (codeMat 40) = codeMat 1 := by
      unfold actionA
      rw [step109wc264s21_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 40 * (codeMat 169 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact

theorem step109wc264s21Dispatch :
    QuotientRankAtLeast (o264SourceU_wc ⟨21, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 225) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 225) hP hQ orbit11W 12
      orbit11_lb12
  exact quotientRankAtLeast_mono step109wc264s21_contain hAct


private theorem step109wc264s22_QtInv :
    (codeMat 165 : Mat3).transpose⁻¹ = (codeMat 163 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 165 : Mat3).transpose * (codeMat 163 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc264s22_contain :
    (o264SourceU_wc ⟨22, by omega⟩) ≤ actionW (codeMat 143) (codeMat 165) orbit11W := by
  change spanCodes [256, 148, 68, 36, 12, 2, 1] ≤ actionW (codeMat 143) (codeMat 165) orbit11W
  apply step109wc264_spanCodes_le_of_gens [256, 148, 68, 36, 12, 2, 1]
    (actionW (codeMat 143) (codeMat 165) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 219 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 219 (by decide)
    have hact : actionA (codeMat 143) (codeMat 165) (codeMat 219) = codeMat 256 := by
      unfold actionA
      rw [step109wc264s22_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 219 * (codeMat 163 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 60 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 60 (by decide)
    have hact : actionA (codeMat 143) (codeMat 165) (codeMat 60) = codeMat 148 := by
      unfold actionA
      rw [step109wc264s22_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 60 * (codeMat 163 : Mat3).transpose = codeMat 148
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 81 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 81 (by decide)
    have hact : actionA (codeMat 143) (codeMat 165) (codeMat 81) = codeMat 68 := by
      unfold actionA
      rw [step109wc264s22_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 81 * (codeMat 163 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 216 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 216 (by decide)
    have hact : actionA (codeMat 143) (codeMat 165) (codeMat 216) = codeMat 36 := by
      unfold actionA
      rw [step109wc264s22_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 216 * (codeMat 163 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 88 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 88 (by decide)
    have hact : actionA (codeMat 143) (codeMat 165) (codeMat 88) = codeMat 12 := by
      unfold actionA
      rw [step109wc264s22_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 88 * (codeMat 163 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 143) (codeMat 165) (codeMat 32) = codeMat 2 := by
      unfold actionA
      rw [step109wc264s22_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 32 * (codeMat 163 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 8 (by decide)
    have hact : actionA (codeMat 143) (codeMat 165) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc264s22_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 8 * (codeMat 163 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact

theorem step109wc264s22Dispatch :
    QuotientRankAtLeast (o264SourceU_wc ⟨22, by omega⟩) 12 := by
  have hP : Invertible (codeMat 143 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 165 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 143) (codeMat 165) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 143) (codeMat 165) hP hQ orbit11W 12
      orbit11_lb12
  exact quotientRankAtLeast_mono step109wc264s22_contain hAct


private theorem step109wc264s23_QtInv :
    (codeMat 225 : Mat3).transpose⁻¹ = (codeMat 169 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 225 : Mat3).transpose * (codeMat 169 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc264s23_contain :
    (o264SourceU_wc ⟨23, by omega⟩) ≤ actionW (codeMat 267) (codeMat 225) orbit11W := by
  change spanCodes [256, 196, 36, 20, 12, 2, 1] ≤ actionW (codeMat 267) (codeMat 225) orbit11W
  apply step109wc264_spanCodes_le_of_gens [256, 196, 36, 20, 12, 2, 1]
    (actionW (codeMat 267) (codeMat 225) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 267) (codeMat 225) (codeMat 128) = codeMat 256 := by
      unfold actionA
      rw [step109wc264s23_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 128 * (codeMat 169 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 80 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 80 (by decide)
    have hact : actionA (codeMat 267) (codeMat 225) (codeMat 80) = codeMat 196 := by
      unfold actionA
      rw [step109wc264s23_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 80 * (codeMat 169 : Mat3).transpose = codeMat 196
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 2 (by decide)
    have hact : actionA (codeMat 267) (codeMat 225) (codeMat 2) = codeMat 36 := by
      unfold actionA
      rw [step109wc264s23_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 2 * (codeMat 169 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 52 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 52 (by decide)
    have hact : actionA (codeMat 267) (codeMat 225) (codeMat 52) = codeMat 20 := by
      unfold actionA
      rw [step109wc264s23_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 52 * (codeMat 169 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 61 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 61 (by decide)
    have hact : actionA (codeMat 267) (codeMat 225) (codeMat 61) = codeMat 12 := by
      unfold actionA
      rw [step109wc264s23_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 61 * (codeMat 169 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 267) (codeMat 225) (codeMat 32) = codeMat 2 := by
      unfold actionA
      rw [step109wc264s23_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 32 * (codeMat 169 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 40 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 40 (by decide)
    have hact : actionA (codeMat 267) (codeMat 225) (codeMat 40) = codeMat 1 := by
      unfold actionA
      rw [step109wc264s23_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 40 * (codeMat 169 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact

theorem step109wc264s23Dispatch :
    QuotientRankAtLeast (o264SourceU_wc ⟨23, by omega⟩) 12 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 225) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 225) hP hQ orbit11W 12
      orbit11_lb12
  exact quotientRankAtLeast_mono step109wc264s23_contain hAct


private theorem step109wc264s24_QtInv :
    (codeMat 468 : Mat3).transpose⁻¹ = (codeMat 87 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 468 : Mat3).transpose * (codeMat 87 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc264s24_contain :
    (o264SourceU_wc ⟨24, by omega⟩) ≤ actionW (codeMat 177) (codeMat 468) flatW_7 := by
  change spanCodes [256, 176, 96, 8, 4, 2, 1] ≤ actionW (codeMat 177) (codeMat 468) flatW_7
  apply step109wc264_spanCodes_le_of_gens [256, 176, 96, 8, 4, 2, 1]
    (actionW (codeMat 177) (codeMat 468) flatW_7)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 360 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 360 (by decide)
    have hact : actionA (codeMat 177) (codeMat 468) (codeMat 360) = codeMat 256 := by
      unfold actionA
      rw [step109wc264s24_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 360 * (codeMat 87 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 368 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 368 (by decide)
    have hact : actionA (codeMat 177) (codeMat 468) (codeMat 368) = codeMat 176 := by
      unfold actionA
      rw [step109wc264s24_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 368 * (codeMat 87 : Mat3).transpose = codeMat 176
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 96 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 96 (by decide)
    have hact : actionA (codeMat 177) (codeMat 468) (codeMat 96) = codeMat 96 := by
      unfold actionA
      rw [step109wc264s24_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 96 * (codeMat 87 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 177) (codeMat 468) (codeMat 256) = codeMat 8 := by
      unfold actionA
      rw [step109wc264s24_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 256 * (codeMat 87 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 5 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 5 (by decide)
    have hact : actionA (codeMat 177) (codeMat 468) (codeMat 5) = codeMat 4 := by
      unfold actionA
      rw [step109wc264s24_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 5 * (codeMat 87 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 6 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 6 (by decide)
    have hact : actionA (codeMat 177) (codeMat 468) (codeMat 6) = codeMat 2 := by
      unfold actionA
      rw [step109wc264s24_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 6 * (codeMat 87 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 4 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 177) (codeMat 468) (codeMat 4) = codeMat 1 := by
      unfold actionA
      rw [step109wc264s24_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 4 * (codeMat 87 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact

theorem step109wc264s24Dispatch :
    QuotientRankAtLeast (o264SourceU_wc ⟨24, by omega⟩) 9 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 468 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 468) flatW_7) 9 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 468) hP hQ flatW_7 9
      flatSeed_7
  exact quotientRankAtLeast_mono step109wc264s24_contain hAct


private theorem step109wc264s25_QtInv :
    (codeMat 281 : Mat3).transpose⁻¹ = (codeMat 281 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 281 : Mat3).transpose * (codeMat 281 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc264s25_contain :
    (o264SourceU_wc ⟨25, by omega⟩) ≤ actionW (codeMat 273) (codeMat 281) flatW_7 := by
  change spanCodes [256, 224, 16, 8, 4, 2, 1] ≤ actionW (codeMat 273) (codeMat 281) flatW_7
  apply step109wc264_spanCodes_le_of_gens [256, 224, 16, 8, 4, 2, 1]
    (actionW (codeMat 273) (codeMat 281) flatW_7)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 281) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step109wc264s25_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 281 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 96 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 96 (by decide)
    have hact : actionA (codeMat 273) (codeMat 281) (codeMat 96) = codeMat 224 := by
      unfold actionA
      rw [step109wc264s25_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 96 * (codeMat 281 : Mat3).transpose = codeMat 224
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 16 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 273) (codeMat 281) (codeMat 16) = codeMat 16 := by
      unfold actionA
      rw [step109wc264s25_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 16 * (codeMat 281 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 24 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 24 (by decide)
    have hact : actionA (codeMat 273) (codeMat 281) (codeMat 24) = codeMat 8 := by
      unfold actionA
      rw [step109wc264s25_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 24 * (codeMat 281 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 4 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 273) (codeMat 281) (codeMat 4) = codeMat 4 := by
      unfold actionA
      rw [step109wc264s25_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 4 * (codeMat 281 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 281) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc264s25_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 281 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 273) (codeMat 281) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step109wc264s25_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 3 * (codeMat 281 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc264_codeMat_mem_actionW_of_witness hw hact

theorem step109wc264s25Dispatch :
    QuotientRankAtLeast (o264SourceU_wc ⟨25, by omega⟩) 9 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 281) flatW_7) 9 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 281) hP hQ flatW_7 9
      flatSeed_7
  exact quotientRankAtLeast_mono step109wc264s25_contain hAct

theorem step109wc264_all_dispatch (i : Fin 26) :
    QuotientRankAtLeast (o264SourceU_wc i) (o264SourceLb_wc i) := by
  fin_cases i
  · exact step109wc264s0Dispatch
  · exact step109wc264s1Dispatch
  · exact step109wc264s2Dispatch
  · exact step109wc264s3Dispatch
  · exact step109wc264s4Dispatch
  · exact step109wc264s5Dispatch
  · exact step109wc264s6Dispatch
  · exact step109wc264s7Dispatch
  · exact step109wc264s8Dispatch
  · exact step109wc264s9Dispatch
  · exact step109wc264s10Dispatch
  · exact step109wc264s11Dispatch
  · exact step109wc264s12Dispatch
  · exact step109wc264s13Dispatch
  · exact step109wc264s14Dispatch
  · exact step109wc264s15Dispatch
  · exact step109wc264s16Dispatch
  · exact step109wc264s17Dispatch
  · exact step109wc264s18Dispatch
  · exact step109wc264s19Dispatch
  · exact step109wc264s20Dispatch
  · exact step109wc264s21Dispatch
  · exact step109wc264s22Dispatch
  · exact step109wc264s23Dispatch
  · exact step109wc264s24Dispatch
  · exact step109wc264s25Dispatch

theorem step109_orbit264_lb16_wc : QuotientRankAtLeast o264W_wc 16 :=
  o264Lb16_wc step109wc264_all_dispatch

end QiushiMatmul
