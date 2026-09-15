import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit187Consumer
import QiushiStep99Orbit34Dispatch
import QiushiMonoOrbit71From17
import QiushiStep99Orbit55Dispatch
import QiushiWcOrbit78Dispatch
import QiushiStep99Orbit82Dispatch
import QiushiMonoOrbit43From14
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc187_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc187_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc187s0_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc187s0_contain :
    (o187SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 273) (codeMat 140) o34W := by
  change spanCodes [258, 128, 32, 10, 4, 1] ≤ actionW (codeMat 273) (codeMat 140) o34W
  apply step109wc187_spanCodes_le_of_gens [258, 128, 32, 10, 4, 1]
    (actionW (codeMat 273) (codeMat 140) o34W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 68 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 68 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 68) = codeMat 258 := by
      unfold actionA
      rw [step109wc187s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 68 * (codeMat 98 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 256) = codeMat 128 := by
      unfold actionA
      rw [step109wc187s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 98 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc187s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 20 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 20) = codeMat 10 := by
      unfold actionA
      rw [step109wc187s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * (codeMat 98 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step109wc187s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o34W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 68, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 140) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc187s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact

theorem step109wc187s0Dispatch :
    QuotientRankAtLeast (o187SourceU_wc ⟨0, by omega⟩) 14 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 140) o34W) 14 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 140) hP hQ o34W 14
      step99_orbit34_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc187s0_contain hAct


private theorem step109wc187s1_QtInv :
    (codeMat 93 : Mat3).transpose⁻¹ = (codeMat 372 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 93 : Mat3).transpose * (codeMat 372 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc187s1_contain :
    (o187SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 282) (codeMat 93) o71W_mono := by
  change spanCodes [262, 128, 32, 20, 10, 1] ≤ actionW (codeMat 282) (codeMat 93) o71W_mono
  apply step109wc187_spanCodes_le_of_gens [262, 128, 32, 20, 10, 1]
    (actionW (codeMat 282) (codeMat 93) o71W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 91 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 91 (by decide)
    have hact : actionA (codeMat 282) (codeMat 93) (codeMat 91) = codeMat 262 := by
      unfold actionA
      rw [step109wc187s1_QtInv]
      show (codeMat 282 : Mat3).transpose * codeMat 91 * (codeMat 372 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 128 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 282) (codeMat 93) (codeMat 128) = codeMat 128 := by
      unfold actionA
      rw [step109wc187s1_QtInv]
      show (codeMat 282 : Mat3).transpose * codeMat 128 * (codeMat 372 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 282) (codeMat 93) (codeMat 1) = codeMat 32 := by
      unfold actionA
      rw [step109wc187s1_QtInv]
      show (codeMat 282 : Mat3).transpose * codeMat 1 * (codeMat 372 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 11 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 282) (codeMat 93) (codeMat 11) = codeMat 20 := by
      unfold actionA
      rw [step109wc187s1_QtInv]
      show (codeMat 282 : Mat3).transpose * codeMat 11 * (codeMat 372 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 21 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 21 (by decide)
    have hact : actionA (codeMat 282) (codeMat 93) (codeMat 21) = codeMat 10 := by
      unfold actionA
      rw [step109wc187s1_QtInv]
      show (codeMat 282 : Mat3).transpose * codeMat 21 * (codeMat 372 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 63 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 63 (by decide)
    have hact : actionA (codeMat 282) (codeMat 93) (codeMat 63) = codeMat 1 := by
      unfold actionA
      rw [step109wc187s1_QtInv]
      show (codeMat 282 : Mat3).transpose * codeMat 63 * (codeMat 372 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact

theorem step109wc187s1Dispatch :
    QuotientRankAtLeast (o187SourceU_wc ⟨1, by omega⟩) 14 := by
  have hP : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 93 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 282) (codeMat 93) o71W_mono) 14 :=
    @quotientRankAtLeast_action (codeMat 282) (codeMat 93) hP hQ o71W_mono 14
      orbit71_lb14_mono
  exact quotientRankAtLeast_mono step109wc187s1_contain hAct

private def step109wc187s2SrcT : Submodule F2 Mat3 := spanCodes [272, 128, 66, 34, 8, 1]

private theorem step109wc187s2SrcT_lb : QuotientRankAtLeast step109wc187s2SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step99_orbit55_lb14_unconditional
  have hle : step109wc187s2SrcT ≤ transposeW o55W := by
    unfold step109wc187s2SrcT transposeW
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

private theorem step109wc187s2_QtInv :
    (codeMat 123 : Mat3).transpose⁻¹ = (codeMat 236 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 123 : Mat3).transpose * (codeMat 236 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc187s2_contain :
    (o187SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 158) (codeMat 123) step109wc187s2SrcT := by
  change spanCodes [262, 128, 32, 22, 10, 1] ≤ actionW (codeMat 158) (codeMat 123) step109wc187s2SrcT
  apply step109wc187_spanCodes_le_of_gens [262, 128, 32, 22, 10, 1]
    (actionW (codeMat 158) (codeMat 123) step109wc187s2SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 202 ∈ step109wc187s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 202 (by decide)
    have hact : actionA (codeMat 158) (codeMat 123) (codeMat 202) = codeMat 262 := by
      unfold actionA
      rw [step109wc187s2_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 202 * (codeMat 236 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 195 ∈ step109wc187s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 195 (by decide)
    have hact : actionA (codeMat 158) (codeMat 123) (codeMat 195) = codeMat 128 := by
      unfold actionA
      rw [step109wc187s2_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 195 * (codeMat 236 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 128 ∈ step109wc187s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 128 (by decide)
    have hact : actionA (codeMat 158) (codeMat 123) (codeMat 128) = codeMat 32 := by
      unfold actionA
      rw [step109wc187s2_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 128 * (codeMat 236 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 136 ∈ step109wc187s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 136 (by decide)
    have hact : actionA (codeMat 158) (codeMat 123) (codeMat 136) = codeMat 22 := by
      unfold actionA
      rw [step109wc187s2_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 136 * (codeMat 236 : Mat3).transpose = codeMat 22
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 280 ∈ step109wc187s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 280 (by decide)
    have hact : actionA (codeMat 158) (codeMat 123) (codeMat 280) = codeMat 10 := by
      unfold actionA
      rw [step109wc187s2_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 280 * (codeMat 236 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 504 ∈ step109wc187s2SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 66, 34, 8, 1] 504 (by decide)
    have hact : actionA (codeMat 158) (codeMat 123) (codeMat 504) = codeMat 1 := by
      unfold actionA
      rw [step109wc187s2_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 504 * (codeMat 236 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact

theorem step109wc187s2Dispatch :
    QuotientRankAtLeast (o187SourceU_wc ⟨2, by omega⟩) 14 := by
  have hP : Invertible (codeMat 158 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 123 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 158) (codeMat 123) step109wc187s2SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 158) (codeMat 123) hP hQ step109wc187s2SrcT 14
      step109wc187s2SrcT_lb
  exact quotientRankAtLeast_mono step109wc187s2_contain hAct


private theorem step109wc187s3_QtInv :
    (codeMat 183 : Mat3).transpose⁻¹ = (codeMat 419 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 183 : Mat3).transpose * (codeMat 419 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc187s3_contain :
    (o187SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 425) (codeMat 183) o71W_mono := by
  change spanCodes [262, 128, 68, 32, 10, 1] ≤ actionW (codeMat 425) (codeMat 183) o71W_mono
  apply step109wc187_spanCodes_le_of_gens [262, 128, 68, 32, 10, 1]
    (actionW (codeMat 425) (codeMat 183) o71W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 31 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 31 (by decide)
    have hact : actionA (codeMat 425) (codeMat 183) (codeMat 31) = codeMat 262 := by
      unfold actionA
      rw [step109wc187s3_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 31 * (codeMat 419 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 63 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 63 (by decide)
    have hact : actionA (codeMat 425) (codeMat 183) (codeMat 63) = codeMat 128 := by
      unfold actionA
      rw [step109wc187s3_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 63 * (codeMat 419 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 10 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 425) (codeMat 183) (codeMat 10) = codeMat 68 := by
      unfold actionA
      rw [step109wc187s3_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 10 * (codeMat 419 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 219 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 219 (by decide)
    have hact : actionA (codeMat 425) (codeMat 183) (codeMat 219) = codeMat 32 := by
      unfold actionA
      rw [step109wc187s3_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 219 * (codeMat 419 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 78 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 425) (codeMat 183) (codeMat 78) = codeMat 10 := by
      unfold actionA
      rw [step109wc187s3_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 78 * (codeMat 419 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o71W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 425) (codeMat 183) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc187s3_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 1 * (codeMat 419 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact

theorem step109wc187s3Dispatch :
    QuotientRankAtLeast (o187SourceU_wc ⟨3, by omega⟩) 14 := by
  have hP : Invertible (codeMat 425 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 183 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 425) (codeMat 183) o71W_mono) 14 :=
    @quotientRankAtLeast_action (codeMat 425) (codeMat 183) hP hQ o71W_mono 14
      orbit71_lb14_mono
  exact quotientRankAtLeast_mono step109wc187s3_contain hAct


private theorem step109wc187s4_QtInv :
    (codeMat 370 : Mat3).transpose⁻¹ = (codeMat 207 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 370 : Mat3).transpose * (codeMat 207 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc187s4_contain :
    (o187SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 460) (codeMat 370) o55W := by
  change spanCodes [262, 128, 70, 32, 10, 1] ≤ actionW (codeMat 460) (codeMat 370) o55W
  apply step109wc187_spanCodes_le_of_gens [262, 128, 70, 32, 10, 1]
    (actionW (codeMat 460) (codeMat 370) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 46 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 46 (by decide)
    have hact : actionA (codeMat 460) (codeMat 370) (codeMat 46) = codeMat 262 := by
      unfold actionA
      rw [step109wc187s4_QtInv]
      show (codeMat 460 : Mat3).transpose * codeMat 46 * (codeMat 207 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 3 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 460) (codeMat 370) (codeMat 3) = codeMat 128 := by
      unfold actionA
      rw [step109wc187s4_QtInv]
      show (codeMat 460 : Mat3).transpose * codeMat 3 * (codeMat 207 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 44 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 44 (by decide)
    have hact : actionA (codeMat 460) (codeMat 370) (codeMat 44) = codeMat 70 := by
      unfold actionA
      rw [step109wc187s4_QtInv]
      show (codeMat 460 : Mat3).transpose * codeMat 44 * (codeMat 207 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 438 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 438 (by decide)
    have hact : actionA (codeMat 460) (codeMat 370) (codeMat 438) = codeMat 32 := by
      unfold actionA
      rw [step109wc187s4_QtInv]
      show (codeMat 460 : Mat3).transpose * codeMat 438 * (codeMat 207 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 316 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 316 (by decide)
    have hact : actionA (codeMat 460) (codeMat 370) (codeMat 316) = codeMat 10 := by
      unfold actionA
      rw [step109wc187s4_QtInv]
      show (codeMat 460 : Mat3).transpose * codeMat 316 * (codeMat 207 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 460) (codeMat 370) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc187s4_QtInv]
      show (codeMat 460 : Mat3).transpose * codeMat 32 * (codeMat 207 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact

theorem step109wc187s4Dispatch :
    QuotientRankAtLeast (o187SourceU_wc ⟨4, by omega⟩) 14 := by
  have hP : Invertible (codeMat 460 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 370 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 460) (codeMat 370) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 460) (codeMat 370) hP hQ o55W 14
      step99_orbit55_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc187s4_contain hAct


private theorem step109wc187s5_QtInv :
    (codeMat 355 : Mat3).transpose⁻¹ = (codeMat 190 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 355 : Mat3).transpose * (codeMat 190 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc187s5_contain :
    (o187SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 412) (codeMat 355) o78W_wc := by
  change spanCodes [262, 128, 84, 32, 10, 1] ≤ actionW (codeMat 412) (codeMat 355) o78W_wc
  apply step109wc187_spanCodes_le_of_gens [262, 128, 84, 32, 10, 1]
    (actionW (codeMat 412) (codeMat 355) o78W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 505 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 505 (by decide)
    have hact : actionA (codeMat 412) (codeMat 355) (codeMat 505) = codeMat 262 := by
      unfold actionA
      rw [step109wc187s5_QtInv]
      show (codeMat 412 : Mat3).transpose * codeMat 505 * (codeMat 190 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 412) (codeMat 355) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step109wc187s5_QtInv]
      show (codeMat 412 : Mat3).transpose * codeMat 1 * (codeMat 190 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 498 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 498 (by decide)
    have hact : actionA (codeMat 412) (codeMat 355) (codeMat 498) = codeMat 84 := by
      unfold actionA
      rw [step109wc187s5_QtInv]
      show (codeMat 412 : Mat3).transpose * codeMat 498 * (codeMat 190 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 390 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 390 (by decide)
    have hact : actionA (codeMat 412) (codeMat 355) (codeMat 390) = codeMat 32 := by
      unfold actionA
      rw [step109wc187s5_QtInv]
      show (codeMat 412 : Mat3).transpose * codeMat 390 * (codeMat 190 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 268 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 268 (by decide)
    have hact : actionA (codeMat 412) (codeMat 355) (codeMat 268) = codeMat 10 := by
      unfold actionA
      rw [step109wc187s5_QtInv]
      show (codeMat 412 : Mat3).transpose * codeMat 268 * (codeMat 190 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 365 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 365 (by decide)
    have hact : actionA (codeMat 412) (codeMat 355) (codeMat 365) = codeMat 1 := by
      unfold actionA
      rw [step109wc187s5_QtInv]
      show (codeMat 412 : Mat3).transpose * codeMat 365 * (codeMat 190 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact

theorem step109wc187s5Dispatch :
    QuotientRankAtLeast (o187SourceU_wc ⟨5, by omega⟩) 14 := by
  have hP : Invertible (codeMat 412 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 355 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 412) (codeMat 355) o78W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 412) (codeMat 355) hP hQ o78W_wc 14
      step109_orbit78_lb14_wc
  exact quotientRankAtLeast_mono step109wc187s5_contain hAct


private theorem step109wc187s6_QtInv :
    (codeMat 395 : Mat3).transpose⁻¹ = (codeMat 474 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 395 : Mat3).transpose * (codeMat 474 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc187s6_contain :
    (o187SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 117) (codeMat 395) o82W := by
  change spanCodes [262, 128, 86, 32, 10, 1] ≤ actionW (codeMat 117) (codeMat 395) o82W
  apply step109wc187_spanCodes_le_of_gens [262, 128, 86, 32, 10, 1]
    (actionW (codeMat 117) (codeMat 395) o82W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 324 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 324 (by decide)
    have hact : actionA (codeMat 117) (codeMat 395) (codeMat 324) = codeMat 262 := by
      unfold actionA
      rw [step109wc187s6_QtInv]
      show (codeMat 117 : Mat3).transpose * codeMat 324 * (codeMat 474 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 325 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 325 (by decide)
    have hact : actionA (codeMat 117) (codeMat 395) (codeMat 325) = codeMat 128 := by
      unfold actionA
      rw [step109wc187s6_QtInv]
      show (codeMat 117 : Mat3).transpose * codeMat 325 * (codeMat 474 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 494 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 494 (by decide)
    have hact : actionA (codeMat 117) (codeMat 395) (codeMat 494) = codeMat 86 := by
      unfold actionA
      rw [step109wc187s6_QtInv]
      show (codeMat 117 : Mat3).transpose * codeMat 494 * (codeMat 474 : Mat3).transpose = codeMat 86
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 292 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 292 (by decide)
    have hact : actionA (codeMat 117) (codeMat 395) (codeMat 292) = codeMat 32 := by
      unfold actionA
      rw [step109wc187s6_QtInv]
      show (codeMat 117 : Mat3).transpose * codeMat 292 * (codeMat 474 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 411 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 411 (by decide)
    have hact : actionA (codeMat 117) (codeMat 395) (codeMat 411) = codeMat 10 := by
      unfold actionA
      rw [step109wc187s6_QtInv]
      show (codeMat 117 : Mat3).transpose * codeMat 411 * (codeMat 474 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 192 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 192 (by decide)
    have hact : actionA (codeMat 117) (codeMat 395) (codeMat 192) = codeMat 1 := by
      unfold actionA
      rw [step109wc187s6_QtInv]
      show (codeMat 117 : Mat3).transpose * codeMat 192 * (codeMat 474 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact

theorem step109wc187s6Dispatch :
    QuotientRankAtLeast (o187SourceU_wc ⟨6, by omega⟩) 14 := by
  have hP : Invertible (codeMat 117 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 395 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 117) (codeMat 395) o82W) 14 :=
    @quotientRankAtLeast_action (codeMat 117) (codeMat 395) hP hQ o82W 14
      step99_orbit82_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc187s6_contain hAct


private theorem step109wc187s7_QtInv :
    (codeMat 114 : Mat3).transpose⁻¹ = (codeMat 204 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 114 : Mat3).transpose * (codeMat 204 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc187s7_contain :
    (o187SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 140) (codeMat 114) o43W_mono := by
  change spanCodes [256, 128, 32, 10, 6, 1] ≤ actionW (codeMat 140) (codeMat 114) o43W_mono
  apply step109wc187_spanCodes_le_of_gens [256, 128, 32, 10, 6, 1]
    (actionW (codeMat 140) (codeMat 114) o43W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 2 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 114) (codeMat 2) = codeMat 256 := by
      unfold actionA
      rw [step109wc187s7_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 204 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 3 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 140) (codeMat 114) (codeMat 3) = codeMat 128 := by
      unfold actionA
      rw [step109wc187s7_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 3 * (codeMat 204 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 128 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 140) (codeMat 114) (codeMat 128) = codeMat 32 := by
      unfold actionA
      rw [step109wc187s7_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 128 * (codeMat 204 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 280 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 280 (by decide)
    have hact : actionA (codeMat 140) (codeMat 114) (codeMat 280) = codeMat 10 := by
      unfold actionA
      rw [step109wc187s7_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 280 * (codeMat 204 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 140) (codeMat 114) (codeMat 8) = codeMat 6 := by
      unfold actionA
      rw [step109wc187s7_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 8 * (codeMat 204 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 140) (codeMat 114) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc187s7_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 32 * (codeMat 204 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact

theorem step109wc187s7Dispatch :
    QuotientRankAtLeast (o187SourceU_wc ⟨7, by omega⟩) 12 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 114 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 114) o43W_mono) 12 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 114) hP hQ o43W_mono 12
      orbit43_lb12_mono
  exact quotientRankAtLeast_mono step109wc187s7_contain hAct


private theorem step109wc187s8_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc187s8_contain :
    (o187SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 85) (codeMat 266) flatW_1 := by
  change spanCodes [260, 128, 64, 32, 16, 8, 2, 1] ≤ actionW (codeMat 85) (codeMat 266) flatW_1
  apply step109wc187_spanCodes_le_of_gens [260, 128, 64, 32, 16, 8, 2, 1]
    (actionW (codeMat 85) (codeMat 266) flatW_1)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 4 ∈ flatW_1 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 64, 32, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 85) (codeMat 266) (codeMat 4) = codeMat 260 := by
      unfold actionA
      rw [step109wc187s8_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 4 * (codeMat 266 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 65 ∈ flatW_1 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 64, 32, 16, 8, 4, 2, 1] 65 (by decide)
    have hact : actionA (codeMat 85) (codeMat 266) (codeMat 65) = codeMat 128 := by
      unfold actionA
      rw [step109wc187s8_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 65 * (codeMat 266 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 130 ∈ flatW_1 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 64, 32, 16, 8, 4, 2, 1] 130 (by decide)
    have hact : actionA (codeMat 85) (codeMat 266) (codeMat 130) = codeMat 64 := by
      unfold actionA
      rw [step109wc187s8_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 130 * (codeMat 266 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ flatW_1 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 64, 32, 16, 8, 4, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 85) (codeMat 266) (codeMat 32) = codeMat 32 := by
      unfold actionA
      rw [step109wc187s8_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 32 * (codeMat 266 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ flatW_1 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 64, 32, 16, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 85) (codeMat 266) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step109wc187s8_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ flatW_1 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 64, 32, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 85) (codeMat 266) (codeMat 16) = codeMat 8 := by
      unfold actionA
      rw [step109wc187s8_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 16 * (codeMat 266 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 64 ∈ flatW_1 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 64, 32, 16, 8, 4, 2, 1] 64 (by decide)
    have hact : actionA (codeMat 85) (codeMat 266) (codeMat 64) = codeMat 2 := by
      unfold actionA
      rw [step109wc187s8_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 64 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 128 ∈ flatW_1 :=
      spanContainsCodeCore_implies_mem_spanCodes [128, 64, 32, 16, 8, 4, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 85) (codeMat 266) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc187s8_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 128 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc187_codeMat_mem_actionW_of_witness hw hact

theorem step109wc187s8Dispatch :
    QuotientRankAtLeast (o187SourceU_wc ⟨8, by omega⟩) 3 := by
  have hP : Invertible (codeMat 85 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 85) (codeMat 266) flatW_1) 3 :=
    @quotientRankAtLeast_action (codeMat 85) (codeMat 266) hP hQ flatW_1 3
      flatSeed_1
  exact quotientRankAtLeast_mono step109wc187s8_contain hAct

theorem step109wc187_all_dispatch (i : Fin 9) :
    QuotientRankAtLeast (o187SourceU_wc i) (o187SourceLb_wc i) := by
  fin_cases i
  · exact step109wc187s0Dispatch
  · exact step109wc187s1Dispatch
  · exact step109wc187s2Dispatch
  · exact step109wc187s3Dispatch
  · exact step109wc187s4Dispatch
  · exact step109wc187s5Dispatch
  · exact step109wc187s6Dispatch
  · exact step109wc187s7Dispatch
  · exact step109wc187s8Dispatch

theorem step109_orbit187_lb15_wc : QuotientRankAtLeast o187W_wc 15 :=
  o187Lb15_wc step109wc187_all_dispatch

end QiushiMatmul
