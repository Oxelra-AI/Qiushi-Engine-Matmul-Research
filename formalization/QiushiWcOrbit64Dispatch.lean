import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit64Consumer
import QiushiOrbit10FP
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc64_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc64_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc64s0_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc64s0_contain :
    (o64SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 266) (codeMat 266) orbit10W := by
  change spanCodes [256, 160, 68, 16, 8, 2, 1] ≤ actionW (codeMat 266) (codeMat 266) orbit10W
  apply step109wc64_spanCodes_le_of_gens [256, 160, 68, 16, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 266) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step109wc64s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 256 * (codeMat 266 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 68) = codeMat 160 := by
      unfold actionA
      rw [step109wc64s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 68 * (codeMat 266 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 160) = codeMat 68 := by
      unfold actionA
      rw [step109wc64s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 160 * (codeMat 266 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc64s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 2) = codeMat 8 := by
      unfold actionA
      rw [step109wc64s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 8) = codeMat 2 := by
      unfold actionA
      rw [step109wc64s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc64s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact

theorem step109wc64s0Dispatch :
    QuotientRankAtLeast (o64SourceU_wc ⟨0, by omega⟩) 12 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 266) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 266) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc64s0_contain hAct


private theorem step109wc64s1_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc64s1_contain :
    (o64SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 84) (codeMat 266) flatW_3 := by
  change spanCodes [258, 128, 64, 32, 16, 10, 4, 1] ≤ actionW (codeMat 84) (codeMat 266) flatW_3
  apply step109wc64_spanCodes_le_of_gens [258, 128, 64, 32, 16, 10, 4, 1]
    (actionW (codeMat 84) (codeMat 266) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 68 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 68 (by decide)
    have hact : actionA (codeMat 84) (codeMat 266) (codeMat 68) = codeMat 258 := by
      unfold actionA
      rw [step109wc64s1_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 68 * (codeMat 266 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 266) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step109wc64s1_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 266) (codeMat 2) = codeMat 64 := by
      unfold actionA
      rw [step109wc64s1_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 84) (codeMat 266) (codeMat 32) = codeMat 32 := by
      unfold actionA
      rw [step109wc64s1_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 32 * (codeMat 266 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 266) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step109wc64s1_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 80 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 84) (codeMat 266) (codeMat 80) = codeMat 10 := by
      unfold actionA
      rw [step109wc64s1_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 80 * (codeMat 266 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 266) (codeMat 256) = codeMat 4 := by
      unfold actionA
      rw [step109wc64s1_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 266 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 266) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc64s1_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact

theorem step109wc64s1Dispatch :
    QuotientRankAtLeast (o64SourceU_wc ⟨1, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 266) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 266) hP hQ flatW_3 9
      flatSeed_3
  exact quotientRankAtLeast_mono step109wc64s1_contain hAct


private theorem step109wc64s2_QtInv :
    (codeMat 494 : Mat3).transpose⁻¹ = (codeMat 501 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 494 : Mat3).transpose * (codeMat 501 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc64s2_contain :
    (o64SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 84) (codeMat 494) flatW_3 := by
  change spanCodes [258, 130, 66, 34, 16, 10, 6, 1] ≤ actionW (codeMat 84) (codeMat 494) flatW_3
  apply step109wc64_spanCodes_le_of_gens [258, 130, 66, 34, 16, 10, 6, 1]
    (actionW (codeMat 84) (codeMat 494) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 327 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 327 (by decide)
    have hact : actionA (codeMat 84) (codeMat 494) (codeMat 327) = codeMat 258 := by
      unfold actionA
      rw [step109wc64s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 327 * (codeMat 501 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 325 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 325 (by decide)
    have hact : actionA (codeMat 84) (codeMat 494) (codeMat 325) = codeMat 130 := by
      unfold actionA
      rw [step109wc64s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 325 * (codeMat 501 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 326 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 326 (by decide)
    have hact : actionA (codeMat 84) (codeMat 494) (codeMat 326) = codeMat 66 := by
      unfold actionA
      rw [step109wc64s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 326 * (codeMat 501 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 376 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 376 (by decide)
    have hact : actionA (codeMat 84) (codeMat 494) (codeMat 376) = codeMat 34 := by
      unfold actionA
      rw [step109wc64s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 376 * (codeMat 501 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 40 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 84) (codeMat 494) (codeMat 40) = codeMat 16 := by
      unfold actionA
      rw [step109wc64s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 501 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 368 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 368 (by decide)
    have hact : actionA (codeMat 84) (codeMat 494) (codeMat 368) = codeMat 10 := by
      unfold actionA
      rw [step109wc64s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 368 * (codeMat 501 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 494) (codeMat 128) = codeMat 6 := by
      unfold actionA
      rw [step109wc64s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 501 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 494) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step109wc64s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 501 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact

theorem step109wc64s2Dispatch :
    QuotientRankAtLeast (o64SourceU_wc ⟨2, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 494 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 494) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 494) hP hQ flatW_3 9
      flatSeed_3
  exact quotientRankAtLeast_mono step109wc64s2_contain hAct


private theorem step109wc64s3_QtInv :
    (codeMat 334 : Mat3).transpose⁻¹ = (codeMat 442 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 334 : Mat3).transpose * (codeMat 442 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc64s3_contain :
    (o64SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 84) (codeMat 334) flatW_3 := by
  change spanCodes [258, 128, 66, 32, 16, 10, 6, 1] ≤ actionW (codeMat 84) (codeMat 334) flatW_3
  apply step109wc64_spanCodes_le_of_gens [258, 128, 66, 32, 16, 10, 6, 1]
    (actionW (codeMat 84) (codeMat 334) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 69 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 69 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 69) = codeMat 258 := by
      unfold actionA
      rw [step109wc64s3_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 69 * (codeMat 442 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step109wc64s3_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 442 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 70 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 70 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 70) = codeMat 66 := by
      unfold actionA
      rw [step109wc64s3_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 70 * (codeMat 442 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 40 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 40) = codeMat 32 := by
      unfold actionA
      rw [step109wc64s3_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 442 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step109wc64s3_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 442 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 112 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 112 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 112) = codeMat 10 := by
      unfold actionA
      rw [step109wc64s3_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 112 * (codeMat 442 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 256) = codeMat 6 := by
      unfold actionA
      rw [step109wc64s3_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 442 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 334) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step109wc64s3_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 442 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact

theorem step109wc64s3Dispatch :
    QuotientRankAtLeast (o64SourceU_wc ⟨3, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 334 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 334) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 334) hP hQ flatW_3 9
      flatSeed_3
  exact quotientRankAtLeast_mono step109wc64s3_contain hAct


private theorem step109wc64s4_QtInv :
    (codeMat 426 : Mat3).transpose⁻¹ = (codeMat 335 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 426 : Mat3).transpose * (codeMat 335 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc64s4_contain :
    (o64SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 84) (codeMat 426) flatW_3 := by
  change spanCodes [258, 130, 64, 34, 16, 10, 4, 1] ≤ actionW (codeMat 84) (codeMat 426) flatW_3
  apply step109wc64_spanCodes_le_of_gens [258, 130, 64, 34, 16, 10, 4, 1]
    (actionW (codeMat 84) (codeMat 426) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 326 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 326 (by decide)
    have hact : actionA (codeMat 84) (codeMat 426) (codeMat 326) = codeMat 258 := by
      unfold actionA
      rw [step109wc64s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 326 * (codeMat 335 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 325 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 325 (by decide)
    have hact : actionA (codeMat 84) (codeMat 426) (codeMat 325) = codeMat 130 := by
      unfold actionA
      rw [step109wc64s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 325 * (codeMat 335 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 426) (codeMat 2) = codeMat 64 := by
      unfold actionA
      rw [step109wc64s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 335 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 368 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 368 (by decide)
    have hact : actionA (codeMat 84) (codeMat 426) (codeMat 368) = codeMat 34 := by
      unfold actionA
      rw [step109wc64s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 368 * (codeMat 335 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 40 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 84) (codeMat 426) (codeMat 40) = codeMat 16 := by
      unfold actionA
      rw [step109wc64s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 335 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 336 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 336 (by decide)
    have hact : actionA (codeMat 84) (codeMat 426) (codeMat 336) = codeMat 10 := by
      unfold actionA
      rw [step109wc64s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 336 * (codeMat 335 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 426) (codeMat 384) = codeMat 4 := by
      unfold actionA
      rw [step109wc64s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 335 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 426) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc64s4_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 335 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc64_codeMat_mem_actionW_of_witness hw hact

theorem step109wc64s4Dispatch :
    QuotientRankAtLeast (o64SourceU_wc ⟨4, by omega⟩) 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 426 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 426) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 426) hP hQ flatW_3 9
      flatSeed_3
  exact quotientRankAtLeast_mono step109wc64s4_contain hAct

theorem step109wc64_all_dispatch (i : Fin 5) :
    QuotientRankAtLeast (o64SourceU_wc i) (o64SourceLb_wc i) := by
  fin_cases i
  · exact step109wc64s0Dispatch
  · exact step109wc64s1Dispatch
  · exact step109wc64s2Dispatch
  · exact step109wc64s3Dispatch
  · exact step109wc64s4Dispatch

theorem step109_orbit64_lb15_wc : QuotientRankAtLeast o64W_wc 15 :=
  o64Lb15_wc step109wc64_all_dispatch

end QiushiMatmul
