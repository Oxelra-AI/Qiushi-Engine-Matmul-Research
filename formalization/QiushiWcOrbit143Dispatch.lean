import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit143Consumer
import QiushiOrbit41FP
import QiushiMonoOrbit43From14
import QiushiFlattenSeeds
import QiushiOrbit14FP

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc143_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc143_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc143s0_QtInv :
    (codeMat 163 : Mat3).transpose⁻¹ = (codeMat 165 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 163 : Mat3).transpose * (codeMat 165 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc143s0_contain :
    (o143SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 330) (codeMat 163) orbit41W := by
  change spanCodes [400, 84, 32, 8, 2, 1] ≤ actionW (codeMat 330) (codeMat 163) orbit41W
  apply step109wc143_spanCodes_le_of_gens [400, 84, 32, 8, 2, 1]
    (actionW (codeMat 330) (codeMat 163) orbit41W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 509 ∈ orbit41W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 384] 509 (by decide)
    have hact : actionA (codeMat 330) (codeMat 163) (codeMat 509) = codeMat 400 := by
      unfold actionA
      rw [step109wc143s0_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 509 * (codeMat 165 : Mat3).transpose = codeMat 400
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 93 ∈ orbit41W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 384] 93 (by decide)
    have hact : actionA (codeMat 330) (codeMat 163) (codeMat 93) = codeMat 84 := by
      unfold actionA
      rw [step109wc143s0_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 93 * (codeMat 165 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit41W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 384] 2 (by decide)
    have hact : actionA (codeMat 330) (codeMat 163) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [step109wc143s0_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 2 * (codeMat 165 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ orbit41W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 384] 1 (by decide)
    have hact : actionA (codeMat 330) (codeMat 163) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step109wc143s0_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 1 * (codeMat 165 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 40 ∈ orbit41W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 384] 40 (by decide)
    have hact : actionA (codeMat 330) (codeMat 163) (codeMat 40) = codeMat 2 := by
      unfold actionA
      rw [step109wc143s0_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 40 * (codeMat 165 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit41W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 384] 8 (by decide)
    have hact : actionA (codeMat 330) (codeMat 163) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc143s0_QtInv]
      show (codeMat 330 : Mat3).transpose * codeMat 8 * (codeMat 165 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact

theorem step109wc143s0Dispatch :
    QuotientRankAtLeast (o143SourceU_wc ⟨0, by omega⟩) 12 := by
  have hP : Invertible (codeMat 330 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 163 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 330) (codeMat 163) orbit41W) 12 :=
    @quotientRankAtLeast_action (codeMat 330) (codeMat 163) hP hQ orbit41W 12
      orbit41_lb12
  exact quotientRankAtLeast_mono step109wc143s0_contain hAct


private theorem step109wc143s1_QtInv :
    (codeMat 230 : Mat3).transpose⁻¹ = (codeMat 159 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 230 : Mat3).transpose * (codeMat 159 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc143s1_contain :
    (o143SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 458) (codeMat 230) o43W_mono := by
  change spanCodes [392, 76, 32, 24, 2, 1] ≤ actionW (codeMat 458) (codeMat 230) o43W_mono
  apply step109wc143_spanCodes_le_of_gens [392, 76, 32, 24, 2, 1]
    (actionW (codeMat 458) (codeMat 230) o43W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 434 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 434 (by decide)
    have hact : actionA (codeMat 458) (codeMat 230) (codeMat 434) = codeMat 392 := by
      unfold actionA
      rw [step109wc143s1_QtInv]
      show (codeMat 458 : Mat3).transpose * codeMat 434 * (codeMat 159 : Mat3).transpose = codeMat 392
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 312 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 312 (by decide)
    have hact : actionA (codeMat 458) (codeMat 230) (codeMat 312) = codeMat 76 := by
      unfold actionA
      rw [step109wc143s1_QtInv]
      show (codeMat 458 : Mat3).transpose * codeMat 312 * (codeMat 159 : Mat3).transpose = codeMat 76
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 3 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 458) (codeMat 230) (codeMat 3) = codeMat 32 := by
      unfold actionA
      rw [step109wc143s1_QtInv]
      show (codeMat 458 : Mat3).transpose * codeMat 3 * (codeMat 159 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 458) (codeMat 230) (codeMat 1) = codeMat 24 := by
      unfold actionA
      rw [step109wc143s1_QtInv]
      show (codeMat 458 : Mat3).transpose * codeMat 1 * (codeMat 159 : Mat3).transpose = codeMat 24
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 40 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 458) (codeMat 230) (codeMat 40) = codeMat 2 := by
      unfold actionA
      rw [step109wc143s1_QtInv]
      show (codeMat 458 : Mat3).transpose * codeMat 40 * (codeMat 159 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 458) (codeMat 230) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc143s1_QtInv]
      show (codeMat 458 : Mat3).transpose * codeMat 32 * (codeMat 159 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact

theorem step109wc143s1Dispatch :
    QuotientRankAtLeast (o143SourceU_wc ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 458 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 230 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 458) (codeMat 230) o43W_mono) 12 :=
    @quotientRankAtLeast_action (codeMat 458) (codeMat 230) hP hQ o43W_mono 12
      orbit43_lb12_mono
  exact quotientRankAtLeast_mono step109wc143s1_contain hAct


private theorem step109wc143s2_QtInv :
    (codeMat 481 : Mat3).transpose⁻¹ = (codeMat 185 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 481 : Mat3).transpose * (codeMat 185 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc143s2_contain :
    (o143SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 142) (codeMat 481) orbit41W := by
  change spanCodes [284, 140, 84, 32, 2, 1] ≤ actionW (codeMat 142) (codeMat 481) orbit41W
  apply step109wc143_spanCodes_le_of_gens [284, 140, 84, 32, 2, 1]
    (actionW (codeMat 142) (codeMat 481) orbit41W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 502 ∈ orbit41W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 384] 502 (by decide)
    have hact : actionA (codeMat 142) (codeMat 481) (codeMat 502) = codeMat 284 := by
      unfold actionA
      rw [step109wc143s2_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 502 * (codeMat 185 : Mat3).transpose = codeMat 284
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 116 ∈ orbit41W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 384] 116 (by decide)
    have hact : actionA (codeMat 142) (codeMat 481) (codeMat 116) = codeMat 140 := by
      unfold actionA
      rw [step109wc143s2_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 116 * (codeMat 185 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 117 ∈ orbit41W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 384] 117 (by decide)
    have hact : actionA (codeMat 142) (codeMat 481) (codeMat 117) = codeMat 84 := by
      unfold actionA
      rw [step109wc143s2_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 117 * (codeMat 185 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 384 ∈ orbit41W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 384] 384 (by decide)
    have hact : actionA (codeMat 142) (codeMat 481) (codeMat 384) = codeMat 32 := by
      unfold actionA
      rw [step109wc143s2_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 384 * (codeMat 185 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ orbit41W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 384] 32 (by decide)
    have hact : actionA (codeMat 142) (codeMat 481) (codeMat 32) = codeMat 2 := by
      unfold actionA
      rw [step109wc143s2_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 32 * (codeMat 185 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 40 ∈ orbit41W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84, 384] 40 (by decide)
    have hact : actionA (codeMat 142) (codeMat 481) (codeMat 40) = codeMat 1 := by
      unfold actionA
      rw [step109wc143s2_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 40 * (codeMat 185 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact

theorem step109wc143s2Dispatch :
    QuotientRankAtLeast (o143SourceU_wc ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 481 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 481) orbit41W) 12 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 481) hP hQ orbit41W 12
      orbit41_lb12
  exact quotientRankAtLeast_mono step109wc143s2_contain hAct


private theorem step109wc143s3_QtInv :
    (codeMat 225 : Mat3).transpose⁻¹ = (codeMat 169 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 225 : Mat3).transpose * (codeMat 169 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc143s3_contain :
    (o143SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 461) (codeMat 225) o43W_mono := by
  change spanCodes [260, 148, 84, 32, 2, 1] ≤ actionW (codeMat 461) (codeMat 225) o43W_mono
  apply step109wc143_spanCodes_le_of_gens [260, 148, 84, 32, 2, 1]
    (actionW (codeMat 461) (codeMat 225) o43W_mono)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 2 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 461) (codeMat 225) (codeMat 2) = codeMat 260 := by
      unfold actionA
      rw [step109wc143s3_QtInv]
      show (codeMat 461 : Mat3).transpose * codeMat 2 * (codeMat 169 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 304 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 304 (by decide)
    have hact : actionA (codeMat 461) (codeMat 225) (codeMat 304) = codeMat 148 := by
      unfold actionA
      rw [step109wc143s3_QtInv]
      show (codeMat 461 : Mat3).transpose * codeMat 304 * (codeMat 169 : Mat3).transpose = codeMat 148
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 313 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 313 (by decide)
    have hact : actionA (codeMat 461) (codeMat 225) (codeMat 313) = codeMat 84 := by
      unfold actionA
      rw [step109wc143s3_QtInv]
      show (codeMat 461 : Mat3).transpose * codeMat 313 * (codeMat 169 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 130 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 130 (by decide)
    have hact : actionA (codeMat 461) (codeMat 225) (codeMat 130) = codeMat 32 := by
      unfold actionA
      rw [step109wc143s3_QtInv]
      show (codeMat 461 : Mat3).transpose * codeMat 130 * (codeMat 169 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 461) (codeMat 225) (codeMat 32) = codeMat 2 := by
      unfold actionA
      rw [step109wc143s3_QtInv]
      show (codeMat 461 : Mat3).transpose * codeMat 32 * (codeMat 169 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 40 ∈ o43W_mono :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 128, 32, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 461) (codeMat 225) (codeMat 40) = codeMat 1 := by
      unfold actionA
      rw [step109wc143s3_QtInv]
      show (codeMat 461 : Mat3).transpose * codeMat 40 * (codeMat 169 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact

theorem step109wc143s3Dispatch :
    QuotientRankAtLeast (o143SourceU_wc ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 461 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 461) (codeMat 225) o43W_mono) 12 :=
    @quotientRankAtLeast_action (codeMat 461) (codeMat 225) hP hQ o43W_mono 12
      orbit43_lb12_mono
  exact quotientRankAtLeast_mono step109wc143s3_contain hAct


private theorem step109wc143s4_QtInv :
    (codeMat 330 : Mat3).transpose⁻¹ = (codeMat 394 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 330 : Mat3).transpose * (codeMat 394 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc143s4_contain :
    (o143SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 161) (codeMat 330) flatW_7 := by
  change spanCodes [272, 128, 80, 32, 4, 2, 1] ≤ actionW (codeMat 161) (codeMat 330) flatW_7
  apply step109wc143_spanCodes_le_of_gens [272, 128, 80, 32, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 330) flatW_7)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 96 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 96 (by decide)
    have hact : actionA (codeMat 161) (codeMat 330) (codeMat 96) = codeMat 272 := by
      unfold actionA
      rw [step109wc143s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 96 * (codeMat 394 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 330) (codeMat 8) = codeMat 128 := by
      unfold actionA
      rw [step109wc143s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 394 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 112 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 112 (by decide)
    have hact : actionA (codeMat 161) (codeMat 330) (codeMat 112) = codeMat 80 := by
      unfold actionA
      rw [step109wc143s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 112 * (codeMat 394 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 330) (codeMat 256) = codeMat 32 := by
      unfold actionA
      rw [step109wc143s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 394 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 4 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 161) (codeMat 330) (codeMat 4) = codeMat 4 := by
      unfold actionA
      rw [step109wc143s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 4 * (codeMat 394 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 330) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step109wc143s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 394 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 6 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 6 (by decide)
    have hact : actionA (codeMat 161) (codeMat 330) (codeMat 6) = codeMat 1 := by
      unfold actionA
      rw [step109wc143s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 6 * (codeMat 394 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact

theorem step109wc143s4Dispatch :
    QuotientRankAtLeast (o143SourceU_wc ⟨4, by omega⟩) 9 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 330 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 330) flatW_7) 9 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 330) hP hQ flatW_7 9
      flatSeed_7
  exact quotientRankAtLeast_mono step109wc143s4_contain hAct


private theorem step109wc143s5_QtInv :
    (codeMat 412 : Mat3).transpose⁻¹ = (codeMat 111 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 412 : Mat3).transpose * (codeMat 111 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc143s5_contain :
    (o143SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 94) (codeMat 412) orbit14W := by
  change spanCodes [264, 132, 72, 32, 28, 2, 1] ≤ actionW (codeMat 94) (codeMat 412) orbit14W
  apply step109wc143_spanCodes_le_of_gens [264, 132, 72, 32, 28, 2, 1]
    (actionW (codeMat 94) (codeMat 412) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 509 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 509 (by decide)
    have hact : actionA (codeMat 94) (codeMat 412) (codeMat 509) = codeMat 264 := by
      unfold actionA
      rw [step109wc143s5_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 509 * (codeMat 111 : Mat3).transpose = codeMat 264
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 246 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 246 (by decide)
    have hact : actionA (codeMat 94) (codeMat 412) (codeMat 246) = codeMat 132 := by
      unfold actionA
      rw [step109wc143s5_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 246 * (codeMat 111 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 94) (codeMat 412) (codeMat 2) = codeMat 72 := by
      unfold actionA
      rw [step109wc143s5_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 2 * (codeMat 111 : Mat3).transpose = codeMat 72
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 94) (codeMat 412) (codeMat 360) = codeMat 32 := by
      unfold actionA
      rw [step109wc143s5_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 360 * (codeMat 111 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 94) (codeMat 412) (codeMat 96) = codeMat 28 := by
      unfold actionA
      rw [step109wc143s5_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 96 * (codeMat 111 : Mat3).transpose = codeMat 28
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 94) (codeMat 412) (codeMat 384) = codeMat 2 := by
      unfold actionA
      rw [step109wc143s5_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 384 * (codeMat 111 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 94) (codeMat 412) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc143s5_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 128 * (codeMat 111 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact

theorem step109wc143s5Dispatch :
    QuotientRankAtLeast (o143SourceU_wc ⟨5, by omega⟩) 12 := by
  have hP : Invertible (codeMat 94 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 412 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 94) (codeMat 412) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 94) (codeMat 412) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc143s5_contain hAct


private theorem step109wc143s6_QtInv :
    (codeMat 116 : Mat3).transpose⁻¹ = (codeMat 92 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 116 : Mat3).transpose * (codeMat 92 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc143s6_contain :
    (o143SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 98) (codeMat 116) orbit14W := by
  change spanCodes [264, 136, 68, 32, 16, 2, 1] ≤ actionW (codeMat 98) (codeMat 116) orbit14W
  apply step109wc143_spanCodes_le_of_gens [264, 136, 68, 32, 16, 2, 1]
    (actionW (codeMat 98) (codeMat 116) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 28 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 28 (by decide)
    have hact : actionA (codeMat 98) (codeMat 116) (codeMat 28) = codeMat 264 := by
      unfold actionA
      rw [step109wc143s6_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 28 * (codeMat 92 : Mat3).transpose = codeMat 264
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 20 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 20 (by decide)
    have hact : actionA (codeMat 98) (codeMat 116) (codeMat 20) = codeMat 136 := by
      unfold actionA
      rw [step109wc143s6_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 20 * (codeMat 92 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 224 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 224 (by decide)
    have hact : actionA (codeMat 98) (codeMat 116) (codeMat 224) = codeMat 68 := by
      unfold actionA
      rw [step109wc143s6_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 224 * (codeMat 92 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 98) (codeMat 116) (codeMat 3) = codeMat 32 := by
      unfold actionA
      rw [step109wc143s6_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 3 * (codeMat 92 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 98) (codeMat 116) (codeMat 2) = codeMat 16 := by
      unfold actionA
      rw [step109wc143s6_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 2 * (codeMat 92 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 98) (codeMat 116) (codeMat 128) = codeMat 2 := by
      unfold actionA
      rw [step109wc143s6_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 128 * (codeMat 92 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 98) (codeMat 116) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc143s6_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 256 * (codeMat 92 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact

theorem step109wc143s6Dispatch :
    QuotientRankAtLeast (o143SourceU_wc ⟨6, by omega⟩) 12 := by
  have hP : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 116 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 98) (codeMat 116) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 98) (codeMat 116) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc143s6_contain hAct


private theorem step109wc143s7_QtInv :
    (codeMat 396 : Mat3).transpose⁻¹ = (codeMat 106 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 396 : Mat3).transpose * (codeMat 106 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc143s7_contain :
    (o143SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 93) (codeMat 396) orbit14W := by
  change spanCodes [268, 136, 64, 32, 20, 2, 1] ≤ actionW (codeMat 93) (codeMat 396) orbit14W
  apply step109wc143_spanCodes_le_of_gens [268, 136, 64, 32, 20, 2, 1]
    (actionW (codeMat 93) (codeMat 396) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 149 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 149 (by decide)
    have hact : actionA (codeMat 93) (codeMat 396) (codeMat 149) = codeMat 268 := by
      unfold actionA
      rw [step109wc143s7_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 149 * (codeMat 106 : Mat3).transpose = codeMat 268
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 404 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 404 (by decide)
    have hact : actionA (codeMat 93) (codeMat 396) (codeMat 404) = codeMat 136 := by
      unfold actionA
      rw [step109wc143s7_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 404 * (codeMat 106 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 130 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 130 (by decide)
    have hact : actionA (codeMat 93) (codeMat 396) (codeMat 130) = codeMat 64 := by
      unfold actionA
      rw [step109wc143s7_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 130 * (codeMat 106 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 93) (codeMat 396) (codeMat 360) = codeMat 32 := by
      unfold actionA
      rw [step109wc143s7_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 360 * (codeMat 106 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 93) (codeMat 396) (codeMat 96) = codeMat 20 := by
      unfold actionA
      rw [step109wc143s7_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 96 * (codeMat 106 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 93) (codeMat 396) (codeMat 256) = codeMat 2 := by
      unfold actionA
      rw [step109wc143s7_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 256 * (codeMat 106 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 93) (codeMat 396) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc143s7_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 128 * (codeMat 106 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact

theorem step109wc143s7Dispatch :
    QuotientRankAtLeast (o143SourceU_wc ⟨7, by omega⟩) 12 := by
  have hP : Invertible (codeMat 93 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 396 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 93) (codeMat 396) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 93) (codeMat 396) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc143s7_contain hAct


private theorem step109wc143s8_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc143s8_contain :
    (o143SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 86) (codeMat 84) orbit14W := by
  change spanCodes [256, 144, 84, 32, 12, 2, 1] ≤ actionW (codeMat 86) (codeMat 84) orbit14W
  apply step109wc143_spanCodes_le_of_gens [256, 144, 84, 32, 12, 2, 1]
    (actionW (codeMat 86) (codeMat 84) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 9 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 9 (by decide)
    have hact : actionA (codeMat 86) (codeMat 84) (codeMat 9) = codeMat 256 := by
      unfold actionA
      rw [step109wc143s8_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 9 * (codeMat 84 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 86) (codeMat 84) (codeMat 2) = codeMat 144 := by
      unfold actionA
      rw [step109wc143s8_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 116 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 116 (by decide)
    have hact : actionA (codeMat 86) (codeMat 84) (codeMat 116) = codeMat 84 := by
      unfold actionA
      rw [step109wc143s8_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 116 * (codeMat 84 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 86) (codeMat 84) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc143s8_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 8 * (codeMat 84 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 86) (codeMat 84) (codeMat 96) = codeMat 12 := by
      unfold actionA
      rw [step109wc143s8_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 96 * (codeMat 84 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 86) (codeMat 84) (codeMat 128) = codeMat 2 := by
      unfold actionA
      rw [step109wc143s8_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 128 * (codeMat 84 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 86) (codeMat 84) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc143s8_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 256 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc143_codeMat_mem_actionW_of_witness hw hact

theorem step109wc143s8Dispatch :
    QuotientRankAtLeast (o143SourceU_wc ⟨8, by omega⟩) 12 := by
  have hP : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 86) (codeMat 84) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 86) (codeMat 84) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc143s8_contain hAct

theorem step109wc143_all_dispatch (i : Fin 9) :
    QuotientRankAtLeast (o143SourceU_wc i) (o143SourceLb_wc i) := by
  fin_cases i
  · exact step109wc143s0Dispatch
  · exact step109wc143s1Dispatch
  · exact step109wc143s2Dispatch
  · exact step109wc143s3Dispatch
  · exact step109wc143s4Dispatch
  · exact step109wc143s5Dispatch
  · exact step109wc143s6Dispatch
  · exact step109wc143s7Dispatch
  · exact step109wc143s8Dispatch

theorem step109_orbit143_lb14_wc : QuotientRankAtLeast o143W_wc 14 :=
  o143Lb14_wc step109wc143_all_dispatch

end QiushiMatmul
