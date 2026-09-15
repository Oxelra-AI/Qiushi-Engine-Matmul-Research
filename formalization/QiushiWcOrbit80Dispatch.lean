import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit80Consumer
import QiushiStep81Qdim2Generated
import QiushiOrbit14FP

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc80_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc80_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc80s0_QtInv :
    (codeMat 302 : Mat3).transpose⁻¹ = (codeMat 302 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 302 : Mat3).transpose * (codeMat 302 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc80s0_contain :
    (o80SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 87) (codeMat 302) step81o17s4Wspan := by
  change spanCodes [260, 134, 70, 38, 20, 10, 1] ≤ actionW (codeMat 87) (codeMat 302) step81o17s4Wspan
  apply step109wc80_spanCodes_le_of_gens [260, 134, 70, 38, 20, 10, 1]
    (actionW (codeMat 87) (codeMat 302) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 63 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 63 (by decide)
    have hact : actionA (codeMat 87) (codeMat 302) (codeMat 63) = codeMat 260 := by
      unfold actionA
      rw [step109wc80s0_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 63 * (codeMat 302 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 457 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 457 (by decide)
    have hact : actionA (codeMat 87) (codeMat 302) (codeMat 457) = codeMat 134 := by
      unfold actionA
      rw [step109wc80s0_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 457 * (codeMat 302 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 274 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 274 (by decide)
    have hact : actionA (codeMat 87) (codeMat 302) (codeMat 274) = codeMat 70 := by
      unfold actionA
      rw [step109wc80s0_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 274 * (codeMat 302 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 440 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 440 (by decide)
    have hact : actionA (codeMat 87) (codeMat 302) (codeMat 440) = codeMat 38 := by
      unfold actionA
      rw [step109wc80s0_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 440 * (codeMat 302 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 456 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 456 (by decide)
    have hact : actionA (codeMat 87) (codeMat 302) (codeMat 456) = codeMat 20 := by
      unfold actionA
      rw [step109wc80s0_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 456 * (codeMat 302 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 80 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 80 (by decide)
    have hact : actionA (codeMat 87) (codeMat 302) (codeMat 80) = codeMat 10 := by
      unfold actionA
      rw [step109wc80s0_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 80 * (codeMat 302 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 87) (codeMat 302) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc80s0_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 128 * (codeMat 302 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact

theorem step109wc80s0Dispatch :
    QuotientRankAtLeast (o80SourceU_wc ⟨0, by omega⟩) 14 := by
  have hP : Invertible (codeMat 87 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 302 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 87) (codeMat 302) step81o17s4Wspan) 14 :=
    @quotientRankAtLeast_action (codeMat 87) (codeMat 302) hP hQ step81o17s4Wspan 14
      step81o17s4Span_lb
  exact quotientRankAtLeast_mono step109wc80s0_contain hAct


private theorem step109wc80s1_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = (codeMat 275 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * (codeMat 275 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc80s1_contain :
    (o80SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 337) (codeMat 275) orbit14W := by
  change spanCodes [260, 160, 96, 20, 8, 2, 1] ≤ actionW (codeMat 337) (codeMat 275) orbit14W
  apply step109wc80_spanCodes_le_of_gens [260, 160, 96, 20, 8, 2, 1]
    (actionW (codeMat 337) (codeMat 275) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 337) (codeMat 275) (codeMat 256) = codeMat 260 := by
      unfold actionA
      rw [step109wc80s1_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 256 * (codeMat 275 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 227 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 227 (by decide)
    have hact : actionA (codeMat 337) (codeMat 275) (codeMat 227) = codeMat 160 := by
      unfold actionA
      rw [step109wc80s1_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 227 * (codeMat 275 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 97 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 97 (by decide)
    have hact : actionA (codeMat 337) (codeMat 275) (codeMat 97) = codeMat 96 := by
      unfold actionA
      rw [step109wc80s1_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 97 * (codeMat 275 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 28 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 28 (by decide)
    have hact : actionA (codeMat 337) (codeMat 275) (codeMat 28) = codeMat 20 := by
      unfold actionA
      rw [step109wc80s1_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 28 * (codeMat 275 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 337) (codeMat 275) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc80s1_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 8 * (codeMat 275 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 337) (codeMat 275) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc80s1_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 3 * (codeMat 275 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 337) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc80s1_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 1 * (codeMat 275 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact

theorem step109wc80s1Dispatch :
    QuotientRankAtLeast (o80SourceU_wc ⟨1, by omega⟩) 12 := by
  have hP : Invertible (codeMat 337 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 337) (codeMat 275) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 337) (codeMat 275) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc80s1_contain hAct


private theorem step109wc80s2_QtInv :
    (codeMat 226 : Mat3).transpose⁻¹ = (codeMat 141 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 226 : Mat3).transpose * (codeMat 141 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc80s2_contain :
    (o80SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 92) (codeMat 226) orbit14W := by
  change spanCodes [256, 160, 96, 16, 10, 4, 1] ≤ actionW (codeMat 92) (codeMat 226) orbit14W
  apply step109wc80_spanCodes_le_of_gens [256, 160, 96, 16, 10, 4, 1]
    (actionW (codeMat 92) (codeMat 226) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 92) (codeMat 226) (codeMat 2) = codeMat 256 := by
      unfold actionA
      rw [step109wc80s2_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 2 * (codeMat 141 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 149 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 149 (by decide)
    have hact : actionA (codeMat 92) (codeMat 226) (codeMat 149) = codeMat 160 := by
      unfold actionA
      rw [step109wc80s2_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 149 * (codeMat 141 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 148 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 148 (by decide)
    have hact : actionA (codeMat 92) (codeMat 226) (codeMat 148) = codeMat 96 := by
      unfold actionA
      rw [step109wc80s2_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 148 * (codeMat 141 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 92) (codeMat 226) (codeMat 360) = codeMat 16 := by
      unfold actionA
      rw [step109wc80s2_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 360 * (codeMat 141 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 92) (codeMat 226) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step109wc80s2_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 96 * (codeMat 141 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 92) (codeMat 226) (codeMat 128) = codeMat 4 := by
      unfold actionA
      rw [step109wc80s2_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 128 * (codeMat 141 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 92) (codeMat 226) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc80s2_QtInv]
      show (codeMat 92 : Mat3).transpose * codeMat 256 * (codeMat 141 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact

theorem step109wc80s2Dispatch :
    QuotientRankAtLeast (o80SourceU_wc ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 92 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 226 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 92) (codeMat 226) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 92) (codeMat 226) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc80s2_contain hAct


private theorem step109wc80s3_QtInv :
    (codeMat 486 : Mat3).transpose⁻¹ = (codeMat 157 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 486 : Mat3).transpose * (codeMat 157 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc80s3_contain :
    (o80SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 86) (codeMat 486) orbit14W := by
  change spanCodes [258, 160, 96, 18, 10, 6, 1] ≤ actionW (codeMat 86) (codeMat 486) orbit14W
  apply step109wc80_spanCodes_le_of_gens [258, 160, 96, 18, 10, 6, 1]
    (actionW (codeMat 86) (codeMat 486) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 383 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 383 (by decide)
    have hact : actionA (codeMat 86) (codeMat 486) (codeMat 383) = codeMat 258 := by
      unfold actionA
      rw [step109wc80s3_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 383 * (codeMat 157 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 21 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 21 (by decide)
    have hact : actionA (codeMat 86) (codeMat 486) (codeMat 21) = codeMat 160 := by
      unfold actionA
      rw [step109wc80s3_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 21 * (codeMat 157 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 28 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 28 (by decide)
    have hact : actionA (codeMat 86) (codeMat 486) (codeMat 28) = codeMat 96 := by
      unfold actionA
      rw [step109wc80s3_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 28 * (codeMat 157 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 86) (codeMat 486) (codeMat 360) = codeMat 18 := by
      unfold actionA
      rw [step109wc80s3_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 360 * (codeMat 157 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 352 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 352 (by decide)
    have hact : actionA (codeMat 86) (codeMat 486) (codeMat 352) = codeMat 10 := by
      unfold actionA
      rw [step109wc80s3_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 352 * (codeMat 157 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 86) (codeMat 486) (codeMat 128) = codeMat 6 := by
      unfold actionA
      rw [step109wc80s3_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 128 * (codeMat 157 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 86) (codeMat 486) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc80s3_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 256 * (codeMat 157 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact

theorem step109wc80s3Dispatch :
    QuotientRankAtLeast (o80SourceU_wc ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 486 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 86) (codeMat 486) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 86) (codeMat 486) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc80s3_contain hAct


private theorem step109wc80s4_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc80s4_contain :
    (o80SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 277) (codeMat 140) orbit14W := by
  change spanCodes [260, 128, 64, 32, 20, 10, 1] ≤ actionW (codeMat 277) (codeMat 140) orbit14W
  apply step109wc80_spanCodes_le_of_gens [260, 128, 64, 32, 20, 10, 1]
    (actionW (codeMat 277) (codeMat 140) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 277) (codeMat 140) (codeMat 1) = codeMat 260 := by
      unfold actionA
      rw [step109wc80s4_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 277) (codeMat 140) (codeMat 256) = codeMat 128 := by
      unfold actionA
      rw [step109wc80s4_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 256 * (codeMat 98 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 277) (codeMat 140) (codeMat 128) = codeMat 64 := by
      unfold actionA
      rw [step109wc80s4_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 128 * (codeMat 98 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 277) (codeMat 140) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc80s4_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 8 * (codeMat 98 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 97 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 97 (by decide)
    have hact : actionA (codeMat 277) (codeMat 140) (codeMat 97) = codeMat 20 := by
      unfold actionA
      rw [step109wc80s4_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 97 * (codeMat 98 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 276 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 276 (by decide)
    have hact : actionA (codeMat 277) (codeMat 140) (codeMat 276) = codeMat 10 := by
      unfold actionA
      rw [step109wc80s4_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 276 * (codeMat 98 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 130 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 130 (by decide)
    have hact : actionA (codeMat 277) (codeMat 140) (codeMat 130) = codeMat 1 := by
      unfold actionA
      rw [step109wc80s4_QtInv]
      show (codeMat 277 : Mat3).transpose * codeMat 130 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact

theorem step109wc80s4Dispatch :
    QuotientRankAtLeast (o80SourceU_wc ⟨4, by omega⟩) 12 := by
  have hP : Invertible (codeMat 277 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 277) (codeMat 140) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 277) (codeMat 140) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc80s4_contain hAct


private theorem step109wc80s5_QtInv :
    (codeMat 417 : Mat3).transpose⁻¹ = (codeMat 177 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 417 : Mat3).transpose * (codeMat 177 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc80s5_contain :
    (o80SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 334) (codeMat 417) orbit14W := by
  change spanCodes [260, 130, 66, 34, 20, 10, 1] ≤ actionW (codeMat 334) (codeMat 417) orbit14W
  apply step109wc80_spanCodes_le_of_gens [260, 130, 66, 34, 20, 10, 1]
    (actionW (codeMat 334) (codeMat 417) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 334) (codeMat 417) (codeMat 384) = codeMat 260 := by
      unfold actionA
      rw [step109wc80s5_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 384 * (codeMat 177 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 334) (codeMat 417) (codeMat 256) = codeMat 130 := by
      unfold actionA
      rw [step109wc80s5_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 256 * (codeMat 177 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 104 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 104 (by decide)
    have hact : actionA (codeMat 334) (codeMat 417) (codeMat 104) = codeMat 66 := by
      unfold actionA
      rw [step109wc80s5_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 104 * (codeMat 177 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 406 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 406 (by decide)
    have hact : actionA (codeMat 334) (codeMat 417) (codeMat 406) = codeMat 34 := by
      unfold actionA
      rw [step109wc80s5_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 406 * (codeMat 177 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 276 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 276 (by decide)
    have hact : actionA (codeMat 334) (codeMat 417) (codeMat 276) = codeMat 20 := by
      unfold actionA
      rw [step109wc80s5_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 276 * (codeMat 177 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 105 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 105 (by decide)
    have hact : actionA (codeMat 334) (codeMat 417) (codeMat 105) = codeMat 10 := by
      unfold actionA
      rw [step109wc80s5_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 105 * (codeMat 177 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 334) (codeMat 417) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc80s5_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 8 * (codeMat 177 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact

theorem step109wc80s5Dispatch :
    QuotientRankAtLeast (o80SourceU_wc ⟨5, by omega⟩) 12 := by
  have hP : Invertible (codeMat 334 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 334) (codeMat 417) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 334) (codeMat 417) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc80s5_contain hAct


private theorem step109wc80s6_QtInv :
    (codeMat 95 : Mat3).transpose⁻¹ = (codeMat 244 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 95 : Mat3).transpose * (codeMat 244 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc80s6_contain :
    (o80SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 286) (codeMat 95) orbit14W := by
  change spanCodes [260, 132, 68, 36, 20, 10, 1] ≤ actionW (codeMat 286) (codeMat 95) orbit14W
  apply step109wc80_spanCodes_le_of_gens [260, 132, 68, 36, 20, 10, 1]
    (actionW (codeMat 286) (codeMat 95) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 9 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 9 (by decide)
    have hact : actionA (codeMat 286) (codeMat 95) (codeMat 9) = codeMat 260 := by
      unfold actionA
      rw [step109wc80s6_QtInv]
      show (codeMat 286 : Mat3).transpose * codeMat 9 * (codeMat 244 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 137 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 137 (by decide)
    have hact : actionA (codeMat 286) (codeMat 95) (codeMat 137) = codeMat 132 := by
      unfold actionA
      rw [step109wc80s6_QtInv]
      show (codeMat 286 : Mat3).transpose * codeMat 137 * (codeMat 244 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 393 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 393 (by decide)
    have hact : actionA (codeMat 286) (codeMat 95) (codeMat 393) = codeMat 68 := by
      unfold actionA
      rw [step109wc80s6_QtInv]
      show (codeMat 286 : Mat3).transpose * codeMat 393 * (codeMat 244 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 286) (codeMat 95) (codeMat 8) = codeMat 36 := by
      unfold actionA
      rw [step109wc80s6_QtInv]
      show (codeMat 286 : Mat3).transpose * codeMat 8 * (codeMat 244 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 138 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 138 (by decide)
    have hact : actionA (codeMat 286) (codeMat 95) (codeMat 138) = codeMat 20 := by
      unfold actionA
      rw [step109wc80s6_QtInv]
      show (codeMat 286 : Mat3).transpose * codeMat 138 * (codeMat 244 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 284 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 284 (by decide)
    have hact : actionA (codeMat 286) (codeMat 95) (codeMat 284) = codeMat 10 := by
      unfold actionA
      rw [step109wc80s6_QtInv]
      show (codeMat 286 : Mat3).transpose * codeMat 284 * (codeMat 244 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 511 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 511 (by decide)
    have hact : actionA (codeMat 286) (codeMat 95) (codeMat 511) = codeMat 1 := by
      unfold actionA
      rw [step109wc80s6_QtInv]
      show (codeMat 286 : Mat3).transpose * codeMat 511 * (codeMat 244 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc80_codeMat_mem_actionW_of_witness hw hact

theorem step109wc80s6Dispatch :
    QuotientRankAtLeast (o80SourceU_wc ⟨6, by omega⟩) 12 := by
  have hP : Invertible (codeMat 286 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 95 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 286) (codeMat 95) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 286) (codeMat 95) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc80s6_contain hAct

theorem step109wc80_all_dispatch (i : Fin 7) :
    QuotientRankAtLeast (o80SourceU_wc i) (o80SourceLb_wc i) := by
  fin_cases i
  · exact step109wc80s0Dispatch
  · exact step109wc80s1Dispatch
  · exact step109wc80s2Dispatch
  · exact step109wc80s3Dispatch
  · exact step109wc80s4Dispatch
  · exact step109wc80s5Dispatch
  · exact step109wc80s6Dispatch

theorem step109_orbit80_lb15_wc : QuotientRankAtLeast o80W_wc 15 :=
  o80Lb15_wc step109wc80_all_dispatch

end QiushiMatmul
