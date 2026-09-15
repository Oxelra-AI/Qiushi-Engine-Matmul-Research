import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit81Consumer
import QiushiStep81Qdim2Generated
import QiushiOrbit14FP
import QiushiWcOrbit16Dispatch
import QiushiOrbit13FP

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc81_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc81_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc81s0_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc81s0_contain :
    (o81SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 94) (codeMat 266) step81o17s4Wspan := by
  change spanCodes [262, 132, 68, 36, 20, 10, 1] ≤ actionW (codeMat 94) (codeMat 266) step81o17s4Wspan
  apply step109wc81_spanCodes_le_of_gens [262, 132, 68, 36, 20, 10, 1]
    (actionW (codeMat 94) (codeMat 266) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 100 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 100 (by decide)
    have hact : actionA (codeMat 94) (codeMat 266) (codeMat 100) = codeMat 262 := by
      unfold actionA
      rw [step109wc81s0_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 100 * (codeMat 266 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 329 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 329 (by decide)
    have hact : actionA (codeMat 94) (codeMat 266) (codeMat 329) = codeMat 132 := by
      unfold actionA
      rw [step109wc81s0_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 329 * (codeMat 266 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 402 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 402 (by decide)
    have hact : actionA (codeMat 94) (codeMat 266) (codeMat 402) = codeMat 68 := by
      unfold actionA
      rw [step109wc81s0_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 402 * (codeMat 266 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 94) (codeMat 266) (codeMat 32) = codeMat 36 := by
      unfold actionA
      rw [step109wc81s0_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 32 * (codeMat 266 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 328 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 328 (by decide)
    have hact : actionA (codeMat 94) (codeMat 266) (codeMat 328) = codeMat 20 := by
      unfold actionA
      rw [step109wc81s0_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 328 * (codeMat 266 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 208 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 208 (by decide)
    have hact : actionA (codeMat 94) (codeMat 266) (codeMat 208) = codeMat 10 := by
      unfold actionA
      rw [step109wc81s0_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 208 * (codeMat 266 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 94) (codeMat 266) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc81s0_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 128 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact

theorem step109wc81s0Dispatch :
    QuotientRankAtLeast (o81SourceU_wc ⟨0, by omega⟩) 14 := by
  have hP : Invertible (codeMat 94 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 94) (codeMat 266) step81o17s4Wspan) 14 :=
    @quotientRankAtLeast_action (codeMat 94) (codeMat 266) hP hQ step81o17s4Wspan 14
      step81o17s4Span_lb
  exact quotientRankAtLeast_mono step109wc81s0_contain hAct


private theorem step109wc81s1_QtInv :
    (codeMat 302 : Mat3).transpose⁻¹ = (codeMat 302 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 302 : Mat3).transpose * (codeMat 302 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc81s1_contain :
    (o81SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 87) (codeMat 302) step81o17s4Wspan := by
  change spanCodes [260, 134, 70, 38, 20, 10, 1] ≤ actionW (codeMat 87) (codeMat 302) step81o17s4Wspan
  apply step109wc81_spanCodes_le_of_gens [260, 134, 70, 38, 20, 10, 1]
    (actionW (codeMat 87) (codeMat 302) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 63 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 63 (by decide)
    have hact : actionA (codeMat 87) (codeMat 302) (codeMat 63) = codeMat 260 := by
      unfold actionA
      rw [step109wc81s1_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 63 * (codeMat 302 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 457 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 457 (by decide)
    have hact : actionA (codeMat 87) (codeMat 302) (codeMat 457) = codeMat 134 := by
      unfold actionA
      rw [step109wc81s1_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 457 * (codeMat 302 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 274 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 274 (by decide)
    have hact : actionA (codeMat 87) (codeMat 302) (codeMat 274) = codeMat 70 := by
      unfold actionA
      rw [step109wc81s1_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 274 * (codeMat 302 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 440 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 440 (by decide)
    have hact : actionA (codeMat 87) (codeMat 302) (codeMat 440) = codeMat 38 := by
      unfold actionA
      rw [step109wc81s1_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 440 * (codeMat 302 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 456 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 456 (by decide)
    have hact : actionA (codeMat 87) (codeMat 302) (codeMat 456) = codeMat 20 := by
      unfold actionA
      rw [step109wc81s1_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 456 * (codeMat 302 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 80 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 80 (by decide)
    have hact : actionA (codeMat 87) (codeMat 302) (codeMat 80) = codeMat 10 := by
      unfold actionA
      rw [step109wc81s1_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 80 * (codeMat 302 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 87) (codeMat 302) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc81s1_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 128 * (codeMat 302 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact

theorem step109wc81s1Dispatch :
    QuotientRankAtLeast (o81SourceU_wc ⟨1, by omega⟩) 14 := by
  have hP : Invertible (codeMat 87 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 302 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 87) (codeMat 302) step81o17s4Wspan) 14 :=
    @quotientRankAtLeast_action (codeMat 87) (codeMat 302) hP hQ step81o17s4Wspan 14
      step81o17s4Span_lb
  exact quotientRankAtLeast_mono step109wc81s1_contain hAct


private theorem step109wc81s2_QtInv :
    (codeMat 279 : Mat3).transpose⁻¹ = (codeMat 279 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 279 : Mat3).transpose * (codeMat 279 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc81s2_contain :
    (o81SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 273) (codeMat 279) orbit14W := by
  change spanCodes [288, 160, 96, 20, 8, 2, 1] ≤ actionW (codeMat 273) (codeMat 279) orbit14W
  apply step109wc81_spanCodes_le_of_gens [288, 160, 96, 20, 8, 2, 1]
    (actionW (codeMat 273) (codeMat 279) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 273) (codeMat 279) (codeMat 360) = codeMat 288 := by
      unfold actionA
      rw [step109wc81s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 360 * (codeMat 279 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 232 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 232 (by decide)
    have hact : actionA (codeMat 273) (codeMat 279) (codeMat 232) = codeMat 160 := by
      unfold actionA
      rw [step109wc81s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 232 * (codeMat 279 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 104 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 104 (by decide)
    have hact : actionA (codeMat 273) (codeMat 279) (codeMat 104) = codeMat 96 := by
      unfold actionA
      rw [step109wc81s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 104 * (codeMat 279 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 29 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 29 (by decide)
    have hact : actionA (codeMat 273) (codeMat 279) (codeMat 29) = codeMat 20 := by
      unfold actionA
      rw [step109wc81s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 29 * (codeMat 279 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 279) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc81s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 279 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 273) (codeMat 279) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [step109wc81s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 3 * (codeMat 279 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 279) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc81s2_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 279 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact

theorem step109wc81s2Dispatch :
    QuotientRankAtLeast (o81SourceU_wc ⟨2, by omega⟩) 12 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 279 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 279) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 279) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono step109wc81s2_contain hAct


private theorem step109wc81s3_QtInv :
    (codeMat 187 : Mat3).transpose⁻¹ = (codeMat 229 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 187 : Mat3).transpose * (codeMat 229 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc81s3_contain :
    (o81SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 225) (codeMat 187) o16W_wc := by
  change spanCodes [290, 160, 96, 16, 10, 4, 1] ≤ actionW (codeMat 225) (codeMat 187) o16W_wc
  apply step109wc81_spanCodes_le_of_gens [290, 160, 96, 16, 10, 4, 1]
    (actionW (codeMat 225) (codeMat 187) o16W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 149 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 149 (by decide)
    have hact : actionA (codeMat 225) (codeMat 187) (codeMat 149) = codeMat 290 := by
      unfold actionA
      rw [step109wc81s3_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 149 * (codeMat 229 : Mat3).transpose = codeMat 290
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 186 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 186 (by decide)
    have hact : actionA (codeMat 225) (codeMat 187) (codeMat 186) = codeMat 160 := by
      unfold actionA
      rw [step109wc81s3_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 186 * (codeMat 229 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 154 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 154 (by decide)
    have hact : actionA (codeMat 225) (codeMat 187) (codeMat 154) = codeMat 96 := by
      unfold actionA
      rw [step109wc81s3_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 154 * (codeMat 229 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 455 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 455 (by decide)
    have hact : actionA (codeMat 225) (codeMat 187) (codeMat 455) = codeMat 16 := by
      unfold actionA
      rw [step109wc81s3_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 455 * (codeMat 229 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 196 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 196 (by decide)
    have hact : actionA (codeMat 225) (codeMat 187) (codeMat 196) = codeMat 10 := by
      unfold actionA
      rw [step109wc81s3_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 196 * (codeMat 229 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 225) (codeMat 187) (codeMat 2) = codeMat 4 := by
      unfold actionA
      rw [step109wc81s3_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 2 * (codeMat 229 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 225) (codeMat 187) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step109wc81s3_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 3 * (codeMat 229 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact

theorem step109wc81s3Dispatch :
    QuotientRankAtLeast (o81SourceU_wc ⟨3, by omega⟩) 12 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 187 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 187) o16W_wc) 12 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 187) hP hQ o16W_wc 12
      step109_orbit16_lb12_wc
  exact quotientRankAtLeast_mono step109wc81s3_contain hAct


private theorem step109wc81s4_QtInv :
    (codeMat 443 : Mat3).transpose⁻¹ = (codeMat 254 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 443 : Mat3).transpose * (codeMat 254 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc81s4_contain :
    (o81SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 161) (codeMat 443) o16W_wc := by
  change spanCodes [290, 160, 96, 18, 10, 6, 1] ≤ actionW (codeMat 161) (codeMat 443) o16W_wc
  apply step109wc81_spanCodes_le_of_gens [290, 160, 96, 18, 10, 6, 1]
    (actionW (codeMat 161) (codeMat 443) o16W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 439 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 439 (by decide)
    have hact : actionA (codeMat 161) (codeMat 443) (codeMat 439) = codeMat 290 := by
      unfold actionA
      rw [step109wc81s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 439 * (codeMat 254 : Mat3).transpose = codeMat 290
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 440 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 440 (by decide)
    have hact : actionA (codeMat 161) (codeMat 443) (codeMat 440) = codeMat 160 := by
      unfold actionA
      rw [step109wc81s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 440 * (codeMat 254 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 408 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 408 (by decide)
    have hact : actionA (codeMat 161) (codeMat 443) (codeMat 408) = codeMat 96 := by
      unfold actionA
      rw [step109wc81s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 408 * (codeMat 254 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 455 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 455 (by decide)
    have hact : actionA (codeMat 161) (codeMat 443) (codeMat 455) = codeMat 18 := by
      unfold actionA
      rw [step109wc81s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 455 * (codeMat 254 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 199 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 199 (by decide)
    have hact : actionA (codeMat 161) (codeMat 443) (codeMat 199) = codeMat 10 := by
      unfold actionA
      rw [step109wc81s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 199 * (codeMat 254 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 443) (codeMat 1) = codeMat 6 := by
      unfold actionA
      rw [step109wc81s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 254 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 161) (codeMat 443) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step109wc81s4_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 3 * (codeMat 254 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact

theorem step109wc81s4Dispatch :
    QuotientRankAtLeast (o81SourceU_wc ⟨4, by omega⟩) 12 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 443 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 443) o16W_wc) 12 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 443) hP hQ o16W_wc 12
      step109_orbit16_lb12_wc
  exact quotientRankAtLeast_mono step109wc81s4_contain hAct


private theorem step109wc81s5_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc81s5_contain :
    (o81SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 140) (codeMat 273) orbit13W := by
  change spanCodes [258, 128, 64, 32, 20, 10, 1] ≤ actionW (codeMat 140) (codeMat 273) orbit13W
  apply step109wc81_spanCodes_le_of_gens [258, 128, 64, 32, 20, 10, 1]
    (actionW (codeMat 140) (codeMat 273) orbit13W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 20 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 20 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 20) = codeMat 258 := by
      unfold actionA
      rw [step109wc81s5_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 20 * (codeMat 273 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 2) = codeMat 128 := by
      unfold actionA
      rw [step109wc81s5_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 1) = codeMat 64 := by
      unfold actionA
      rw [step109wc81s5_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 256) = codeMat 32 := by
      unfold actionA
      rw [step109wc81s5_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 256 * (codeMat 273 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 160) = codeMat 20 := by
      unfold actionA
      rw [step109wc81s5_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 160 * (codeMat 273 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 80 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 80 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 80) = codeMat 10 := by
      unfold actionA
      rw [step109wc81s5_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 80 * (codeMat 273 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 140) (codeMat 273) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc81s5_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact

theorem step109wc81s5Dispatch :
    QuotientRankAtLeast (o81SourceU_wc ⟨5, by omega⟩) 12 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 273) orbit13W) 12 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 273) hP hQ orbit13W 12
      orbit13_lb12
  exact quotientRankAtLeast_mono step109wc81s5_contain hAct


private theorem step109wc81s6_QtInv :
    (codeMat 214 : Mat3).transpose⁻¹ = (codeMat 214 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 214 : Mat3).transpose * (codeMat 214 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc81s6_contain :
    (o81SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 116) (codeMat 214) o16W_wc := by
  change spanCodes [256, 130, 66, 34, 20, 10, 1] ≤ actionW (codeMat 116) (codeMat 214) o16W_wc
  apply step109wc81_spanCodes_le_of_gens [256, 130, 66, 34, 20, 10, 1]
    (actionW (codeMat 116) (codeMat 214) o16W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 116) (codeMat 214) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc81s6_QtInv]
      show (codeMat 116 : Mat3).transpose * codeMat 1 * (codeMat 214 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 455 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 455 (by decide)
    have hact : actionA (codeMat 116) (codeMat 214) (codeMat 455) = codeMat 130 := by
      unfold actionA
      rw [step109wc81s6_QtInv]
      show (codeMat 116 : Mat3).transpose * codeMat 455 * (codeMat 214 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 452 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 452 (by decide)
    have hact : actionA (codeMat 116) (codeMat 214) (codeMat 452) = codeMat 66 := by
      unfold actionA
      rw [step109wc81s6_QtInv]
      show (codeMat 116 : Mat3).transpose * codeMat 452 * (codeMat 214 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 457 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 457 (by decide)
    have hact : actionA (codeMat 116) (codeMat 214) (codeMat 457) = codeMat 34 := by
      unfold actionA
      rw [step109wc81s6_QtInv]
      show (codeMat 116 : Mat3).transpose * codeMat 457 * (codeMat 214 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 127 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 127 (by decide)
    have hact : actionA (codeMat 116) (codeMat 214) (codeMat 127) = codeMat 20 := by
      unfold actionA
      rw [step109wc81s6_QtInv]
      show (codeMat 116 : Mat3).transpose * codeMat 127 * (codeMat 214 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 484 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 484 (by decide)
    have hact : actionA (codeMat 116) (codeMat 214) (codeMat 484) = codeMat 10 := by
      unfold actionA
      rw [step109wc81s6_QtInv]
      show (codeMat 116 : Mat3).transpose * codeMat 484 * (codeMat 214 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ o16W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 148, 80, 32, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 116) (codeMat 214) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc81s6_QtInv]
      show (codeMat 116 : Mat3).transpose * codeMat 256 * (codeMat 214 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc81_codeMat_mem_actionW_of_witness hw hact

theorem step109wc81s6Dispatch :
    QuotientRankAtLeast (o81SourceU_wc ⟨6, by omega⟩) 12 := by
  have hP : Invertible (codeMat 116 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 214 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 116) (codeMat 214) o16W_wc) 12 :=
    @quotientRankAtLeast_action (codeMat 116) (codeMat 214) hP hQ o16W_wc 12
      step109_orbit16_lb12_wc
  exact quotientRankAtLeast_mono step109wc81s6_contain hAct

theorem step109wc81_all_dispatch (i : Fin 7) :
    QuotientRankAtLeast (o81SourceU_wc i) (o81SourceLb_wc i) := by
  fin_cases i
  · exact step109wc81s0Dispatch
  · exact step109wc81s1Dispatch
  · exact step109wc81s2Dispatch
  · exact step109wc81s3Dispatch
  · exact step109wc81s4Dispatch
  · exact step109wc81s5Dispatch
  · exact step109wc81s6Dispatch

theorem step109_orbit81_lb15_wc : QuotientRankAtLeast o81W_wc 15 :=
  o81Lb15_wc step109wc81_all_dispatch

end QiushiMatmul
