import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit75Consumer
import QiushiStep81Qdim2Generated
import QiushiOrbit13FP

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc75_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc75_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc75s0_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = (codeMat 267 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * (codeMat 267 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc75s0_contain :
    (o75SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 87) (codeMat 282) step81o17s4Wspan := by
  change spanCodes [262, 128, 68, 32, 20, 10, 1] ≤ actionW (codeMat 87) (codeMat 282) step81o17s4Wspan
  apply step109wc75_spanCodes_le_of_gens [262, 128, 68, 32, 20, 10, 1]
    (actionW (codeMat 87) (codeMat 282) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 228 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 228 (by decide)
    have hact : actionA (codeMat 87) (codeMat 282) (codeMat 228) = codeMat 262 := by
      unfold actionA
      rw [step109wc75s0_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 228 * (codeMat 267 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 219 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 219 (by decide)
    have hact : actionA (codeMat 87) (codeMat 282) (codeMat 219) = codeMat 128 := by
      unfold actionA
      rw [step109wc75s0_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 219 * (codeMat 267 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 402 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 402 (by decide)
    have hact : actionA (codeMat 87) (codeMat 282) (codeMat 402) = codeMat 68 := by
      unfold actionA
      rw [step109wc75s0_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 402 * (codeMat 267 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 87) (codeMat 282) (codeMat 32) = codeMat 32 := by
      unfold actionA
      rw [step109wc75s0_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 32 * (codeMat 267 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 280 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 280 (by decide)
    have hact : actionA (codeMat 87) (codeMat 282) (codeMat 280) = codeMat 20 := by
      unfold actionA
      rw [step109wc75s0_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 280 * (codeMat 267 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 208 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 208 (by decide)
    have hact : actionA (codeMat 87) (codeMat 282) (codeMat 208) = codeMat 10 := by
      unfold actionA
      rw [step109wc75s0_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 208 * (codeMat 267 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 87) (codeMat 282) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc75s0_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 128 * (codeMat 267 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact

theorem step109wc75s0Dispatch :
    QuotientRankAtLeast (o75SourceU_wc ⟨0, by omega⟩) 14 := by
  have hP : Invertible (codeMat 87 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 87) (codeMat 282) step81o17s4Wspan) 14 :=
    @quotientRankAtLeast_action (codeMat 87) (codeMat 282) hP hQ step81o17s4Wspan 14
      step81o17s4Span_lb
  exact quotientRankAtLeast_mono step109wc75s0_contain hAct


private theorem step109wc75s1_QtInv :
    (codeMat 314 : Mat3).transpose⁻¹ = (codeMat 271 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 314 : Mat3).transpose * (codeMat 271 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc75s1_contain :
    (o75SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 86) (codeMat 314) step81o17s4Wspan := by
  change spanCodes [262, 130, 68, 34, 20, 10, 1] ≤ actionW (codeMat 86) (codeMat 314) step81o17s4Wspan
  apply step109wc75_spanCodes_le_of_gens [262, 130, 68, 34, 20, 10, 1]
    (actionW (codeMat 86) (codeMat 314) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 374 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 374 (by decide)
    have hact : actionA (codeMat 86) (codeMat 314) (codeMat 374) = codeMat 262 := by
      unfold actionA
      rw [step109wc75s1_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 374 * (codeMat 271 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 219 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 219 (by decide)
    have hact : actionA (codeMat 86) (codeMat 314) (codeMat 219) = codeMat 130 := by
      unfold actionA
      rw [step109wc75s1_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 219 * (codeMat 271 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 402 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 402 (by decide)
    have hact : actionA (codeMat 86) (codeMat 314) (codeMat 402) = codeMat 68 := by
      unfold actionA
      rw [step109wc75s1_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 402 * (codeMat 271 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 240 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 240 (by decide)
    have hact : actionA (codeMat 86) (codeMat 314) (codeMat 240) = codeMat 34 := by
      unfold actionA
      rw [step109wc75s1_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 240 * (codeMat 271 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 408 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 408 (by decide)
    have hact : actionA (codeMat 86) (codeMat 314) (codeMat 408) = codeMat 20 := by
      unfold actionA
      rw [step109wc75s1_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 408 * (codeMat 271 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 208 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 208 (by decide)
    have hact : actionA (codeMat 86) (codeMat 314) (codeMat 208) = codeMat 10 := by
      unfold actionA
      rw [step109wc75s1_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 208 * (codeMat 271 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 86) (codeMat 314) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc75s1_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 128 * (codeMat 271 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact

theorem step109wc75s1Dispatch :
    QuotientRankAtLeast (o75SourceU_wc ⟨1, by omega⟩) 14 := by
  have hP : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 314 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 86) (codeMat 314) step81o17s4Wspan) 14 :=
    @quotientRankAtLeast_action (codeMat 86) (codeMat 314) hP hQ step81o17s4Wspan 14
      step81o17s4Span_lb
  exact quotientRankAtLeast_mono step109wc75s1_contain hAct


private theorem step109wc75s2_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc75s2_contain :
    (o75SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 94) (codeMat 266) step81o17s4Wspan := by
  change spanCodes [262, 132, 68, 36, 20, 10, 1] ≤ actionW (codeMat 94) (codeMat 266) step81o17s4Wspan
  apply step109wc75_spanCodes_le_of_gens [262, 132, 68, 36, 20, 10, 1]
    (actionW (codeMat 94) (codeMat 266) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 100 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 100 (by decide)
    have hact : actionA (codeMat 94) (codeMat 266) (codeMat 100) = codeMat 262 := by
      unfold actionA
      rw [step109wc75s2_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 100 * (codeMat 266 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 329 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 329 (by decide)
    have hact : actionA (codeMat 94) (codeMat 266) (codeMat 329) = codeMat 132 := by
      unfold actionA
      rw [step109wc75s2_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 329 * (codeMat 266 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 402 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 402 (by decide)
    have hact : actionA (codeMat 94) (codeMat 266) (codeMat 402) = codeMat 68 := by
      unfold actionA
      rw [step109wc75s2_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 402 * (codeMat 266 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 94) (codeMat 266) (codeMat 32) = codeMat 36 := by
      unfold actionA
      rw [step109wc75s2_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 32 * (codeMat 266 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 328 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 328 (by decide)
    have hact : actionA (codeMat 94) (codeMat 266) (codeMat 328) = codeMat 20 := by
      unfold actionA
      rw [step109wc75s2_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 328 * (codeMat 266 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 208 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 208 (by decide)
    have hact : actionA (codeMat 94) (codeMat 266) (codeMat 208) = codeMat 10 := by
      unfold actionA
      rw [step109wc75s2_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 208 * (codeMat 266 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 94) (codeMat 266) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc75s2_QtInv]
      show (codeMat 94 : Mat3).transpose * codeMat 128 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact

theorem step109wc75s2Dispatch :
    QuotientRankAtLeast (o75SourceU_wc ⟨2, by omega⟩) 14 := by
  have hP : Invertible (codeMat 94 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 94) (codeMat 266) step81o17s4Wspan) 14 :=
    @quotientRankAtLeast_action (codeMat 94) (codeMat 266) hP hQ step81o17s4Wspan 14
      step81o17s4Span_lb
  exact quotientRankAtLeast_mono step109wc75s2_contain hAct


private theorem step109wc75s3_QtInv :
    (codeMat 298 : Mat3).transpose⁻¹ = (codeMat 270 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 298 : Mat3).transpose * (codeMat 270 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc75s3_contain :
    (o75SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 95) (codeMat 298) step81o17s4Wspan := by
  change spanCodes [262, 134, 68, 38, 20, 10, 1] ≤ actionW (codeMat 95) (codeMat 298) step81o17s4Wspan
  apply step109wc75_spanCodes_le_of_gens [262, 134, 68, 38, 20, 10, 1]
    (actionW (codeMat 95) (codeMat 298) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 502 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 502 (by decide)
    have hact : actionA (codeMat 95) (codeMat 298) (codeMat 502) = codeMat 262 := by
      unfold actionA
      rw [step109wc75s3_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 502 * (codeMat 270 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 457 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 457 (by decide)
    have hact : actionA (codeMat 95) (codeMat 298) (codeMat 457) = codeMat 134 := by
      unfold actionA
      rw [step109wc75s3_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 457 * (codeMat 270 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 402 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 402 (by decide)
    have hact : actionA (codeMat 95) (codeMat 298) (codeMat 402) = codeMat 68 := by
      unfold actionA
      rw [step109wc75s3_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 402 * (codeMat 270 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 112 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 112 (by decide)
    have hact : actionA (codeMat 95) (codeMat 298) (codeMat 112) = codeMat 38 := by
      unfold actionA
      rw [step109wc75s3_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 112 * (codeMat 270 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 456 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 456 (by decide)
    have hact : actionA (codeMat 95) (codeMat 298) (codeMat 456) = codeMat 20 := by
      unfold actionA
      rw [step109wc75s3_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 456 * (codeMat 270 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 208 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 208 (by decide)
    have hact : actionA (codeMat 95) (codeMat 298) (codeMat 208) = codeMat 10 := by
      unfold actionA
      rw [step109wc75s3_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 208 * (codeMat 270 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 128 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 95) (codeMat 298) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc75s3_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 128 * (codeMat 270 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact

theorem step109wc75s3Dispatch :
    QuotientRankAtLeast (o75SourceU_wc ⟨3, by omega⟩) 14 := by
  have hP : Invertible (codeMat 95 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 298 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 95) (codeMat 298) step81o17s4Wspan) 14 :=
    @quotientRankAtLeast_action (codeMat 95) (codeMat 298) hP hQ step81o17s4Wspan 14
      step81o17s4Span_lb
  exact quotientRankAtLeast_mono step109wc75s3_contain hAct


private theorem step109wc75s4_QtInv :
    (codeMat 277 : Mat3).transpose⁻¹ = (codeMat 277 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 277 : Mat3).transpose * (codeMat 277 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc75s4_contain :
    (o75SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 273) (codeMat 277) orbit13W := by
  change spanCodes [260, 160, 68, 20, 8, 2, 1] ≤ actionW (codeMat 273) (codeMat 277) orbit13W
  apply step109wc75_spanCodes_le_of_gens [260, 160, 68, 20, 8, 2, 1]
    (actionW (codeMat 273) (codeMat 277) orbit13W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 325 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 325 (by decide)
    have hact : actionA (codeMat 273) (codeMat 277) (codeMat 325) = codeMat 260 := by
      unfold actionA
      rw [step109wc75s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 325 * (codeMat 277 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 168 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 168 (by decide)
    have hact : actionA (codeMat 273) (codeMat 277) (codeMat 168) = codeMat 160 := by
      unfold actionA
      rw [step109wc75s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 168 * (codeMat 277 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 69 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 69 (by decide)
    have hact : actionA (codeMat 273) (codeMat 277) (codeMat 69) = codeMat 68 := by
      unfold actionA
      rw [step109wc75s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 69 * (codeMat 277 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 21 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 21 (by decide)
    have hact : actionA (codeMat 273) (codeMat 277) (codeMat 21) = codeMat 20 := by
      unfold actionA
      rw [step109wc75s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 21 * (codeMat 277 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 277) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc75s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 277 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 277) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc75s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 277 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 277) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc75s4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 277 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact

theorem step109wc75s4Dispatch :
    QuotientRankAtLeast (o75SourceU_wc ⟨4, by omega⟩) 12 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 277 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 277) orbit13W) 12 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 277) hP hQ orbit13W 12
      orbit13_lb12
  exact quotientRankAtLeast_mono step109wc75s4_contain hAct


private theorem step109wc75s5_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc75s5_contain :
    (o75SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 161) (codeMat 161) orbit13W := by
  change spanCodes [258, 160, 64, 16, 10, 4, 1] ≤ actionW (codeMat 161) (codeMat 161) orbit13W
  apply step109wc75_spanCodes_le_of_gens [258, 160, 64, 16, 10, 4, 1]
    (actionW (codeMat 161) (codeMat 161) orbit13W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 20 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 20 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 20) = codeMat 258 := by
      unfold actionA
      rw [step109wc75s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 20 * (codeMat 161 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 160) = codeMat 160 := by
      unfold actionA
      rw [step109wc75s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * (codeMat 161 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 8) = codeMat 64 := by
      unfold actionA
      rw [step109wc75s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 256) = codeMat 16 := by
      unfold actionA
      rw [step109wc75s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 161 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 68 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 68) = codeMat 10 := by
      unfold actionA
      rw [step109wc75s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 68 * (codeMat 161 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 2) = codeMat 4 := by
      unfold actionA
      rw [step109wc75s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc75s5_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact

theorem step109wc75s5Dispatch :
    QuotientRankAtLeast (o75SourceU_wc ⟨5, by omega⟩) 12 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 161) orbit13W) 12 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 161) hP hQ orbit13W 12
      orbit13_lb12
  exact quotientRankAtLeast_mono step109wc75s5_contain hAct


private theorem step109wc75s6_QtInv :
    (codeMat 423 : Mat3).transpose⁻¹ = (codeMat 181 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 423 : Mat3).transpose * (codeMat 181 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc75s6_contain :
    (o75SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 177) (codeMat 423) orbit13W := by
  change spanCodes [256, 160, 66, 18, 10, 6, 1] ≤ actionW (codeMat 177) (codeMat 423) orbit13W
  apply step109wc75_spanCodes_le_of_gens [256, 160, 66, 18, 10, 6, 1]
    (actionW (codeMat 177) (codeMat 423) orbit13W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 504 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 504 (by decide)
    have hact : actionA (codeMat 177) (codeMat 423) (codeMat 504) = codeMat 256 := by
      unfold actionA
      rw [step109wc75s6_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 504 * (codeMat 181 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 168 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 168 (by decide)
    have hact : actionA (codeMat 177) (codeMat 423) (codeMat 168) = codeMat 160 := by
      unfold actionA
      rw [step109wc75s6_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 168 * (codeMat 181 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 77 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 77 (by decide)
    have hact : actionA (codeMat 177) (codeMat 423) (codeMat 77) = codeMat 66 := by
      unfold actionA
      rw [step109wc75s6_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 77 * (codeMat 181 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 325 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 325 (by decide)
    have hact : actionA (codeMat 177) (codeMat 423) (codeMat 325) = codeMat 18 := by
      unfold actionA
      rw [step109wc75s6_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 325 * (codeMat 181 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 69 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 69 (by decide)
    have hact : actionA (codeMat 177) (codeMat 423) (codeMat 69) = codeMat 10 := by
      unfold actionA
      rw [step109wc75s6_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 69 * (codeMat 181 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 177) (codeMat 423) (codeMat 2) = codeMat 6 := by
      unfold actionA
      rw [step109wc75s6_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 2 * (codeMat 181 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ orbit13W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 423) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc75s6_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * (codeMat 181 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc75_codeMat_mem_actionW_of_witness hw hact

theorem step109wc75s6Dispatch :
    QuotientRankAtLeast (o75SourceU_wc ⟨6, by omega⟩) 12 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 423 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 423) orbit13W) 12 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 423) hP hQ orbit13W 12
      orbit13_lb12
  exact quotientRankAtLeast_mono step109wc75s6_contain hAct

theorem step109wc75_all_dispatch (i : Fin 7) :
    QuotientRankAtLeast (o75SourceU_wc i) (o75SourceLb_wc i) := by
  fin_cases i
  · exact step109wc75s0Dispatch
  · exact step109wc75s1Dispatch
  · exact step109wc75s2Dispatch
  · exact step109wc75s3Dispatch
  · exact step109wc75s4Dispatch
  · exact step109wc75s5Dispatch
  · exact step109wc75s6Dispatch

theorem step109_orbit75_lb16_wc : QuotientRankAtLeast o75W_wc 16 :=
  o75Lb16_wc step109wc75_all_dispatch

end QiushiMatmul
